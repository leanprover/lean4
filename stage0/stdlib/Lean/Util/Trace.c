// Lean compiler output
// Module: Lean.Util.Trace
// Imports: public import Lean.Elab.Exception public import Lean.Log
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
lean_object* l_MonadExcept_ofExcept___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_KVMap_instValueNat;
double lean_float_div(double, double);
lean_object* l_IO_monoNanosNow___boxed(lean_object*);
lean_object* l_IO_getNumHeartbeats___boxed(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonadExceptOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
lean_object* l_Lean_MessageData_format___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BaseIO_toIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_instToStringFormat___lam__0(lean_object*);
lean_object* l_IO_println___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqRaw___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_KVMap_instValueString;
lean_object* l_Lean_Option_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_instHashableRaw_hash___boxed(lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonadExceptOf___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonadExceptOf___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedTraceElem_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTraceElem_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceElem_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceElem;
static lean_once_cell_t l_Lean_instInhabitedTraceState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instInhabitedTraceState_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedTraceState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTraceState_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedTraceState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTraceState_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceState_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceState;
static lean_once_cell_t l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_inheritedTraceOptions;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4_value;
static const lean_array_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "inheritedTraceOptions.get"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14_value;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "inheritedTraceOptions"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value),LEAN_SCALAR_PTR_LITERAL(111, 221, 127, 62, 213, 113, 62, 253)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value),LEAN_SCALAR_PTR_LITERAL(249, 53, 178, 254, 160, 90, 192, 243)}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27;
static lean_once_cell_t l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28;
LEAN_EXPORT lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam;
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_printTraces___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringFormat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_printTraces___redArg___closed__0 = (const lean_object*)&l_Lean_printTraces___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_resetTraceState___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_resetTraceState___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_resetTraceState___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_resetTraceState___redArg___lam__0___closed__1;
static lean_once_cell_t l_Lean_resetTraceState___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_resetTraceState___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_resetTraceState___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_resetTraceState___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resetTraceState___redArg___closed__0 = (const lean_object*)&l_Lean_resetTraceState___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resetTraceState(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkTraceOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_checkTraceOption___closed__0 = (const lean_object*)&l_Lean_checkTraceOption___closed__0_value;
static const lean_ctor_object l_Lean_checkTraceOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_checkTraceOption___closed__1 = (const lean_object*)&l_Lean_checkTraceOption___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkTraceOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_is_trace_class_enabled(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___redArg___lam__0___closed__0;
static const lean_string_object l_Lean_addTrace___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_addTrace___redArg___lam__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_addTrace___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__0_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__1_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__7_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__2_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__3_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__4_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__5_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__8_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__6_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "profiler"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "activate nested traces with execution time above `trace.profiler.threshold` and annotate with time"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "threshold"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(184, 9, 42, 114, 12, 38, 11, 42)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 130, .m_capacity = 130, .m_length = 129, .m_data = "threshold in milliseconds (or heartbeats if `trace.profiler.useHeartbeats` is true), traces below threshold will not be activated"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 45, 177, 27, 189, 220, 1, 137)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold;
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "useHeartbeats"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 182, 122, 179, 202, 46, 182, 49)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "if true, measure and report heartbeats instead of seconds"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(89, 248, 181, 172, 128, 194, 123, 56)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_useHeartbeats;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "output"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(19, 45, 221, 139, 23, 193, 130, 68)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "output `trace.profiler` data in Firefox Profiler-compatible format to given file path"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addTrace___redArg___lam__0___closed__1_value),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(58, 195, 204, 148, 25, 40, 60, 227)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_output;
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(19, 45, 221, 139, 23, 193, 130, 68)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(193, 225, 100, 102, 84, 233, 134, 170)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 232, .m_capacity = 232, .m_length = 231, .m_data = "if false, limit text in exported trace nodes to trace class name and `TraceData.tag`, if any\n\nThis is useful when we are interested in the time taken by specific subsystems instead of specific invocations, which is the common case."};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(58, 195, 204, 148, 25, 40, 60, 227)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(228, 86, 200, 244, 100, 192, 149, 216)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_output_pp;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_monoNanosNow___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_getNumHeartbeats___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_trace_profiler_threshold_unitAdjusted___closed__0;
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object*);
static lean_once_cell_t l_Lean_instMonadAlwaysExceptEIO___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instMonadAlwaysExceptEIO___closed__0;
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_bombEmoji___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 2, .m_data = "💥️"};
static const lean_object* l_Lean_bombEmoji___closed__0 = (const lean_object*)&l_Lean_bombEmoji___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_bombEmoji = (const lean_object*)&l_Lean_bombEmoji___closed__0_value;
static const lean_string_object l_Lean_checkEmoji___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 2, .m_data = "✅️"};
static const lean_object* l_Lean_checkEmoji___closed__0 = (const lean_object*)&l_Lean_checkEmoji___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_checkEmoji = (const lean_object*)&l_Lean_checkEmoji___closed__0_value;
static const lean_string_object l_Lean_crossEmoji___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 2, .m_data = "❌️"};
static const lean_object* l_Lean_crossEmoji___closed__0 = (const lean_object*)&l_Lean_crossEmoji___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_crossEmoji = (const lean_object*)&l_Lean_crossEmoji___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResultBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResultBool___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResultBool___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResultOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultOption___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResultOption___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResultOption___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResult___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResult___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResult___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, double, double, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object**);
static const lean_closure_object l_Lean_withTraceNode_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withTraceNode_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_withTraceNode_x27___redArg___closed__0 = (const lean_object*)&l_Lean_withTraceNode_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerTraceClass___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_registerTraceClass___auto__1___closed__0 = (const lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value;
static const lean_string_object l_Lean_registerTraceClass___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_registerTraceClass___auto__1___closed__1 = (const lean_object*)&l_Lean_registerTraceClass___auto__1___closed__1_value;
static const lean_ctor_object l_Lean_registerTraceClass___auto__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_registerTraceClass___auto__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__2_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_registerTraceClass___auto__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__2_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_registerTraceClass___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__2_value_aux_2),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_registerTraceClass___auto__1___closed__2 = (const lean_object*)&l_Lean_registerTraceClass___auto__1___closed__2_value;
static const lean_string_object l_Lean_registerTraceClass___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_registerTraceClass___auto__1___closed__3 = (const lean_object*)&l_Lean_registerTraceClass___auto__1___closed__3_value;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__4;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__5;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__6;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__7;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__8;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__9;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__10;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__11;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__12;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__13;
static lean_once_cell_t l_Lean_registerTraceClass___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTraceClass___auto__1___closed__14;
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___auto__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_registerTraceClass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_registerTraceClass___closed__0 = (const lean_object*)&l_Lean_registerTraceClass___closed__0_value;
static const lean_string_object l_Lean_registerTraceClass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "enable/disable tracing for the given module and submodules"};
static const lean_object* l_Lean_registerTraceClass___closed__1 = (const lean_object*)&l_Lean_registerTraceClass___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "liftMethod"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.isTracingEnabledFor"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "isTracingEnabledFor"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.addTrace"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "addTrace"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cls"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value),LEAN_SCALAR_PTR_LITERAL(28, 113, 141, 155, 240, 79, 69, 244)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MessageData"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value),LEAN_SCALAR_PTR_LITERAL(117, 193, 162, 252, 67, 31, 191, 159)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doElemTrace[_]__"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__0 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value_aux_0),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 144, 171, 160, 60, 151, 54, 39)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__1 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__2 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__3 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "trace["};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__4 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__4_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__5 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__6 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__7 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__7_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__8 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__5_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__8_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__9 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__10 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__10_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__11 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__9_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__11_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__12 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__13 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__13_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__14 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__15 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__15_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__16 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value;
static const lean_string_object l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__17 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__17_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__18 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__19 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__16_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__20 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__14_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__20_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__19_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__21 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__3_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__12_value),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__21_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__22 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value;
static const lean_ctor_object l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__22_value)}};
static const lean_object* l_Lean_doElemTrace_x5b___x5d_____00__closed__23 = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value;
LEAN_EXPORT const lean_object* l_Lean_doElemTrace_x5b___x5d____ = (const lean_object*)&l_Lean_doElemTrace_x5b___x5d_____00__closed__23_value;
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__0;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__1;
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHashableRaw_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__2 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value;
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___lam__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableProd___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value),((lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__11___closed__2_value)} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__3 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__11___closed__3_value;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__4;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__5;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_addTraceAsMessages___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___closed__0 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___closed__0_value;
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_addTraceAsMessages___redArg___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___closed__1 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 215, 222, 176, 152, 52, 0, 225)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 20, 155, 62, 160, 30, 19, 156)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Trace"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__6_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 45, 197, 3, 218, 39, 236, 122)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__8_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(212, 132, 182, 134, 118, 170, 212, 125)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__9_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 109, 156, 246, 253, 156, 207, 235)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__10_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__11_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(252, 109, 61, 254, 212, 130, 102, 57)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__12_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__13_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 63, 132, 83, 234, 34, 87, 212)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__14_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(96, 141, 129, 211, 167, 99, 91, 102)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__15_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__5_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 185, 91, 65, 254, 191, 29, 193)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__16_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__7_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 72, 204, 88, 19, 210, 210, 71)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_instInhabitedTraceElem_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = l_Lean_instInhabitedMessageData_default;
v___x_2_ = lean_box(0);
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceElem_default(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&l_Lean_instInhabitedTraceElem_default___closed__0, &l_Lean_instInhabitedTraceElem_default___closed__0_once, _init_l_Lean_instInhabitedTraceElem_default___closed__0);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceElem(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Lean_instInhabitedTraceElem_default;
return v___x_5_;
}
}
static uint64_t _init_l_Lean_instInhabitedTraceState_default___closed__0(void){
_start:
{
lean_object* v___x_6_; uint64_t v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_uint64_of_nat(v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState_default___closed__1(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_8_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState_default___closed__2(void){
_start:
{
lean_object* v___x_9_; uint64_t v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__1, &l_Lean_instInhabitedTraceState_default___closed__1_once, _init_l_Lean_instInhabitedTraceState_default___closed__1);
v___x_10_ = lean_uint64_once(&l_Lean_instInhabitedTraceState_default___closed__0, &l_Lean_instInhabitedTraceState_default___closed__0_once, _init_l_Lean_instInhabitedTraceState_default___closed__0);
v___x_11_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_11_, 0, v___x_9_);
lean_ctor_set_uint64(v___x_11_, sizeof(void*)*1, v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState_default(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__2, &l_Lean_instInhabitedTraceState_default___closed__2_once, _init_l_Lean_instInhabitedTraceState_default___closed__2);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_instInhabitedTraceState_default;
return v___x_13_;
}
}
static lean_object* _init_l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_box(0);
v___x_15_ = lean_unsigned_to_nat(16u);
v___x_16_ = lean_mk_array(v___x_15_, v___x_14_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_obj_once(&l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_, &l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_obj_once(&l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_, &l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
v___x_22_ = lean_st_mk_ref(v___x_21_);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2____boxed(lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
return v_res_25_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10));
v___x_53_ = l_Lean_mkAtom(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12);
v___x_55_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_56_ = lean_array_push(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14));
v___x_59_ = lean_string_utf8_byte_size(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15);
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14));
v___x_63_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
lean_ctor_set(v___x_63_, 2, v___x_60_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_69_ = lean_box(0);
v___x_70_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19));
v___x_71_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16);
v___x_72_ = lean_box(2);
v___x_73_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
lean_ctor_set(v___x_73_, 3, v___x_69_);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20);
v___x_75_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_76_ = lean_array_push(v___x_75_, v___x_74_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21);
v___x_78_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_79_ = lean_box(2);
v___x_80_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
lean_ctor_set(v___x_80_, 2, v___x_77_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22);
v___x_82_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_83_ = lean_array_push(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_84_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23);
v___x_85_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_86_ = lean_box(2);
v___x_87_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
lean_ctor_set(v___x_87_, 2, v___x_84_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24);
v___x_89_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_90_ = lean_array_push(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25);
v___x_92_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_93_ = lean_box(2);
v___x_94_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
lean_ctor_set(v___x_94_, 2, v___x_91_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26);
v___x_96_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_97_ = lean_array_push(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27);
v___x_99_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_100_ = lean_box(2);
v___x_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_98_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg___lam__0(lean_object* v_modifyTraceState_103_, lean_object* v_inst_104_, lean_object* v_f_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_apply_1(v_modifyTraceState_103_, v_f_105_);
v___x_107_ = lean_apply_2(v_inst_104_, lean_box(0), v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object* v_inst_108_, lean_object* v_inst_109_){
_start:
{
lean_object* v_modifyTraceState_110_; lean_object* v_getTraceState_111_; lean_object* v_getInheritedTraceOptions_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_122_; 
v_modifyTraceState_110_ = lean_ctor_get(v_inst_109_, 0);
v_getTraceState_111_ = lean_ctor_get(v_inst_109_, 1);
v_getInheritedTraceOptions_112_ = lean_ctor_get(v_inst_109_, 2);
v_isSharedCheck_122_ = !lean_is_exclusive(v_inst_109_);
if (v_isSharedCheck_122_ == 0)
{
v___x_114_ = v_inst_109_;
v_isShared_115_ = v_isSharedCheck_122_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_getInheritedTraceOptions_112_);
lean_inc(v_getTraceState_111_);
lean_inc(v_modifyTraceState_110_);
lean_dec(v_inst_109_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_122_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___f_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
lean_inc_n(v_inst_108_, 2);
v___f_116_ = lean_alloc_closure((void*)(l_Lean_instMonadTraceOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_116_, 0, v_modifyTraceState_110_);
lean_closure_set(v___f_116_, 1, v_inst_108_);
v___x_117_ = lean_apply_2(v_inst_108_, lean_box(0), v_getTraceState_111_);
v___x_118_ = lean_apply_2(v_inst_108_, lean_box(0), v_getInheritedTraceOptions_112_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 2, v___x_118_);
lean_ctor_set(v___x_114_, 1, v___x_117_);
lean_ctor_set(v___x_114_, 0, v___f_116_);
v___x_120_ = v___x_114_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___f_116_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift(lean_object* v_m_123_, lean_object* v_n_124_, lean_object* v_inst_125_, lean_object* v_inst_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_instMonadTraceOfMonadLift___redArg(v_inst_125_, v_inst_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__0(lean_object* v_toPure_128_, lean_object* v_____s_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_box(0);
v___x_131_ = lean_apply_2(v_toPure_128_, lean_box(0), v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__1(lean_object* v___x_132_, lean_object* v_toPure_133_, lean_object* v_r_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_132_);
v___x_136_ = lean_apply_2(v_toPure_133_, lean_box(0), v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__2(lean_object* v___f_137_, lean_object* v_inst_138_, lean_object* v_toBind_139_, lean_object* v___f_140_, lean_object* v_____do__lift_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_alloc_closure((void*)(l_IO_println___boxed), 4, 3);
lean_closure_set(v___x_142_, 0, lean_box(0));
lean_closure_set(v___x_142_, 1, v___f_137_);
lean_closure_set(v___x_142_, 2, v_____do__lift_141_);
v___x_143_ = lean_apply_2(v_inst_138_, lean_box(0), v___x_142_);
v___x_144_ = lean_apply_4(v_toBind_139_, lean_box(0), lean_box(0), v___x_143_, v___f_140_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__3(lean_object* v_inst_145_, lean_object* v_toBind_146_, lean_object* v___f_147_, lean_object* v_x_148_, lean_object* v_____s_149_){
_start:
{
lean_object* v_msg_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_msg_150_ = lean_ctor_get(v_x_148_, 1);
lean_inc_ref(v_msg_150_);
lean_dec_ref(v_x_148_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_alloc_closure((void*)(l_Lean_MessageData_format___boxed), 3, 2);
lean_closure_set(v___x_152_, 0, v_msg_150_);
lean_closure_set(v___x_152_, 1, v___x_151_);
v___x_153_ = lean_alloc_closure((void*)(l_BaseIO_toIO___boxed), 3, 2);
lean_closure_set(v___x_153_, 0, lean_box(0));
lean_closure_set(v___x_153_, 1, v___x_152_);
v___x_154_ = lean_apply_2(v_inst_145_, lean_box(0), v___x_153_);
v___x_155_ = lean_apply_4(v_toBind_146_, lean_box(0), lean_box(0), v___x_154_, v___f_147_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4(lean_object* v_toPure_156_, lean_object* v___f_157_, lean_object* v_inst_158_, lean_object* v_toBind_159_, lean_object* v_inst_160_, lean_object* v___f_161_, lean_object* v_____do__lift_162_){
_start:
{
lean_object* v_traces_163_; lean_object* v___x_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_traces_163_ = lean_ctor_get(v_____do__lift_162_, 0);
lean_inc_ref(v_traces_163_);
lean_dec_ref(v_____do__lift_162_);
v___x_164_ = lean_box(0);
v___f_165_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_165_, 0, v___x_164_);
lean_closure_set(v___f_165_, 1, v_toPure_156_);
lean_inc_n(v_toBind_159_, 2);
lean_inc(v_inst_158_);
v___f_166_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_166_, 0, v___f_157_);
lean_closure_set(v___f_166_, 1, v_inst_158_);
lean_closure_set(v___f_166_, 2, v_toBind_159_);
lean_closure_set(v___f_166_, 3, v___f_165_);
v___f_167_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__3), 5, 3);
lean_closure_set(v___f_167_, 0, v_inst_158_);
lean_closure_set(v___f_167_, 1, v_toBind_159_);
lean_closure_set(v___f_167_, 2, v___f_166_);
v___x_168_ = l_Lean_PersistentArray_forIn___redArg(v_inst_160_, v_traces_163_, v___x_164_, v___f_167_);
v___x_169_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_168_, v___f_161_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_){
_start:
{
lean_object* v_toApplicative_174_; lean_object* v_toBind_175_; lean_object* v_getTraceState_176_; lean_object* v_toPure_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___f_180_; lean_object* v___x_181_; 
v_toApplicative_174_ = lean_ctor_get(v_inst_171_, 0);
v_toBind_175_ = lean_ctor_get(v_inst_171_, 1);
lean_inc_n(v_toBind_175_, 2);
v_getTraceState_176_ = lean_ctor_get(v_inst_172_, 1);
lean_inc(v_getTraceState_176_);
lean_dec_ref(v_inst_172_);
v_toPure_177_ = lean_ctor_get(v_toApplicative_174_, 1);
lean_inc_n(v_toPure_177_, 2);
v___f_178_ = ((lean_object*)(l_Lean_printTraces___redArg___closed__0));
v___f_179_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_179_, 0, v_toPure_177_);
v___f_180_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__4), 7, 6);
lean_closure_set(v___f_180_, 0, v_toPure_177_);
lean_closure_set(v___f_180_, 1, v___f_178_);
lean_closure_set(v___f_180_, 2, v_inst_173_);
lean_closure_set(v___f_180_, 3, v_toBind_175_);
lean_closure_set(v___f_180_, 4, v_inst_171_);
lean_closure_set(v___f_180_, 5, v___f_179_);
v___x_181_ = lean_apply_4(v_toBind_175_, lean_box(0), lean_box(0), v_getTraceState_176_, v___f_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces(lean_object* v_m_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_inst_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_printTraces___redArg(v_inst_183_, v_inst_184_, v_inst_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_resetTraceState___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_unsigned_to_nat(32u);
v___x_188_ = lean_mk_empty_array_with_capacity(v___x_187_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_resetTraceState___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_190_ = ((size_t)5ULL);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_unsigned_to_nat(32u);
v___x_193_ = lean_mk_empty_array_with_capacity(v___x_192_);
v___x_194_ = lean_obj_once(&l_Lean_resetTraceState___redArg___lam__0___closed__0, &l_Lean_resetTraceState___redArg___lam__0___closed__0_once, _init_l_Lean_resetTraceState___redArg___lam__0___closed__0);
v___x_195_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 2, v___x_191_);
lean_ctor_set(v___x_195_, 3, v___x_191_);
lean_ctor_set_usize(v___x_195_, 4, v___x_190_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_resetTraceState___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_196_; uint64_t v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_obj_once(&l_Lean_resetTraceState___redArg___lam__0___closed__1, &l_Lean_resetTraceState___redArg___lam__0___closed__1_once, _init_l_Lean_resetTraceState___redArg___lam__0___closed__1);
v___x_197_ = 0ULL;
v___x_198_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set_uint64(v___x_198_, sizeof(void*)*1, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0(lean_object* v_x_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lean_resetTraceState___redArg___lam__0___closed__2, &l_Lean_resetTraceState___redArg___lam__0___closed__2_once, _init_l_Lean_resetTraceState___redArg___lam__0___closed__2);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0___boxed(lean_object* v_x_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_resetTraceState___redArg___lam__0(v_x_201_);
lean_dec_ref(v_x_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg(lean_object* v_inst_204_){
_start:
{
lean_object* v_modifyTraceState_205_; lean_object* v___f_206_; lean_object* v___x_207_; 
v_modifyTraceState_205_ = lean_ctor_get(v_inst_204_, 0);
lean_inc(v_modifyTraceState_205_);
lean_dec_ref(v_inst_204_);
v___f_206_ = ((lean_object*)(l_Lean_resetTraceState___redArg___closed__0));
v___x_207_ = lean_apply_1(v_modifyTraceState_205_, v___f_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState(lean_object* v_m_208_, lean_object* v_inst_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_resetTraceState___redArg(v_inst_209_);
return v___x_210_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(lean_object* v_a_211_, lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
uint8_t v___x_213_; 
v___x_213_ = 0;
return v___x_213_;
}
else
{
lean_object* v_key_214_; lean_object* v_tail_215_; uint8_t v___x_216_; 
v_key_214_ = lean_ctor_get(v_x_212_, 0);
v_tail_215_ = lean_ctor_get(v_x_212_, 2);
v___x_216_ = lean_name_eq(v_key_214_, v_a_211_);
if (v___x_216_ == 0)
{
v_x_212_ = v_tail_215_;
goto _start;
}
else
{
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_218_, lean_object* v_x_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_218_, v_x_219_);
lean_dec(v_x_219_);
lean_dec(v_a_218_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_222_; uint64_t v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(1723u);
v___x_223_ = lean_uint64_of_nat(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(lean_object* v_m_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_buckets_226_; lean_object* v___x_227_; uint64_t v___y_229_; 
v_buckets_226_ = lean_ctor_get(v_m_224_, 1);
v___x_227_ = lean_array_get_size(v_buckets_226_);
if (lean_obj_tag(v_a_225_) == 0)
{
uint64_t v___x_243_; 
v___x_243_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_229_ = v___x_243_;
goto v___jp_228_;
}
else
{
uint64_t v_hash_244_; 
v_hash_244_ = lean_ctor_get_uint64(v_a_225_, sizeof(void*)*2);
v___y_229_ = v_hash_244_;
goto v___jp_228_;
}
v___jp_228_:
{
uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v_fold_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_230_ = 32ULL;
v___x_231_ = lean_uint64_shift_right(v___y_229_, v___x_230_);
v_fold_232_ = lean_uint64_xor(v___y_229_, v___x_231_);
v___x_233_ = 16ULL;
v___x_234_ = lean_uint64_shift_right(v_fold_232_, v___x_233_);
v___x_235_ = lean_uint64_xor(v_fold_232_, v___x_234_);
v___x_236_ = lean_uint64_to_usize(v___x_235_);
v___x_237_ = lean_usize_of_nat(v___x_227_);
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_sub(v___x_237_, v___x_238_);
v___x_240_ = lean_usize_land(v___x_236_, v___x_239_);
v___x_241_ = lean_array_uget_borrowed(v_buckets_226_, v___x_240_);
v___x_242_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_225_, v___x_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___boxed(lean_object* v_m_245_, lean_object* v_a_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_m_245_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object* v_inherited_249_, lean_object* v_opts_250_, lean_object* v_opt_251_){
_start:
{
lean_object* v_map_257_; lean_object* v___x_258_; 
v_map_257_ = lean_ctor_get(v_opts_250_, 0);
v___x_258_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_257_, v_opt_251_);
if (lean_obj_tag(v___x_258_) == 0)
{
goto v___jp_252_;
}
else
{
lean_object* v_val_259_; 
v_val_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_val_259_);
lean_dec_ref(v___x_258_);
if (lean_obj_tag(v_val_259_) == 1)
{
uint8_t v_v_260_; 
v_v_260_ = lean_ctor_get_uint8(v_val_259_, 0);
lean_dec_ref(v_val_259_);
return v_v_260_;
}
else
{
lean_dec(v_val_259_);
goto v___jp_252_;
}
}
v___jp_252_:
{
if (lean_obj_tag(v_opt_251_) == 1)
{
lean_object* v_pre_253_; uint8_t v___x_254_; 
v_pre_253_ = lean_ctor_get(v_opt_251_, 0);
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_inherited_249_, v_opt_251_);
if (v___x_254_ == 0)
{
return v___x_254_;
}
else
{
v_opt_251_ = v_pre_253_;
goto _start;
}
}
else
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go___boxed(lean_object* v_inherited_261_, lean_object* v_opts_262_, lean_object* v_opt_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_261_, v_opts_262_, v_opt_263_);
lean_dec(v_opt_263_);
lean_dec_ref(v_opts_262_);
lean_dec_ref(v_inherited_261_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(lean_object* v_00_u03b2_266_, lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_267_, v_a_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(lean_object* v_00_u03b2_270_, lean_object* v_m_271_, lean_object* v_a_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(v_00_u03b2_270_, v_m_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_m_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(lean_object* v_00_u03b2_275_, lean_object* v_a_276_, lean_object* v_x_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_276_, v_x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_279_, lean_object* v_a_280_, lean_object* v_x_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(v_00_u03b2_279_, v_a_280_, v_x_281_);
lean_dec(v_x_281_);
lean_dec(v_a_280_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT uint8_t l_Lean_checkTraceOption(lean_object* v_inherited_287_, lean_object* v_opts_288_, lean_object* v_cls_289_){
_start:
{
uint8_t v_hasTrace_290_; 
v_hasTrace_290_ = lean_ctor_get_uint8(v_opts_288_, sizeof(void*)*1);
if (v_hasTrace_290_ == 0)
{
lean_dec(v_cls_289_);
return v_hasTrace_290_;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_291_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_292_ = l_Lean_Name_append(v___x_291_, v_cls_289_);
v___x_293_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_287_, v_opts_288_, v___x_292_);
lean_dec(v___x_292_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkTraceOption___boxed(lean_object* v_inherited_294_, lean_object* v_opts_295_, lean_object* v_cls_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Lean_checkTraceOption(v_inherited_294_, v_opts_295_, v_cls_296_);
lean_dec_ref(v_opts_295_);
lean_dec_ref(v_inherited_294_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0(lean_object* v_toPure_299_, lean_object* v_cls_300_, lean_object* v_____do__lift_301_, lean_object* v_____do__lift_302_){
_start:
{
uint8_t v_hasTrace_303_; 
v_hasTrace_303_ = lean_ctor_get_uint8(v_____do__lift_302_, sizeof(void*)*1);
if (v_hasTrace_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v_cls_300_);
v___x_304_ = lean_box(v_hasTrace_303_);
v___x_305_ = lean_apply_2(v_toPure_299_, lean_box(0), v___x_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_306_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_307_ = l_Lean_Name_append(v___x_306_, v_cls_300_);
v___x_308_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_301_, v_____do__lift_302_, v___x_307_);
lean_dec(v___x_307_);
v___x_309_ = lean_box(v___x_308_);
v___x_310_ = lean_apply_2(v_toPure_299_, lean_box(0), v___x_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0___boxed(lean_object* v_toPure_311_, lean_object* v_cls_312_, lean_object* v_____do__lift_313_, lean_object* v_____do__lift_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_isTracingEnabledFor___redArg___lam__0(v_toPure_311_, v_cls_312_, v_____do__lift_313_, v_____do__lift_314_);
lean_dec_ref(v_____do__lift_314_);
lean_dec_ref(v_____do__lift_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__1(lean_object* v_toPure_316_, lean_object* v_cls_317_, lean_object* v_toBind_318_, lean_object* v_inst_319_, lean_object* v_____do__lift_320_){
_start:
{
lean_object* v___f_321_; lean_object* v___x_322_; 
v___f_321_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_321_, 0, v_toPure_316_);
lean_closure_set(v___f_321_, 1, v_cls_317_);
lean_closure_set(v___f_321_, 2, v_____do__lift_320_);
v___x_322_ = lean_apply_4(v_toBind_318_, lean_box(0), lean_box(0), v_inst_319_, v___f_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_cls_326_){
_start:
{
lean_object* v_toApplicative_327_; lean_object* v_toBind_328_; lean_object* v_getInheritedTraceOptions_329_; lean_object* v_toPure_330_; lean_object* v___f_331_; lean_object* v___x_332_; 
v_toApplicative_327_ = lean_ctor_get(v_inst_323_, 0);
lean_inc_ref(v_toApplicative_327_);
v_toBind_328_ = lean_ctor_get(v_inst_323_, 1);
lean_inc_n(v_toBind_328_, 2);
lean_dec_ref(v_inst_323_);
v_getInheritedTraceOptions_329_ = lean_ctor_get(v_inst_324_, 2);
lean_inc(v_getInheritedTraceOptions_329_);
lean_dec_ref(v_inst_324_);
v_toPure_330_ = lean_ctor_get(v_toApplicative_327_, 1);
lean_inc(v_toPure_330_);
lean_dec_ref(v_toApplicative_327_);
v___f_331_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_331_, 0, v_toPure_330_);
lean_closure_set(v___f_331_, 1, v_cls_326_);
lean_closure_set(v___f_331_, 2, v_toBind_328_);
lean_closure_set(v___f_331_, 3, v_inst_325_);
v___x_332_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_329_, v___f_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor(lean_object* v_m_333_, lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_cls_337_){
_start:
{
lean_object* v_toApplicative_338_; lean_object* v_toBind_339_; lean_object* v_getInheritedTraceOptions_340_; lean_object* v_toPure_341_; lean_object* v___f_342_; lean_object* v___x_343_; 
v_toApplicative_338_ = lean_ctor_get(v_inst_334_, 0);
lean_inc_ref(v_toApplicative_338_);
v_toBind_339_ = lean_ctor_get(v_inst_334_, 1);
lean_inc_n(v_toBind_339_, 2);
lean_dec_ref(v_inst_334_);
v_getInheritedTraceOptions_340_ = lean_ctor_get(v_inst_335_, 2);
lean_inc(v_getInheritedTraceOptions_340_);
lean_dec_ref(v_inst_335_);
v_toPure_341_ = lean_ctor_get(v_toApplicative_338_, 1);
lean_inc(v_toPure_341_);
lean_dec_ref(v_toApplicative_338_);
v___f_342_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_342_, 0, v_toPure_341_);
lean_closure_set(v___f_342_, 1, v_cls_337_);
lean_closure_set(v___f_342_, 2, v_toBind_339_);
lean_closure_set(v___f_342_, 3, v_inst_336_);
v___x_343_ = lean_apply_4(v_toBind_339_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_340_, v___f_342_);
return v___x_343_;
}
}
LEAN_EXPORT uint8_t lean_is_trace_class_enabled(lean_object* v_opts_344_, lean_object* v_cls_345_){
_start:
{
uint8_t v_hasTrace_347_; 
v_hasTrace_347_ = lean_ctor_get_uint8(v_opts_344_, sizeof(void*)*1);
if (v_hasTrace_347_ == 0)
{
lean_dec(v_cls_345_);
lean_dec_ref(v_opts_344_);
return v_hasTrace_347_;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_348_ = l_Lean_inheritedTraceOptions;
v___x_349_ = lean_st_ref_get(v___x_348_);
v___x_350_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_351_ = l_Lean_Name_append(v___x_350_, v_cls_345_);
v___x_352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_349_, v_opts_344_, v___x_351_);
lean_dec(v___x_351_);
lean_dec_ref(v_opts_344_);
lean_dec(v___x_349_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object* v_opts_353_, lean_object* v_cls_354_, lean_object* v_a_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = lean_is_trace_class_enabled(v_opts_353_, v_cls_354_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object* v_toPure_358_, lean_object* v_s_359_){
_start:
{
lean_object* v_traces_360_; lean_object* v___x_361_; 
v_traces_360_ = lean_ctor_get(v_s_359_, 0);
lean_inc_ref(v_traces_360_);
lean_dec_ref(v_s_359_);
v___x_361_ = lean_apply_2(v_toPure_358_, lean_box(0), v_traces_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object* v_inst_362_, lean_object* v_inst_363_){
_start:
{
lean_object* v_toApplicative_364_; lean_object* v_toBind_365_; lean_object* v_getTraceState_366_; lean_object* v_toPure_367_; lean_object* v___f_368_; lean_object* v___x_369_; 
v_toApplicative_364_ = lean_ctor_get(v_inst_362_, 0);
lean_inc_ref(v_toApplicative_364_);
v_toBind_365_ = lean_ctor_get(v_inst_362_, 1);
lean_inc(v_toBind_365_);
lean_dec_ref(v_inst_362_);
v_getTraceState_366_ = lean_ctor_get(v_inst_363_, 1);
lean_inc(v_getTraceState_366_);
lean_dec_ref(v_inst_363_);
v_toPure_367_ = lean_ctor_get(v_toApplicative_364_, 1);
lean_inc(v_toPure_367_);
lean_dec_ref(v_toApplicative_364_);
v___f_368_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_368_, 0, v_toPure_367_);
v___x_369_ = lean_apply_4(v_toBind_365_, lean_box(0), lean_box(0), v_getTraceState_366_, v___f_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object* v_m_370_, lean_object* v_inst_371_, lean_object* v_inst_372_){
_start:
{
lean_object* v_toApplicative_373_; lean_object* v_toBind_374_; lean_object* v_getTraceState_375_; lean_object* v_toPure_376_; lean_object* v___f_377_; lean_object* v___x_378_; 
v_toApplicative_373_ = lean_ctor_get(v_inst_371_, 0);
lean_inc_ref(v_toApplicative_373_);
v_toBind_374_ = lean_ctor_get(v_inst_371_, 1);
lean_inc(v_toBind_374_);
lean_dec_ref(v_inst_371_);
v_getTraceState_375_ = lean_ctor_get(v_inst_372_, 1);
lean_inc(v_getTraceState_375_);
lean_dec_ref(v_inst_372_);
v_toPure_376_ = lean_ctor_get(v_toApplicative_373_, 1);
lean_inc(v_toPure_376_);
lean_dec_ref(v_toApplicative_373_);
v___f_377_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_377_, 0, v_toPure_376_);
v___x_378_ = lean_apply_4(v_toBind_374_, lean_box(0), lean_box(0), v_getTraceState_375_, v___f_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object* v_f_379_, lean_object* v_s_380_){
_start:
{
uint64_t v_tid_381_; lean_object* v_traces_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_tid_381_ = lean_ctor_get_uint64(v_s_380_, sizeof(void*)*1);
v_traces_382_ = lean_ctor_get(v_s_380_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v_s_380_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v_s_380_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_traces_382_);
lean_dec(v_s_380_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_apply_1(v_f_379_, v_traces_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
lean_ctor_set_uint64(v_reuseFailAlloc_389_, sizeof(void*)*1, v_tid_381_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object* v_inst_391_, lean_object* v_f_392_){
_start:
{
lean_object* v_modifyTraceState_393_; lean_object* v___f_394_; lean_object* v___x_395_; 
v_modifyTraceState_393_ = lean_ctor_get(v_inst_391_, 0);
lean_inc(v_modifyTraceState_393_);
lean_dec_ref(v_inst_391_);
v___f_394_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_394_, 0, v_f_392_);
v___x_395_ = lean_apply_1(v_modifyTraceState_393_, v___f_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object* v_m_396_, lean_object* v_inst_397_, lean_object* v_f_398_){
_start:
{
lean_object* v_modifyTraceState_399_; lean_object* v___f_400_; lean_object* v___x_401_; 
v_modifyTraceState_399_ = lean_ctor_get(v_inst_397_, 0);
lean_inc(v_modifyTraceState_399_);
lean_dec_ref(v_inst_397_);
v___f_400_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_400_, 0, v_f_398_);
v___x_401_ = lean_apply_1(v_modifyTraceState_399_, v___f_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object* v_s_402_, lean_object* v_x_403_){
_start:
{
lean_inc_ref(v_s_402_);
return v_s_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object* v_s_404_, lean_object* v_x_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_setTraceState___redArg___lam__0(v_s_404_, v_x_405_);
lean_dec_ref(v_x_405_);
lean_dec_ref(v_s_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object* v_inst_407_, lean_object* v_s_408_){
_start:
{
lean_object* v_modifyTraceState_409_; lean_object* v___f_410_; lean_object* v___x_411_; 
v_modifyTraceState_409_ = lean_ctor_get(v_inst_407_, 0);
lean_inc(v_modifyTraceState_409_);
lean_dec_ref(v_inst_407_);
v___f_410_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_410_, 0, v_s_408_);
v___x_411_ = lean_apply_1(v_modifyTraceState_409_, v___f_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object* v_m_412_, lean_object* v_inst_413_, lean_object* v_s_414_){
_start:
{
lean_object* v_modifyTraceState_415_; lean_object* v___f_416_; lean_object* v___x_417_; 
v_modifyTraceState_415_ = lean_ctor_get(v_inst_413_, 0);
lean_inc(v_modifyTraceState_415_);
lean_dec_ref(v_inst_413_);
v___f_416_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_416_, 0, v_s_414_);
v___x_417_ = lean_apply_1(v_modifyTraceState_415_, v___f_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object* v_s_418_){
_start:
{
uint64_t v_tid_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_429_; 
v_tid_419_ = lean_ctor_get_uint64(v_s_418_, sizeof(void*)*1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_s_418_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; 
v_unused_430_ = lean_ctor_get(v_s_418_, 0);
lean_dec(v_unused_430_);
v___x_421_ = v_s_418_;
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
else
{
lean_dec(v_s_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_423_ = lean_unsigned_to_nat(32u);
v___x_424_ = lean_mk_empty_array_with_capacity(v___x_423_);
lean_dec_ref(v___x_424_);
v___x_425_ = lean_obj_once(&l_Lean_resetTraceState___redArg___lam__0___closed__1, &l_Lean_resetTraceState___redArg___lam__0___closed__1_once, _init_l_Lean_resetTraceState___redArg___lam__0___closed__1);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_425_);
v___x_427_ = v___x_421_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
lean_ctor_set_uint64(v_reuseFailAlloc_428_, sizeof(void*)*1, v_tid_419_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object* v_toPure_431_, lean_object* v_oldTraces_432_, lean_object* v_____r_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = lean_apply_2(v_toPure_431_, lean_box(0), v_oldTraces_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object* v_toPure_435_, lean_object* v_modifyTraceState_436_, lean_object* v___f_437_, lean_object* v_toBind_438_, lean_object* v_oldTraces_439_){
_start:
{
lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___f_440_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_440_, 0, v_toPure_435_);
lean_closure_set(v___f_440_, 1, v_oldTraces_439_);
v___x_441_ = lean_apply_1(v_modifyTraceState_436_, v___f_437_);
v___x_442_ = lean_apply_4(v_toBind_438_, lean_box(0), lean_box(0), v___x_441_, v___f_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object* v_inst_444_, lean_object* v_inst_445_){
_start:
{
lean_object* v_toApplicative_446_; lean_object* v_toBind_447_; lean_object* v_modifyTraceState_448_; lean_object* v_getTraceState_449_; lean_object* v_toPure_450_; lean_object* v___f_451_; lean_object* v___f_452_; lean_object* v___f_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_toApplicative_446_ = lean_ctor_get(v_inst_444_, 0);
lean_inc_ref(v_toApplicative_446_);
v_toBind_447_ = lean_ctor_get(v_inst_444_, 1);
lean_inc_n(v_toBind_447_, 3);
lean_dec_ref(v_inst_444_);
v_modifyTraceState_448_ = lean_ctor_get(v_inst_445_, 0);
lean_inc(v_modifyTraceState_448_);
v_getTraceState_449_ = lean_ctor_get(v_inst_445_, 1);
lean_inc(v_getTraceState_449_);
lean_dec_ref(v_inst_445_);
v_toPure_450_ = lean_ctor_get(v_toApplicative_446_, 1);
lean_inc_n(v_toPure_450_, 2);
lean_dec_ref(v_toApplicative_446_);
v___f_451_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0));
v___f_452_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_452_, 0, v_toPure_450_);
lean_closure_set(v___f_452_, 1, v_modifyTraceState_448_);
lean_closure_set(v___f_452_, 2, v___f_451_);
lean_closure_set(v___f_452_, 3, v_toBind_447_);
v___f_453_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_453_, 0, v_toPure_450_);
v___x_454_ = lean_apply_4(v_toBind_447_, lean_box(0), lean_box(0), v_getTraceState_449_, v___f_453_);
v___x_455_ = lean_apply_4(v_toBind_447_, lean_box(0), lean_box(0), v___x_454_, v___f_452_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object* v_m_456_, lean_object* v_inst_457_, lean_object* v_inst_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_457_, v_inst_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object* v_ref_460_, lean_object* v_msg_461_, lean_object* v_s_462_){
_start:
{
uint64_t v_tid_463_; lean_object* v_traces_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_473_; 
v_tid_463_ = lean_ctor_get_uint64(v_s_462_, sizeof(void*)*1);
v_traces_464_ = lean_ctor_get(v_s_462_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_s_462_);
if (v_isSharedCheck_473_ == 0)
{
v___x_466_ = v_s_462_;
v_isShared_467_ = v_isSharedCheck_473_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_traces_464_);
lean_dec(v_s_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_473_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v_ref_460_);
lean_ctor_set(v___x_468_, 1, v_msg_461_);
v___x_469_ = l_Lean_PersistentArray_push___redArg(v_traces_464_, v___x_468_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_469_);
v___x_471_ = v___x_466_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_469_);
lean_ctor_set_uint64(v_reuseFailAlloc_472_, sizeof(void*)*1, v_tid_463_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object* v_inst_474_, lean_object* v_ref_475_, lean_object* v_msg_476_){
_start:
{
lean_object* v_modifyTraceState_477_; lean_object* v___f_478_; lean_object* v___x_479_; 
v_modifyTraceState_477_ = lean_ctor_get(v_inst_474_, 0);
lean_inc(v_modifyTraceState_477_);
lean_dec_ref(v_inst_474_);
v___f_478_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__0), 3, 2);
lean_closure_set(v___f_478_, 0, v_ref_475_);
lean_closure_set(v___f_478_, 1, v_msg_476_);
v___x_479_ = lean_apply_1(v_modifyTraceState_477_, v___f_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_msg_482_, lean_object* v_toBind_483_, lean_object* v_ref_484_){
_start:
{
lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___f_485_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__1), 3, 2);
lean_closure_set(v___f_485_, 0, v_inst_480_);
lean_closure_set(v___f_485_, 1, v_ref_484_);
v___x_486_ = lean_apply_1(v_inst_481_, v_msg_482_);
v___x_487_ = lean_apply_4(v_toBind_483_, lean_box(0), lean_box(0), v___x_486_, v___f_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_msg_492_){
_start:
{
lean_object* v_toBind_493_; lean_object* v_getRef_494_; lean_object* v___f_495_; lean_object* v___x_496_; 
v_toBind_493_ = lean_ctor_get(v_inst_488_, 1);
lean_inc_n(v_toBind_493_, 2);
lean_dec_ref(v_inst_488_);
v_getRef_494_ = lean_ctor_get(v_inst_490_, 0);
lean_inc(v_getRef_494_);
lean_dec_ref(v_inst_490_);
v___f_495_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__2), 5, 4);
lean_closure_set(v___f_495_, 0, v_inst_489_);
lean_closure_set(v___f_495_, 1, v_inst_491_);
lean_closure_set(v___f_495_, 2, v_msg_492_);
lean_closure_set(v___f_495_, 3, v_toBind_493_);
v___x_496_ = lean_apply_4(v_toBind_493_, lean_box(0), lean_box(0), v_getRef_494_, v___f_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object* v_m_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_msg_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_addRawTrace___redArg(v_inst_498_, v_inst_499_, v_inst_500_, v_inst_501_, v_msg_502_);
return v___x_503_;
}
}
static double _init_l_Lean_addTrace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_504_; double v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_float_of_nat(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object* v_cls_509_, lean_object* v_msg_510_, lean_object* v_ref_511_, lean_object* v_s_512_){
_start:
{
uint64_t v_tid_513_; lean_object* v_traces_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_530_; 
v_tid_513_ = lean_ctor_get_uint64(v_s_512_, sizeof(void*)*1);
v_traces_514_ = lean_ctor_get(v_s_512_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_s_512_);
if (v_isSharedCheck_530_ == 0)
{
v___x_516_ = v_s_512_;
v_isShared_517_ = v_isSharedCheck_530_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_traces_514_);
lean_dec(v_s_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_530_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; double v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_518_ = lean_box(0);
v___x_519_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
v___x_520_ = 0;
v___x_521_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_522_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_522_, 0, v_cls_509_);
lean_ctor_set(v___x_522_, 1, v___x_518_);
lean_ctor_set(v___x_522_, 2, v___x_521_);
lean_ctor_set_float(v___x_522_, sizeof(void*)*3, v___x_519_);
lean_ctor_set_float(v___x_522_, sizeof(void*)*3 + 8, v___x_519_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*3 + 16, v___x_520_);
v___x_523_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
v___x_524_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v_msg_510_);
lean_ctor_set(v___x_524_, 2, v___x_523_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v_ref_511_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_PersistentArray_push___redArg(v_traces_514_, v___x_525_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_526_);
v___x_528_ = v___x_516_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
lean_ctor_set_uint64(v_reuseFailAlloc_529_, sizeof(void*)*1, v_tid_513_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object* v_inst_531_, lean_object* v_cls_532_, lean_object* v_ref_533_, lean_object* v_msg_534_){
_start:
{
lean_object* v_modifyTraceState_535_; lean_object* v___f_536_; lean_object* v___x_537_; 
v_modifyTraceState_535_ = lean_ctor_get(v_inst_531_, 0);
lean_inc(v_modifyTraceState_535_);
lean_dec_ref(v_inst_531_);
v___f_536_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_536_, 0, v_cls_532_);
lean_closure_set(v___f_536_, 1, v_msg_534_);
lean_closure_set(v___f_536_, 2, v_ref_533_);
v___x_537_ = lean_apply_1(v_modifyTraceState_535_, v___f_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object* v_inst_538_, lean_object* v_cls_539_, lean_object* v_inst_540_, lean_object* v_msg_541_, lean_object* v_toBind_542_, lean_object* v_ref_543_){
_start:
{
lean_object* v___f_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___f_544_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__1), 4, 3);
lean_closure_set(v___f_544_, 0, v_inst_538_);
lean_closure_set(v___f_544_, 1, v_cls_539_);
lean_closure_set(v___f_544_, 2, v_ref_543_);
v___x_545_ = lean_apply_1(v_inst_540_, v_msg_541_);
v___x_546_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_545_, v___f_544_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_cls_551_, lean_object* v_msg_552_){
_start:
{
lean_object* v_toBind_553_; lean_object* v_getRef_554_; lean_object* v___f_555_; lean_object* v___x_556_; 
v_toBind_553_ = lean_ctor_get(v_inst_547_, 1);
lean_inc_n(v_toBind_553_, 2);
lean_dec_ref(v_inst_547_);
v_getRef_554_ = lean_ctor_get(v_inst_549_, 0);
lean_inc(v_getRef_554_);
lean_dec_ref(v_inst_549_);
v___f_555_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__2), 6, 5);
lean_closure_set(v___f_555_, 0, v_inst_548_);
lean_closure_set(v___f_555_, 1, v_cls_551_);
lean_closure_set(v___f_555_, 2, v_inst_550_);
lean_closure_set(v___f_555_, 3, v_msg_552_);
lean_closure_set(v___f_555_, 4, v_toBind_553_);
v___x_556_ = lean_apply_4(v_toBind_553_, lean_box(0), lean_box(0), v_getRef_554_, v___f_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object* v_m_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_cls_562_, lean_object* v_msg_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_addTrace___redArg(v_inst_558_, v_inst_559_, v_inst_560_, v_inst_561_, v_cls_562_, v_msg_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0(lean_object* v_toPure_565_, lean_object* v_msg_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_cls_571_, uint8_t v_____do__lift_572_){
_start:
{
if (v_____do__lift_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v_cls_571_);
lean_dec(v_inst_570_);
lean_dec_ref(v_inst_569_);
lean_dec_ref(v_inst_568_);
lean_dec_ref(v_inst_567_);
lean_dec_ref(v_msg_566_);
v___x_573_ = lean_box(0);
v___x_574_ = lean_apply_2(v_toPure_565_, lean_box(0), v___x_573_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_toPure_565_);
v___x_575_ = lean_box(0);
v___x_576_ = lean_apply_1(v_msg_566_, v___x_575_);
v___x_577_ = l_Lean_addTrace___redArg(v_inst_567_, v_inst_568_, v_inst_569_, v_inst_570_, v_cls_571_, v___x_576_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object* v_toPure_578_, lean_object* v_msg_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_cls_584_, lean_object* v_____do__lift_585_){
_start:
{
uint8_t v_____do__lift_147__boxed_586_; lean_object* v_res_587_; 
v_____do__lift_147__boxed_586_ = lean_unbox(v_____do__lift_585_);
v_res_587_ = l_Lean_trace___redArg___lam__0(v_toPure_578_, v_msg_579_, v_inst_580_, v_inst_581_, v_inst_582_, v_inst_583_, v_cls_584_, v_____do__lift_147__boxed_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_cls_593_, lean_object* v_msg_594_){
_start:
{
lean_object* v_toApplicative_595_; lean_object* v_toBind_596_; lean_object* v_getInheritedTraceOptions_597_; lean_object* v_toPure_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_toApplicative_595_ = lean_ctor_get(v_inst_588_, 0);
v_toBind_596_ = lean_ctor_get(v_inst_588_, 1);
lean_inc_n(v_toBind_596_, 3);
v_getInheritedTraceOptions_597_ = lean_ctor_get(v_inst_589_, 2);
lean_inc(v_getInheritedTraceOptions_597_);
v_toPure_598_ = lean_ctor_get(v_toApplicative_595_, 1);
lean_inc_n(v_toPure_598_, 2);
lean_inc(v_cls_593_);
v___f_599_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_599_, 0, v_toPure_598_);
lean_closure_set(v___f_599_, 1, v_msg_594_);
lean_closure_set(v___f_599_, 2, v_inst_588_);
lean_closure_set(v___f_599_, 3, v_inst_589_);
lean_closure_set(v___f_599_, 4, v_inst_590_);
lean_closure_set(v___f_599_, 5, v_inst_591_);
lean_closure_set(v___f_599_, 6, v_cls_593_);
v___f_600_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_600_, 0, v_toPure_598_);
lean_closure_set(v___f_600_, 1, v_cls_593_);
lean_closure_set(v___f_600_, 2, v_toBind_596_);
lean_closure_set(v___f_600_, 3, v_inst_592_);
v___x_601_ = lean_apply_4(v_toBind_596_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_597_, v___f_600_);
v___x_602_ = lean_apply_4(v_toBind_596_, lean_box(0), lean_box(0), v___x_601_, v___f_599_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace(lean_object* v_m_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_cls_609_, lean_object* v_msg_610_){
_start:
{
lean_object* v_toApplicative_611_; lean_object* v_toBind_612_; lean_object* v_getInheritedTraceOptions_613_; lean_object* v_toPure_614_; lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_toApplicative_611_ = lean_ctor_get(v_inst_604_, 0);
v_toBind_612_ = lean_ctor_get(v_inst_604_, 1);
lean_inc_n(v_toBind_612_, 3);
v_getInheritedTraceOptions_613_ = lean_ctor_get(v_inst_605_, 2);
lean_inc(v_getInheritedTraceOptions_613_);
v_toPure_614_ = lean_ctor_get(v_toApplicative_611_, 1);
lean_inc_n(v_toPure_614_, 2);
lean_inc(v_cls_609_);
v___f_615_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_615_, 0, v_toPure_614_);
lean_closure_set(v___f_615_, 1, v_msg_610_);
lean_closure_set(v___f_615_, 2, v_inst_604_);
lean_closure_set(v___f_615_, 3, v_inst_605_);
lean_closure_set(v___f_615_, 4, v_inst_606_);
lean_closure_set(v___f_615_, 5, v_inst_607_);
lean_closure_set(v___f_615_, 6, v_cls_609_);
v___f_616_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_616_, 0, v_toPure_614_);
lean_closure_set(v___f_616_, 1, v_cls_609_);
lean_closure_set(v___f_616_, 2, v_toBind_612_);
lean_closure_set(v___f_616_, 3, v_inst_608_);
v___x_617_ = lean_apply_4(v_toBind_612_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_613_, v___f_616_);
v___x_618_ = lean_apply_4(v_toBind_612_, lean_box(0), lean_box(0), v___x_617_, v___f_615_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_cls_623_, lean_object* v_msg_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_addTrace___redArg(v_inst_619_, v_inst_620_, v_inst_621_, v_inst_622_, v_cls_623_, v_msg_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1(lean_object* v_toPure_626_, lean_object* v_toBind_627_, lean_object* v_mkMsg_628_, lean_object* v___f_629_, uint8_t v_____do__lift_630_){
_start:
{
if (v_____do__lift_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v___f_629_);
lean_dec(v_mkMsg_628_);
lean_dec(v_toBind_627_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_apply_2(v_toPure_626_, lean_box(0), v___x_631_);
return v___x_632_;
}
else
{
lean_object* v___x_633_; 
lean_dec(v_toPure_626_);
v___x_633_ = lean_apply_4(v_toBind_627_, lean_box(0), lean_box(0), v_mkMsg_628_, v___f_629_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object* v_toPure_634_, lean_object* v_toBind_635_, lean_object* v_mkMsg_636_, lean_object* v___f_637_, lean_object* v_____do__lift_638_){
_start:
{
uint8_t v_____do__lift_153__boxed_639_; lean_object* v_res_640_; 
v_____do__lift_153__boxed_639_ = lean_unbox(v_____do__lift_638_);
v_res_640_ = l_Lean_traceM___redArg___lam__1(v_toPure_634_, v_toBind_635_, v_mkMsg_636_, v___f_637_, v_____do__lift_153__boxed_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_cls_646_, lean_object* v_mkMsg_647_){
_start:
{
lean_object* v_toApplicative_648_; lean_object* v_toBind_649_; lean_object* v_getInheritedTraceOptions_650_; lean_object* v_toPure_651_; lean_object* v___f_652_; lean_object* v___f_653_; lean_object* v___f_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_toApplicative_648_ = lean_ctor_get(v_inst_641_, 0);
v_toBind_649_ = lean_ctor_get(v_inst_641_, 1);
lean_inc_n(v_toBind_649_, 4);
v_getInheritedTraceOptions_650_ = lean_ctor_get(v_inst_642_, 2);
lean_inc(v_getInheritedTraceOptions_650_);
v_toPure_651_ = lean_ctor_get(v_toApplicative_648_, 1);
lean_inc_n(v_toPure_651_, 2);
lean_inc(v_cls_646_);
v___f_652_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_652_, 0, v_inst_641_);
lean_closure_set(v___f_652_, 1, v_inst_642_);
lean_closure_set(v___f_652_, 2, v_inst_643_);
lean_closure_set(v___f_652_, 3, v_inst_644_);
lean_closure_set(v___f_652_, 4, v_cls_646_);
v___f_653_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_653_, 0, v_toPure_651_);
lean_closure_set(v___f_653_, 1, v_toBind_649_);
lean_closure_set(v___f_653_, 2, v_mkMsg_647_);
lean_closure_set(v___f_653_, 3, v___f_652_);
v___f_654_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_654_, 0, v_toPure_651_);
lean_closure_set(v___f_654_, 1, v_cls_646_);
lean_closure_set(v___f_654_, 2, v_toBind_649_);
lean_closure_set(v___f_654_, 3, v_inst_645_);
v___x_655_ = lean_apply_4(v_toBind_649_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_650_, v___f_654_);
v___x_656_ = lean_apply_4(v_toBind_649_, lean_box(0), lean_box(0), v___x_655_, v___f_653_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object* v_m_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_cls_663_, lean_object* v_mkMsg_664_){
_start:
{
lean_object* v_toApplicative_665_; lean_object* v_toBind_666_; lean_object* v_getInheritedTraceOptions_667_; lean_object* v_toPure_668_; lean_object* v___f_669_; lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_toApplicative_665_ = lean_ctor_get(v_inst_658_, 0);
v_toBind_666_ = lean_ctor_get(v_inst_658_, 1);
lean_inc_n(v_toBind_666_, 4);
v_getInheritedTraceOptions_667_ = lean_ctor_get(v_inst_659_, 2);
lean_inc(v_getInheritedTraceOptions_667_);
v_toPure_668_ = lean_ctor_get(v_toApplicative_665_, 1);
lean_inc_n(v_toPure_668_, 2);
lean_inc(v_cls_663_);
v___f_669_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_669_, 0, v_inst_658_);
lean_closure_set(v___f_669_, 1, v_inst_659_);
lean_closure_set(v___f_669_, 2, v_inst_660_);
lean_closure_set(v___f_669_, 3, v_inst_661_);
lean_closure_set(v___f_669_, 4, v_cls_663_);
v___f_670_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_670_, 0, v_toPure_668_);
lean_closure_set(v___f_670_, 1, v_toBind_666_);
lean_closure_set(v___f_670_, 2, v_mkMsg_664_);
lean_closure_set(v___f_670_, 3, v___f_669_);
v___f_671_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_671_, 0, v_toPure_668_);
lean_closure_set(v___f_671_, 1, v_cls_663_);
lean_closure_set(v___f_671_, 2, v_toBind_666_);
lean_closure_set(v___f_671_, 3, v_inst_662_);
v___x_672_ = lean_apply_4(v_toBind_666_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_667_, v___f_671_);
v___x_673_ = lean_apply_4(v_toBind_666_, lean_box(0), lean_box(0), v___x_672_, v___f_670_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object* v_x_674_){
_start:
{
lean_object* v_msg_675_; 
v_msg_675_ = lean_ctor_get(v_x_674_, 1);
lean_inc_ref(v_msg_675_);
return v_msg_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object* v_x_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_676_);
lean_dec_ref(v_x_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object* v_ref_678_, lean_object* v_msg_679_, lean_object* v_oldTraces_680_, lean_object* v_s_681_){
_start:
{
uint64_t v_tid_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_691_; 
v_tid_682_ = lean_ctor_get_uint64(v_s_681_, sizeof(void*)*1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_s_681_);
if (v_isSharedCheck_691_ == 0)
{
lean_object* v_unused_692_; 
v_unused_692_ = lean_ctor_get(v_s_681_, 0);
lean_dec(v_unused_692_);
v___x_684_ = v_s_681_;
v_isShared_685_ = v_isSharedCheck_691_;
goto v_resetjp_683_;
}
else
{
lean_dec(v_s_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_691_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_ref_678_);
lean_ctor_set(v___x_686_, 1, v_msg_679_);
v___x_687_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_680_, v___x_686_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_687_);
v___x_689_ = v___x_684_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
lean_ctor_set_uint64(v_reuseFailAlloc_690_, sizeof(void*)*1, v_tid_682_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object* v_ref_693_, lean_object* v_oldTraces_694_, lean_object* v_modifyTraceState_695_, lean_object* v_msg_696_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; 
v___f_697_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0), 4, 3);
lean_closure_set(v___f_697_, 0, v_ref_693_);
lean_closure_set(v___f_697_, 1, v_msg_696_);
lean_closure_set(v___f_697_, 2, v_oldTraces_694_);
v___x_698_ = lean_apply_1(v_modifyTraceState_695_, v___f_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object* v___f_718_, lean_object* v_data_719_, lean_object* v_msg_720_, lean_object* v_inst_721_, lean_object* v_toBind_722_, lean_object* v___f_723_, lean_object* v_____do__lift_724_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; size_t v_sz_727_; size_t v___x_728_; lean_object* v___x_729_; lean_object* v_msg_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_725_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_724_);
v___x_726_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v_sz_727_ = lean_array_size(v___x_725_);
v___x_728_ = ((size_t)0ULL);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_726_, v___f_718_, v_sz_727_, v___x_728_, v___x_725_);
v_msg_730_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_730_, 0, v_data_719_);
lean_ctor_set(v_msg_730_, 1, v_msg_720_);
lean_ctor_set(v_msg_730_, 2, v___x_729_);
v___x_731_ = lean_apply_1(v_inst_721_, v_msg_730_);
v___x_732_ = lean_apply_4(v_toBind_722_, lean_box(0), lean_box(0), v___x_731_, v___f_723_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object* v___f_733_, lean_object* v_data_734_, lean_object* v_msg_735_, lean_object* v_inst_736_, lean_object* v_toBind_737_, lean_object* v___f_738_, lean_object* v_____do__lift_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(v___f_733_, v_data_734_, v_msg_735_, v_inst_736_, v_toBind_737_, v___f_738_, v_____do__lift_739_);
lean_dec_ref(v_____do__lift_739_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object* v_ref_741_, lean_object* v_withRef_742_, lean_object* v___x_743_, lean_object* v_oldRef_744_){
_start:
{
lean_object* v_ref_745_; lean_object* v___x_746_; 
v_ref_745_ = l_Lean_replaceRef(v_ref_741_, v_oldRef_744_);
v___x_746_ = lean_apply_3(v_withRef_742_, lean_box(0), v_ref_745_, v___x_743_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object* v_ref_747_, lean_object* v_withRef_748_, lean_object* v___x_749_, lean_object* v_oldRef_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(v_ref_747_, v_withRef_748_, v___x_749_, v_oldRef_750_);
lean_dec(v_oldRef_750_);
lean_dec(v_ref_747_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_oldTraces_757_, lean_object* v_data_758_, lean_object* v_ref_759_, lean_object* v_msg_760_){
_start:
{
lean_object* v_toApplicative_761_; lean_object* v_toBind_762_; lean_object* v_modifyTraceState_763_; lean_object* v_getTraceState_764_; lean_object* v_toPure_765_; lean_object* v_getRef_766_; lean_object* v_withRef_767_; lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_775_; 
v_toApplicative_761_ = lean_ctor_get(v_inst_753_, 0);
lean_inc_ref(v_toApplicative_761_);
v_toBind_762_ = lean_ctor_get(v_inst_753_, 1);
lean_inc_n(v_toBind_762_, 4);
lean_dec_ref(v_inst_753_);
v_modifyTraceState_763_ = lean_ctor_get(v_inst_754_, 0);
lean_inc(v_modifyTraceState_763_);
v_getTraceState_764_ = lean_ctor_get(v_inst_754_, 1);
lean_inc(v_getTraceState_764_);
lean_dec_ref(v_inst_754_);
v_toPure_765_ = lean_ctor_get(v_toApplicative_761_, 1);
lean_inc(v_toPure_765_);
lean_dec_ref(v_toApplicative_761_);
v_getRef_766_ = lean_ctor_get(v_inst_755_, 0);
lean_inc(v_getRef_766_);
v_withRef_767_ = lean_ctor_get(v_inst_755_, 1);
lean_inc(v_withRef_767_);
lean_dec_ref(v_inst_755_);
v___f_768_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_768_, 0, v_toPure_765_);
v___x_769_ = lean_apply_4(v_toBind_762_, lean_box(0), lean_box(0), v_getTraceState_764_, v___f_768_);
v___f_770_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0));
lean_inc(v_ref_759_);
v___f_771_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2), 4, 3);
lean_closure_set(v___f_771_, 0, v_ref_759_);
lean_closure_set(v___f_771_, 1, v_oldTraces_757_);
lean_closure_set(v___f_771_, 2, v_modifyTraceState_763_);
v___f_772_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_772_, 0, v___f_770_);
lean_closure_set(v___f_772_, 1, v_data_758_);
lean_closure_set(v___f_772_, 2, v_msg_760_);
lean_closure_set(v___f_772_, 3, v_inst_756_);
lean_closure_set(v___f_772_, 4, v_toBind_762_);
lean_closure_set(v___f_772_, 5, v___f_771_);
v___x_773_ = lean_apply_4(v_toBind_762_, lean_box(0), lean_box(0), v___x_769_, v___f_772_);
v___f_774_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_774_, 0, v_ref_759_);
lean_closure_set(v___f_774_, 1, v_withRef_767_);
lean_closure_set(v___f_774_, 2, v___x_773_);
v___x_775_ = lean_apply_4(v_toBind_762_, lean_box(0), lean_box(0), v_getRef_766_, v___f_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object* v_m_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_oldTraces_781_, lean_object* v_data_782_, lean_object* v_ref_783_, lean_object* v_msg_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_777_, v_inst_778_, v_inst_779_, v_inst_780_, v_oldTraces_781_, v_data_782_, v_ref_783_, v_msg_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object* v_name_786_, lean_object* v_decl_787_, lean_object* v_ref_788_){
_start:
{
lean_object* v_defValue_790_; lean_object* v_descr_791_; lean_object* v_deprecation_x3f_792_; lean_object* v___x_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_defValue_790_ = lean_ctor_get(v_decl_787_, 0);
v_descr_791_ = lean_ctor_get(v_decl_787_, 1);
v_deprecation_x3f_792_ = lean_ctor_get(v_decl_787_, 2);
v___x_793_ = lean_alloc_ctor(1, 0, 1);
v___x_794_ = lean_unbox(v_defValue_790_);
lean_ctor_set_uint8(v___x_793_, 0, v___x_794_);
lean_inc(v_deprecation_x3f_792_);
lean_inc_ref(v_descr_791_);
lean_inc_n(v_name_786_, 2);
v___x_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_795_, 0, v_name_786_);
lean_ctor_set(v___x_795_, 1, v_ref_788_);
lean_ctor_set(v___x_795_, 2, v___x_793_);
lean_ctor_set(v___x_795_, 3, v_descr_791_);
lean_ctor_set(v___x_795_, 4, v_deprecation_x3f_792_);
v___x_796_ = lean_register_option(v_name_786_, v___x_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_804_; 
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v___x_796_, 0);
lean_dec(v_unused_805_);
v___x_798_ = v___x_796_;
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
else
{
lean_dec(v___x_796_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
lean_inc(v_defValue_790_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_name_786_);
lean_ctor_set(v___x_800_, 1, v_defValue_790_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_800_);
v___x_802_ = v___x_798_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v_name_786_);
v_a_806_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_796_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_796_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_814_, lean_object* v_decl_815_, lean_object* v_ref_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_814_, v_decl_815_, v_ref_816_);
lean_dec_ref(v_decl_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_834_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_835_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_836_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_837_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_834_, v___x_835_, v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object* v_name_840_, lean_object* v_decl_841_, lean_object* v_ref_842_){
_start:
{
lean_object* v_defValue_844_; lean_object* v_descr_845_; lean_object* v_deprecation_x3f_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_defValue_844_ = lean_ctor_get(v_decl_841_, 0);
v_descr_845_ = lean_ctor_get(v_decl_841_, 1);
v_deprecation_x3f_846_ = lean_ctor_get(v_decl_841_, 2);
lean_inc(v_defValue_844_);
v___x_847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_847_, 0, v_defValue_844_);
lean_inc(v_deprecation_x3f_846_);
lean_inc_ref(v_descr_845_);
lean_inc_n(v_name_840_, 2);
v___x_848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_848_, 0, v_name_840_);
lean_ctor_set(v___x_848_, 1, v_ref_842_);
lean_ctor_set(v___x_848_, 2, v___x_847_);
lean_ctor_set(v___x_848_, 3, v_descr_845_);
lean_ctor_set(v___x_848_, 4, v_deprecation_x3f_846_);
v___x_849_ = lean_register_option(v_name_840_, v___x_848_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_857_; 
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_857_ == 0)
{
lean_object* v_unused_858_; 
v_unused_858_ = lean_ctor_get(v___x_849_, 0);
lean_dec(v_unused_858_);
v___x_851_ = v___x_849_;
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
else
{
lean_dec(v___x_849_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
lean_inc(v_defValue_844_);
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v_name_840_);
lean_ctor_set(v___x_853_, 1, v_defValue_844_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_853_);
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec(v_name_840_);
v_a_859_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_849_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_849_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_867_, lean_object* v_decl_868_, lean_object* v_ref_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_867_, v_decl_868_, v_ref_869_);
lean_dec_ref(v_decl_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_888_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_889_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_890_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_891_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_888_, v___x_889_, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_911_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_912_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_913_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_914_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_911_, v___x_912_, v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object* v_name_917_, lean_object* v_decl_918_, lean_object* v_ref_919_){
_start:
{
lean_object* v_defValue_921_; lean_object* v_descr_922_; lean_object* v_deprecation_x3f_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_defValue_921_ = lean_ctor_get(v_decl_918_, 0);
v_descr_922_ = lean_ctor_get(v_decl_918_, 1);
v_deprecation_x3f_923_ = lean_ctor_get(v_decl_918_, 2);
lean_inc(v_defValue_921_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v_defValue_921_);
lean_inc(v_deprecation_x3f_923_);
lean_inc_ref(v_descr_922_);
lean_inc_n(v_name_917_, 2);
v___x_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_925_, 0, v_name_917_);
lean_ctor_set(v___x_925_, 1, v_ref_919_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
lean_ctor_set(v___x_925_, 3, v_descr_922_);
lean_ctor_set(v___x_925_, 4, v_deprecation_x3f_923_);
v___x_926_ = lean_register_option(v_name_917_, v___x_925_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_934_; 
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v___x_926_, 0);
lean_dec(v_unused_935_);
v___x_928_ = v___x_926_;
v_isShared_929_ = v_isSharedCheck_934_;
goto v_resetjp_927_;
}
else
{
lean_dec(v___x_926_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_934_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_932_; 
lean_inc(v_defValue_921_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v_name_917_);
lean_ctor_set(v___x_930_, 1, v_defValue_921_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_930_);
v___x_932_ = v___x_928_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_name_917_);
v_a_936_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_926_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_926_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_944_, lean_object* v_decl_945_, lean_object* v_ref_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_944_, v_decl_945_, v_ref_946_);
lean_dec_ref(v_decl_945_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_965_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_966_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_967_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_968_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_965_, v___x_966_, v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_990_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_991_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_992_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_993_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_990_, v___x_991_, v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
return v_res_995_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_996_; double v___x_997_; 
v___x_996_ = lean_unsigned_to_nat(1000000000u);
v___x_997_ = lean_float_of_nat(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object* v_toApplicative_998_, lean_object* v_start_999_, lean_object* v_a_1000_, lean_object* v_stop_1001_){
_start:
{
lean_object* v_toPure_1002_; double v___x_1003_; double v___x_1004_; double v___x_1005_; double v___x_1006_; double v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_toPure_1002_ = lean_ctor_get(v_toApplicative_998_, 1);
lean_inc(v_toPure_1002_);
lean_dec_ref(v_toApplicative_998_);
v___x_1003_ = lean_float_of_nat(v_start_999_);
v___x_1004_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1005_ = lean_float_div(v___x_1003_, v___x_1004_);
v___x_1006_ = lean_float_of_nat(v_stop_1001_);
v___x_1007_ = lean_float_div(v___x_1006_, v___x_1004_);
v___x_1008_ = lean_box_float(v___x_1005_);
v___x_1009_ = lean_box_float(v___x_1007_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_a_1000_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_apply_2(v_toPure_1002_, lean_box(0), v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object* v_toApplicative_1013_, lean_object* v_start_1014_, lean_object* v_toBind_1015_, lean_object* v___x_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___f_1018_; lean_object* v___x_1019_; 
v___f_1018_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1018_, 0, v_toApplicative_1013_);
lean_closure_set(v___f_1018_, 1, v_start_1014_);
lean_closure_set(v___f_1018_, 2, v_a_1017_);
v___x_1019_ = lean_apply_4(v_toBind_1015_, lean_box(0), lean_box(0), v___x_1016_, v___f_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object* v_toApplicative_1020_, lean_object* v_toBind_1021_, lean_object* v___x_1022_, lean_object* v_act_1023_, lean_object* v_start_1024_){
_start:
{
lean_object* v___f_1025_; lean_object* v___x_1026_; 
lean_inc(v_toBind_1021_);
v___f_1025_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1025_, 0, v_toApplicative_1020_);
lean_closure_set(v___f_1025_, 1, v_start_1024_);
lean_closure_set(v___f_1025_, 2, v_toBind_1021_);
lean_closure_set(v___f_1025_, 3, v___x_1022_);
v___x_1026_ = lean_apply_4(v_toBind_1021_, lean_box(0), lean_box(0), v_act_1023_, v___f_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object* v_toApplicative_1027_, lean_object* v_start_1028_, lean_object* v_a_1029_, lean_object* v_stop_1030_){
_start:
{
lean_object* v_toPure_1031_; double v___x_1032_; double v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_toPure_1031_ = lean_ctor_get(v_toApplicative_1027_, 1);
lean_inc(v_toPure_1031_);
lean_dec_ref(v_toApplicative_1027_);
v___x_1032_ = lean_float_of_nat(v_start_1028_);
v___x_1033_ = lean_float_of_nat(v_stop_1030_);
v___x_1034_ = lean_box_float(v___x_1032_);
v___x_1035_ = lean_box_float(v___x_1033_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v_a_1029_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_apply_2(v_toPure_1031_, lean_box(0), v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object* v_toApplicative_1039_, lean_object* v_start_1040_, lean_object* v_toBind_1041_, lean_object* v___x_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___f_1044_; lean_object* v___x_1045_; 
v___f_1044_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1044_, 0, v_toApplicative_1039_);
lean_closure_set(v___f_1044_, 1, v_start_1040_);
lean_closure_set(v___f_1044_, 2, v_a_1043_);
v___x_1045_ = lean_apply_4(v_toBind_1041_, lean_box(0), lean_box(0), v___x_1042_, v___f_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object* v_toApplicative_1046_, lean_object* v_toBind_1047_, lean_object* v___x_1048_, lean_object* v_act_1049_, lean_object* v_start_1050_){
_start:
{
lean_object* v___f_1051_; lean_object* v___x_1052_; 
lean_inc(v_toBind_1047_);
v___f_1051_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1051_, 0, v_toApplicative_1046_);
lean_closure_set(v___f_1051_, 1, v_start_1050_);
lean_closure_set(v___f_1051_, 2, v_toBind_1047_);
lean_closure_set(v___f_1051_, 3, v___x_1048_);
v___x_1052_ = lean_apply_4(v_toBind_1047_, lean_box(0), lean_box(0), v_act_1049_, v___f_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_opts_1057_, lean_object* v_act_1058_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1059_ = l_Lean_KVMap_instValueBool;
v___x_1060_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1061_ = l_Lean_Option_get___redArg(v___x_1059_, v_opts_1057_, v___x_1060_);
v___x_1062_ = lean_unbox(v___x_1061_);
lean_dec(v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v_toApplicative_1063_; lean_object* v_toBind_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; 
v_toApplicative_1063_ = lean_ctor_get(v_inst_1055_, 0);
lean_inc_ref(v_toApplicative_1063_);
v_toBind_1064_ = lean_ctor_get(v_inst_1055_, 1);
lean_inc_n(v_toBind_1064_, 2);
lean_dec_ref(v_inst_1055_);
v___x_1065_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1066_ = lean_apply_2(v_inst_1056_, lean_box(0), v___x_1065_);
lean_inc(v___x_1066_);
v___f_1067_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1067_, 0, v_toApplicative_1063_);
lean_closure_set(v___f_1067_, 1, v_toBind_1064_);
lean_closure_set(v___f_1067_, 2, v___x_1066_);
lean_closure_set(v___f_1067_, 3, v_act_1058_);
v___x_1068_ = lean_apply_4(v_toBind_1064_, lean_box(0), lean_box(0), v___x_1066_, v___f_1067_);
return v___x_1068_;
}
else
{
lean_object* v_toApplicative_1069_; lean_object* v_toBind_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___f_1073_; lean_object* v___x_1074_; 
v_toApplicative_1069_ = lean_ctor_get(v_inst_1055_, 0);
lean_inc_ref(v_toApplicative_1069_);
v_toBind_1070_ = lean_ctor_get(v_inst_1055_, 1);
lean_inc_n(v_toBind_1070_, 2);
lean_dec_ref(v_inst_1055_);
v___x_1071_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1072_ = lean_apply_2(v_inst_1056_, lean_box(0), v___x_1071_);
lean_inc(v___x_1072_);
v___f_1073_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1073_, 0, v_toApplicative_1069_);
lean_closure_set(v___f_1073_, 1, v_toBind_1070_);
lean_closure_set(v___f_1073_, 2, v___x_1072_);
lean_closure_set(v___f_1073_, 3, v_act_1058_);
v___x_1074_ = lean_apply_4(v_toBind_1070_, lean_box(0), lean_box(0), v___x_1072_, v___f_1073_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_opts_1077_, lean_object* v_act_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(v_inst_1075_, v_inst_1076_, v_opts_1077_, v_act_1078_);
lean_dec_ref(v_opts_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object* v_00_u03b1_1080_, lean_object* v_m_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_opts_1084_, lean_object* v_act_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1086_ = l_Lean_KVMap_instValueBool;
v___x_1087_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1088_ = l_Lean_Option_get___redArg(v___x_1086_, v_opts_1084_, v___x_1087_);
v___x_1089_ = lean_unbox(v___x_1088_);
lean_dec(v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v_toApplicative_1090_; lean_object* v_toBind_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; 
v_toApplicative_1090_ = lean_ctor_get(v_inst_1082_, 0);
lean_inc_ref(v_toApplicative_1090_);
v_toBind_1091_ = lean_ctor_get(v_inst_1082_, 1);
lean_inc_n(v_toBind_1091_, 2);
lean_dec_ref(v_inst_1082_);
v___x_1092_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1093_ = lean_apply_2(v_inst_1083_, lean_box(0), v___x_1092_);
lean_inc(v___x_1093_);
v___f_1094_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1094_, 0, v_toApplicative_1090_);
lean_closure_set(v___f_1094_, 1, v_toBind_1091_);
lean_closure_set(v___f_1094_, 2, v___x_1093_);
lean_closure_set(v___f_1094_, 3, v_act_1085_);
v___x_1095_ = lean_apply_4(v_toBind_1091_, lean_box(0), lean_box(0), v___x_1093_, v___f_1094_);
return v___x_1095_;
}
else
{
lean_object* v_toApplicative_1096_; lean_object* v_toBind_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; 
v_toApplicative_1096_ = lean_ctor_get(v_inst_1082_, 0);
lean_inc_ref(v_toApplicative_1096_);
v_toBind_1097_ = lean_ctor_get(v_inst_1082_, 1);
lean_inc_n(v_toBind_1097_, 2);
lean_dec_ref(v_inst_1082_);
v___x_1098_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1099_ = lean_apply_2(v_inst_1083_, lean_box(0), v___x_1098_);
lean_inc(v___x_1099_);
v___f_1100_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1100_, 0, v_toApplicative_1096_);
lean_closure_set(v___f_1100_, 1, v_toBind_1097_);
lean_closure_set(v___f_1100_, 2, v___x_1099_);
lean_closure_set(v___f_1100_, 3, v_act_1085_);
v___x_1101_ = lean_apply_4(v_toBind_1097_, lean_box(0), lean_box(0), v___x_1099_, v___f_1100_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object* v_00_u03b1_1102_, lean_object* v_m_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_opts_1106_, lean_object* v_act_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(v_00_u03b1_1102_, v_m_1103_, v_inst_1104_, v_inst_1105_, v_opts_1106_, v_act_1107_);
lean_dec_ref(v_opts_1106_);
return v_res_1108_;
}
}
static double _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0(void){
_start:
{
lean_object* v___x_1109_; double v___x_1110_; 
v___x_1109_ = lean_unsigned_to_nat(1000u);
v___x_1110_ = lean_float_of_nat(v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object* v_o_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1112_ = l_Lean_KVMap_instValueBool;
v___x_1113_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1114_ = l_Lean_Option_get___redArg(v___x_1112_, v_o_1111_, v___x_1113_);
v___x_1115_ = lean_unbox(v___x_1114_);
lean_dec(v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; double v___x_1119_; double v___x_1120_; double v___x_1121_; 
v___x_1116_ = l_Lean_KVMap_instValueNat;
v___x_1117_ = l_Lean_trace_profiler_threshold;
v___x_1118_ = l_Lean_Option_get___redArg(v___x_1116_, v_o_1111_, v___x_1117_);
v___x_1119_ = lean_float_of_nat(v___x_1118_);
v___x_1120_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1121_ = lean_float_div(v___x_1119_, v___x_1120_);
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; double v___x_1125_; 
v___x_1122_ = l_Lean_KVMap_instValueNat;
v___x_1123_ = l_Lean_trace_profiler_threshold;
v___x_1124_ = l_Lean_Option_get___redArg(v___x_1122_, v_o_1111_, v___x_1123_);
v___x_1125_ = lean_float_of_nat(v___x_1124_);
return v___x_1125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object* v_o_1126_){
_start:
{
double v_res_1127_; lean_object* v_r_1128_; 
v_res_1127_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1126_);
lean_dec_ref(v_o_1126_);
v_r_1128_ = lean_box_float(v_res_1127_);
return v_r_1128_;
}
}
static lean_object* _init_l_Lean_instMonadAlwaysExceptEIO___closed__0(void){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object* v_00_u03b5_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___closed__0, &l_Lean_instMonadAlwaysExceptEIO___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___closed__0);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object* v_inst_1132_, lean_object* v_always_1133_){
_start:
{
lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; 
lean_inc_ref(v_always_1133_);
v___f_1134_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1134_, 0, v_always_1133_);
lean_closure_set(v___f_1134_, 1, v_inst_1132_);
v___f_1135_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_1135_, 0, v_always_1133_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___f_1134_);
lean_ctor_set(v___x_1136_, 1, v___f_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object* v_m_1137_, lean_object* v_inst_1138_, lean_object* v_00_u03b5_1139_, lean_object* v_00_u03c3_1140_, lean_object* v_always_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_1138_, v_always_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object* v_always_1143_){
_start:
{
lean_object* v___f_1144_; lean_object* v___f_1145_; lean_object* v___x_1146_; 
lean_inc_ref(v_always_1143_);
v___f_1144_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1144_, 0, v_always_1143_);
v___f_1145_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1145_, 0, v_always_1143_);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___f_1144_);
lean_ctor_set(v___x_1146_, 1, v___f_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object* v_m_1147_, lean_object* v_00_u03b5_1148_, lean_object* v_00_u03c9_1149_, lean_object* v_00_u03c3_1150_, lean_object* v_always_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object* v_always_1153_){
_start:
{
lean_object* v___f_1154_; lean_object* v___f_1155_; lean_object* v___x_1156_; 
lean_inc_ref(v_always_1153_);
v___f_1154_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1154_, 0, v_always_1153_);
v___f_1155_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1155_, 0, v_always_1153_);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___f_1154_);
lean_ctor_set(v___x_1156_, 1, v___f_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object* v_m_1157_, lean_object* v_00_u03b5_1158_, lean_object* v_00_u03c1_1159_, lean_object* v_always_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object* v_always_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1163_, v_inst_1164_, v_inst_1165_, v_always_1162_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object* v_00_u03b1_1167_, lean_object* v_m_1168_, lean_object* v_00_u03b5_1169_, lean_object* v_00_u03c9_1170_, lean_object* v_00_u03b2_1171_, lean_object* v_always_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1173_, v_inst_1174_, v_inst_1175_, v_always_1172_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t v_x_1183_){
_start:
{
switch(v_x_1183_)
{
case 0:
{
lean_object* v___x_1184_; 
v___x_1184_ = ((lean_object*)(l_Lean_checkEmoji___closed__0));
return v___x_1184_;
}
case 1:
{
lean_object* v___x_1185_; 
v___x_1185_ = ((lean_object*)(l_Lean_crossEmoji___closed__0));
return v___x_1185_;
}
default: 
{
lean_object* v___x_1186_; 
v___x_1186_ = ((lean_object*)(l_Lean_bombEmoji___closed__0));
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object* v_x_1187_){
_start:
{
uint8_t v_x_31__boxed_1188_; lean_object* v_res_1189_; 
v_x_31__boxed_1188_ = lean_unbox(v_x_1187_);
v_res_1189_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___lam__0(lean_object* v_x_1190_){
_start:
{
if (lean_obj_tag(v_x_1190_) == 0)
{
uint8_t v___x_1191_; 
v___x_1191_ = 2;
return v___x_1191_;
}
else
{
lean_object* v_a_1192_; uint8_t v___x_1193_; 
v_a_1192_ = lean_ctor_get(v_x_1190_, 0);
v___x_1193_ = lean_unbox(v_a_1192_);
if (v___x_1193_ == 0)
{
uint8_t v___x_1194_; 
v___x_1194_ = 1;
return v___x_1194_;
}
else
{
uint8_t v___x_1195_; 
v___x_1195_ = 0;
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object* v_x_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l_Lean_instExceptToTraceResultBool___lam__0(v_x_1196_);
lean_dec_ref(v_x_1196_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object* v_00_u03b5_1200_){
_start:
{
lean_object* v___f_1201_; 
v___f_1201_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___closed__0));
return v___f_1201_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___lam__0(lean_object* v_x_1202_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
uint8_t v___x_1203_; 
v___x_1203_ = 2;
return v___x_1203_;
}
else
{
lean_object* v_a_1204_; 
v_a_1204_ = lean_ctor_get(v_x_1202_, 0);
if (lean_obj_tag(v_a_1204_) == 0)
{
uint8_t v___x_1205_; 
v___x_1205_ = 1;
return v___x_1205_;
}
else
{
uint8_t v___x_1206_; 
v___x_1206_ = 0;
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object* v_x_1207_){
_start:
{
uint8_t v_res_1208_; lean_object* v_r_1209_; 
v_res_1208_ = l_Lean_instExceptToTraceResultOption___lam__0(v_x_1207_);
lean_dec_ref(v_x_1207_);
v_r_1209_ = lean_box(v_res_1208_);
return v_r_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object* v_00_u03b1_1211_, lean_object* v_00_u03b5_1212_){
_start:
{
lean_object* v___f_1213_; 
v___f_1213_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___closed__0));
return v___f_1213_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object* v_x_1214_){
_start:
{
if (lean_obj_tag(v_x_1214_) == 0)
{
uint8_t v___x_1215_; 
v___x_1215_ = 2;
return v___x_1215_;
}
else
{
uint8_t v___x_1216_; 
v___x_1216_ = 0;
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object* v_x_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l_Lean_instExceptToTraceResult___lam__0(v_x_1217_);
lean_dec_ref(v_x_1217_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object* v_00_u03b1_1221_, lean_object* v_00_u03b5_1222_){
_start:
{
lean_object* v___f_1223_; 
v___f_1223_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
return v___f_1223_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___redArg(lean_object* v_inst_1224_, lean_object* v_e_1225_){
_start:
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_apply_1(v_inst_1224_, v_e_1225_);
v___x_1227_ = lean_unbox(v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___redArg___boxed(lean_object* v_inst_1228_, lean_object* v_e_1229_){
_start:
{
uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_res_1230_ = l_Except_toTraceResult___redArg(v_inst_1228_, v_e_1229_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult(lean_object* v_00_u03b1_1232_, lean_object* v_00_u03b5_1233_, lean_object* v_inst_1234_, lean_object* v_e_1235_){
_start:
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = lean_apply_1(v_inst_1234_, v_e_1235_);
v___x_1237_ = lean_unbox(v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___boxed(lean_object* v_00_u03b1_1238_, lean_object* v_00_u03b5_1239_, lean_object* v_inst_1240_, lean_object* v_e_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Except_toTraceResult(v_00_u03b1_1238_, v_00_u03b5_1239_, v_inst_1240_, v_e_1241_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0));
v___x_1246_ = l_Lean_stringToMessageData(v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object* v_inst_1247_, lean_object* v_x_1248_){
_start:
{
lean_object* v_toApplicative_1249_; lean_object* v_toPure_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_toApplicative_1249_ = lean_ctor_get(v_inst_1247_, 0);
lean_inc_ref(v_toApplicative_1249_);
lean_dec_ref(v_inst_1247_);
v_toPure_1250_ = lean_ctor_get(v_toApplicative_1249_, 1);
lean_inc(v_toPure_1250_);
lean_dec_ref(v_toApplicative_1249_);
v___x_1251_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1);
v___x_1252_ = lean_apply_2(v_toPure_1250_, lean_box(0), v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(lean_object* v_inst_1253_, lean_object* v_x_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(v_inst_1253_, v_x_1254_);
lean_dec(v_x_1254_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object* v_oldTraces_1256_, lean_object* v_s_1257_){
_start:
{
uint64_t v_tid_1258_; lean_object* v_traces_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1267_; 
v_tid_1258_ = lean_ctor_get_uint64(v_s_1257_, sizeof(void*)*1);
v_traces_1259_ = lean_ctor_get(v_s_1257_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_s_1257_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1261_ = v_s_1257_;
v_isShared_1262_ = v_isSharedCheck_1267_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_traces_1259_);
lean_dec(v_s_1257_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1267_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1256_, v_traces_1259_);
lean_dec_ref(v_traces_1259_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1263_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
lean_ctor_set_uint64(v_reuseFailAlloc_1266_, sizeof(void*)*1, v_tid_1258_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object* v_always_1268_, lean_object* v_inst_1269_, lean_object* v_fst_1270_, lean_object* v_____r_1271_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1268_);
v___x_1273_ = l_MonadExcept_ofExcept___redArg(v_inst_1269_, v___x_1272_, v_fst_1270_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object* v_inst_1274_, lean_object* v___x_1275_, lean_object* v_fst_1276_, lean_object* v_____r_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_MonadExcept_ofExcept___redArg(v_inst_1274_, v___x_1275_, v_fst_1276_);
return v___x_1278_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0));
v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object* v_inst_1282_, lean_object* v_fst_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_oldTraces_1288_, lean_object* v_ref_1289_, lean_object* v_toBind_1290_, lean_object* v___f_1291_, lean_object* v_cls_1292_, uint8_t v_collapsed_1293_, lean_object* v_tag_1294_, uint8_t v___x_1295_, double v_fst_1296_, double v_snd_1297_, lean_object* v_m_1298_){
_start:
{
lean_object* v_result_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v_m_1305_; lean_object* v_data_1307_; lean_object* v___x_1310_; double v___x_1311_; lean_object* v_data_1312_; 
v_result_1299_ = lean_apply_1(v_inst_1282_, v_fst_1283_);
v___x_1300_ = lean_unbox(v_result_1299_);
v___x_1301_ = l_Lean_TraceResult_toEmoji(v___x_1300_);
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
v___x_1303_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
v___x_1304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v_m_1305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_m_1305_, 0, v___x_1304_);
lean_ctor_set(v_m_1305_, 1, v_m_1298_);
v___x_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1310_, 0, v_result_1299_);
v___x_1311_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_1294_);
lean_inc_ref(v___x_1310_);
lean_inc(v_cls_1292_);
v_data_1312_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1312_, 0, v_cls_1292_);
lean_ctor_set(v_data_1312_, 1, v___x_1310_);
lean_ctor_set(v_data_1312_, 2, v_tag_1294_);
lean_ctor_set_float(v_data_1312_, sizeof(void*)*3, v___x_1311_);
lean_ctor_set_float(v_data_1312_, sizeof(void*)*3 + 8, v___x_1311_);
lean_ctor_set_uint8(v_data_1312_, sizeof(void*)*3 + 16, v_collapsed_1293_);
if (v___x_1295_ == 0)
{
lean_dec_ref(v___x_1310_);
lean_dec_ref(v_tag_1294_);
lean_dec(v_cls_1292_);
v_data_1307_ = v_data_1312_;
goto v___jp_1306_;
}
else
{
lean_object* v_data_1313_; 
lean_dec_ref(v_data_1312_);
v_data_1313_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1313_, 0, v_cls_1292_);
lean_ctor_set(v_data_1313_, 1, v___x_1310_);
lean_ctor_set(v_data_1313_, 2, v_tag_1294_);
lean_ctor_set_float(v_data_1313_, sizeof(void*)*3, v_fst_1296_);
lean_ctor_set_float(v_data_1313_, sizeof(void*)*3 + 8, v_snd_1297_);
lean_ctor_set_uint8(v_data_1313_, sizeof(void*)*3 + 16, v_collapsed_1293_);
v_data_1307_ = v_data_1313_;
goto v___jp_1306_;
}
v___jp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_1284_, v_inst_1285_, v_inst_1286_, v_inst_1287_, v_oldTraces_1288_, v_data_1307_, v_ref_1289_, v_m_1305_);
v___x_1309_ = lean_apply_4(v_toBind_1290_, lean_box(0), lean_box(0), v___x_1308_, v___f_1291_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_1314_ = _args[0];
lean_object* v_fst_1315_ = _args[1];
lean_object* v_inst_1316_ = _args[2];
lean_object* v_inst_1317_ = _args[3];
lean_object* v_inst_1318_ = _args[4];
lean_object* v_inst_1319_ = _args[5];
lean_object* v_oldTraces_1320_ = _args[6];
lean_object* v_ref_1321_ = _args[7];
lean_object* v_toBind_1322_ = _args[8];
lean_object* v___f_1323_ = _args[9];
lean_object* v_cls_1324_ = _args[10];
lean_object* v_collapsed_1325_ = _args[11];
lean_object* v_tag_1326_ = _args[12];
lean_object* v___x_1327_ = _args[13];
lean_object* v_fst_1328_ = _args[14];
lean_object* v_snd_1329_ = _args[15];
lean_object* v_m_1330_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1331_; uint8_t v___x_676__boxed_1332_; double v_fst_677__boxed_1333_; double v_snd_678__boxed_1334_; lean_object* v_res_1335_; 
v_collapsed_boxed_1331_ = lean_unbox(v_collapsed_1325_);
v___x_676__boxed_1332_ = lean_unbox(v___x_1327_);
v_fst_677__boxed_1333_ = lean_unbox_float(v_fst_1328_);
lean_dec_ref(v_fst_1328_);
v_snd_678__boxed_1334_ = lean_unbox_float(v_snd_1329_);
lean_dec_ref(v_snd_1329_);
v_res_1335_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1314_, v_fst_1315_, v_inst_1316_, v_inst_1317_, v_inst_1318_, v_inst_1319_, v_oldTraces_1320_, v_ref_1321_, v_toBind_1322_, v___f_1323_, v_cls_1324_, v_collapsed_boxed_1331_, v_tag_1326_, v___x_676__boxed_1332_, v_fst_677__boxed_1333_, v_snd_678__boxed_1334_, v_m_1330_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(lean_object* v_always_1336_, lean_object* v_inst_1337_, lean_object* v_fst_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_oldTraces_1343_, lean_object* v_toBind_1344_, lean_object* v_cls_1345_, uint8_t v_collapsed_1346_, lean_object* v_tag_1347_, uint8_t v___x_1348_, double v_fst_1349_, double v_snd_1350_, lean_object* v_msg_1351_, lean_object* v___f_1352_, lean_object* v_ref_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v_tryCatch_1355_; lean_object* v___f_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___f_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_inc_ref(v_always_1336_);
v___x_1354_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1336_);
v_tryCatch_1355_ = lean_ctor_get(v_always_1336_, 1);
lean_inc(v_tryCatch_1355_);
lean_dec_ref(v_always_1336_);
lean_inc_ref_n(v_fst_1338_, 2);
lean_inc_ref(v_inst_1337_);
v___f_1356_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1356_, 0, v_inst_1337_);
lean_closure_set(v___f_1356_, 1, v___x_1354_);
lean_closure_set(v___f_1356_, 2, v_fst_1338_);
v___x_1357_ = lean_box(v_collapsed_1346_);
v___x_1358_ = lean_box(v___x_1348_);
v___x_1359_ = lean_box_float(v_fst_1349_);
v___x_1360_ = lean_box_float(v_snd_1350_);
lean_inc(v_toBind_1344_);
v___f_1361_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1361_, 0, v_inst_1339_);
lean_closure_set(v___f_1361_, 1, v_fst_1338_);
lean_closure_set(v___f_1361_, 2, v_inst_1337_);
lean_closure_set(v___f_1361_, 3, v_inst_1340_);
lean_closure_set(v___f_1361_, 4, v_inst_1341_);
lean_closure_set(v___f_1361_, 5, v_inst_1342_);
lean_closure_set(v___f_1361_, 6, v_oldTraces_1343_);
lean_closure_set(v___f_1361_, 7, v_ref_1353_);
lean_closure_set(v___f_1361_, 8, v_toBind_1344_);
lean_closure_set(v___f_1361_, 9, v___f_1356_);
lean_closure_set(v___f_1361_, 10, v_cls_1345_);
lean_closure_set(v___f_1361_, 11, v___x_1357_);
lean_closure_set(v___f_1361_, 12, v_tag_1347_);
lean_closure_set(v___f_1361_, 13, v___x_1358_);
lean_closure_set(v___f_1361_, 14, v___x_1359_);
lean_closure_set(v___f_1361_, 15, v___x_1360_);
v___x_1362_ = lean_apply_1(v_msg_1351_, v_fst_1338_);
v___x_1363_ = lean_apply_3(v_tryCatch_1355_, lean_box(0), v___x_1362_, v___f_1352_);
v___x_1364_ = lean_apply_4(v_toBind_1344_, lean_box(0), lean_box(0), v___x_1363_, v___f_1361_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_always_1365_ = _args[0];
lean_object* v_inst_1366_ = _args[1];
lean_object* v_fst_1367_ = _args[2];
lean_object* v_inst_1368_ = _args[3];
lean_object* v_inst_1369_ = _args[4];
lean_object* v_inst_1370_ = _args[5];
lean_object* v_inst_1371_ = _args[6];
lean_object* v_oldTraces_1372_ = _args[7];
lean_object* v_toBind_1373_ = _args[8];
lean_object* v_cls_1374_ = _args[9];
lean_object* v_collapsed_1375_ = _args[10];
lean_object* v_tag_1376_ = _args[11];
lean_object* v___x_1377_ = _args[12];
lean_object* v_fst_1378_ = _args[13];
lean_object* v_snd_1379_ = _args[14];
lean_object* v_msg_1380_ = _args[15];
lean_object* v___f_1381_ = _args[16];
lean_object* v_ref_1382_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_1383_; uint8_t v___x_728__boxed_1384_; double v_fst_729__boxed_1385_; double v_snd_730__boxed_1386_; lean_object* v_res_1387_; 
v_collapsed_boxed_1383_ = lean_unbox(v_collapsed_1375_);
v___x_728__boxed_1384_ = lean_unbox(v___x_1377_);
v_fst_729__boxed_1385_ = lean_unbox_float(v_fst_1378_);
lean_dec_ref(v_fst_1378_);
v_snd_730__boxed_1386_ = lean_unbox_float(v_snd_1379_);
lean_dec_ref(v_snd_1379_);
v_res_1387_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(v_always_1365_, v_inst_1366_, v_fst_1367_, v_inst_1368_, v_inst_1369_, v_inst_1370_, v_inst_1371_, v_oldTraces_1372_, v_toBind_1373_, v_cls_1374_, v_collapsed_boxed_1383_, v_tag_1376_, v___x_728__boxed_1384_, v_fst_729__boxed_1385_, v_snd_730__boxed_1386_, v_msg_1380_, v___f_1381_, v_ref_1382_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object* v_inst_1388_, lean_object* v_inst_1389_, lean_object* v_inst_1390_, lean_object* v_inst_1391_, lean_object* v_always_1392_, lean_object* v_inst_1393_, lean_object* v_cls_1394_, uint8_t v_collapsed_1395_, lean_object* v_tag_1396_, lean_object* v_opts_1397_, uint8_t v_clsEnabled_1398_, lean_object* v_oldTraces_1399_, lean_object* v_msg_1400_, lean_object* v_resStartStop_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v_snd_1403_; lean_object* v_fst_1404_; lean_object* v_fst_1405_; lean_object* v_snd_1406_; lean_object* v___f_1407_; lean_object* v___f_1408_; lean_object* v___f_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___y_1419_; double v___y_1425_; uint8_t v___x_1430_; 
v___x_1402_ = l_Lean_KVMap_instValueBool;
v_snd_1403_ = lean_ctor_get(v_resStartStop_1401_, 1);
lean_inc(v_snd_1403_);
v_fst_1404_ = lean_ctor_get(v_resStartStop_1401_, 0);
lean_inc_n(v_fst_1404_, 2);
lean_dec_ref(v_resStartStop_1401_);
v_fst_1405_ = lean_ctor_get(v_snd_1403_, 0);
lean_inc(v_fst_1405_);
v_snd_1406_ = lean_ctor_get(v_snd_1403_, 1);
lean_inc(v_snd_1406_);
lean_dec(v_snd_1403_);
lean_inc_ref_n(v_inst_1388_, 2);
v___f_1407_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1407_, 0, v_inst_1388_);
lean_inc_ref(v_oldTraces_1399_);
v___f_1408_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1408_, 0, v_oldTraces_1399_);
lean_inc_ref(v_always_1392_);
v___f_1409_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1409_, 0, v_always_1392_);
lean_closure_set(v___f_1409_, 1, v_inst_1388_);
lean_closure_set(v___f_1409_, 2, v_fst_1404_);
v___x_1410_ = l_Lean_trace_profiler;
v___x_1411_ = l_Lean_Option_get___redArg(v___x_1402_, v_opts_1397_, v___x_1410_);
v___x_1430_ = lean_unbox(v___x_1411_);
if (v___x_1430_ == 0)
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_unbox(v___x_1411_);
v___y_1419_ = v___x_1431_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1433_ = l_Lean_Option_get___redArg(v___x_1402_, v_opts_1397_, v___x_1432_);
v___x_1434_ = lean_unbox(v___x_1433_);
lean_dec(v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; double v___x_1438_; double v___x_1439_; double v___x_1440_; 
v___x_1435_ = l_Lean_KVMap_instValueNat;
v___x_1436_ = l_Lean_trace_profiler_threshold;
v___x_1437_ = l_Lean_Option_get___redArg(v___x_1435_, v_opts_1397_, v___x_1436_);
v___x_1438_ = lean_float_of_nat(v___x_1437_);
v___x_1439_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1440_ = lean_float_div(v___x_1438_, v___x_1439_);
v___y_1425_ = v___x_1440_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; double v___x_1444_; 
v___x_1441_ = l_Lean_KVMap_instValueNat;
v___x_1442_ = l_Lean_trace_profiler_threshold;
v___x_1443_ = l_Lean_Option_get___redArg(v___x_1441_, v_opts_1397_, v___x_1442_);
v___x_1444_ = lean_float_of_nat(v___x_1443_);
v___y_1425_ = v___x_1444_;
goto v___jp_1424_;
}
}
v___jp_1412_:
{
lean_object* v_toBind_1413_; lean_object* v_getRef_1414_; lean_object* v___x_1415_; lean_object* v___f_1416_; lean_object* v___x_1417_; 
v_toBind_1413_ = lean_ctor_get(v_inst_1388_, 1);
lean_inc_n(v_toBind_1413_, 2);
v_getRef_1414_ = lean_ctor_get(v_inst_1390_, 0);
lean_inc(v_getRef_1414_);
v___x_1415_ = lean_box(v_collapsed_1395_);
v___f_1416_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed), 18, 17);
lean_closure_set(v___f_1416_, 0, v_always_1392_);
lean_closure_set(v___f_1416_, 1, v_inst_1388_);
lean_closure_set(v___f_1416_, 2, v_fst_1404_);
lean_closure_set(v___f_1416_, 3, v_inst_1393_);
lean_closure_set(v___f_1416_, 4, v_inst_1389_);
lean_closure_set(v___f_1416_, 5, v_inst_1390_);
lean_closure_set(v___f_1416_, 6, v_inst_1391_);
lean_closure_set(v___f_1416_, 7, v_oldTraces_1399_);
lean_closure_set(v___f_1416_, 8, v_toBind_1413_);
lean_closure_set(v___f_1416_, 9, v_cls_1394_);
lean_closure_set(v___f_1416_, 10, v___x_1415_);
lean_closure_set(v___f_1416_, 11, v_tag_1396_);
lean_closure_set(v___f_1416_, 12, v___x_1411_);
lean_closure_set(v___f_1416_, 13, v_fst_1405_);
lean_closure_set(v___f_1416_, 14, v_snd_1406_);
lean_closure_set(v___f_1416_, 15, v_msg_1400_);
lean_closure_set(v___f_1416_, 16, v___f_1407_);
v___x_1417_ = lean_apply_4(v_toBind_1413_, lean_box(0), lean_box(0), v_getRef_1414_, v___f_1416_);
return v___x_1417_;
}
v___jp_1418_:
{
if (v_clsEnabled_1398_ == 0)
{
if (v___y_1419_ == 0)
{
lean_object* v_toBind_1420_; lean_object* v_modifyTraceState_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec(v___x_1411_);
lean_dec_ref(v___f_1407_);
lean_dec(v_snd_1406_);
lean_dec(v_fst_1405_);
lean_dec(v_fst_1404_);
lean_dec(v_msg_1400_);
lean_dec_ref(v_oldTraces_1399_);
lean_dec_ref(v_tag_1396_);
lean_dec(v_cls_1394_);
lean_dec_ref(v_inst_1393_);
lean_dec_ref(v_always_1392_);
lean_dec(v_inst_1391_);
lean_dec_ref(v_inst_1390_);
v_toBind_1420_ = lean_ctor_get(v_inst_1388_, 1);
lean_inc(v_toBind_1420_);
lean_dec_ref(v_inst_1388_);
v_modifyTraceState_1421_ = lean_ctor_get(v_inst_1389_, 0);
lean_inc(v_modifyTraceState_1421_);
lean_dec_ref(v_inst_1389_);
v___x_1422_ = lean_apply_1(v_modifyTraceState_1421_, v___f_1408_);
v___x_1423_ = lean_apply_4(v_toBind_1420_, lean_box(0), lean_box(0), v___x_1422_, v___f_1409_);
return v___x_1423_;
}
else
{
lean_dec_ref(v___f_1409_);
lean_dec_ref(v___f_1408_);
goto v___jp_1412_;
}
}
else
{
lean_dec_ref(v___f_1409_);
lean_dec_ref(v___f_1408_);
goto v___jp_1412_;
}
}
v___jp_1424_:
{
double v___x_1426_; double v___x_1427_; double v___x_1428_; uint8_t v___x_1429_; 
v___x_1426_ = lean_unbox_float(v_snd_1406_);
v___x_1427_ = lean_unbox_float(v_fst_1405_);
v___x_1428_ = lean_float_sub(v___x_1426_, v___x_1427_);
v___x_1429_ = lean_float_decLt(v___y_1425_, v___x_1428_);
v___y_1419_ = v___x_1429_;
goto v___jp_1418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object* v_inst_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_always_1449_, lean_object* v_inst_1450_, lean_object* v_cls_1451_, lean_object* v_collapsed_1452_, lean_object* v_tag_1453_, lean_object* v_opts_1454_, lean_object* v_clsEnabled_1455_, lean_object* v_oldTraces_1456_, lean_object* v_msg_1457_, lean_object* v_resStartStop_1458_){
_start:
{
uint8_t v_collapsed_boxed_1459_; uint8_t v_clsEnabled_boxed_1460_; lean_object* v_res_1461_; 
v_collapsed_boxed_1459_ = lean_unbox(v_collapsed_1452_);
v_clsEnabled_boxed_1460_ = lean_unbox(v_clsEnabled_1455_);
v_res_1461_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1445_, v_inst_1446_, v_inst_1447_, v_inst_1448_, v_always_1449_, v_inst_1450_, v_cls_1451_, v_collapsed_boxed_1459_, v_tag_1453_, v_opts_1454_, v_clsEnabled_boxed_1460_, v_oldTraces_1456_, v_msg_1457_, v_resStartStop_1458_);
lean_dec_ref(v_opts_1454_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object* v_00_u03b1_1462_, lean_object* v_m_1463_, lean_object* v_inst_1464_, lean_object* v_inst_1465_, lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_00_u03b5_1468_, lean_object* v_always_1469_, lean_object* v_inst_1470_, lean_object* v_cls_1471_, uint8_t v_collapsed_1472_, lean_object* v_tag_1473_, lean_object* v_opts_1474_, uint8_t v_clsEnabled_1475_, lean_object* v_oldTraces_1476_, lean_object* v_msg_1477_, lean_object* v_resStartStop_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1464_, v_inst_1465_, v_inst_1466_, v_inst_1467_, v_always_1469_, v_inst_1470_, v_cls_1471_, v_collapsed_1472_, v_tag_1473_, v_opts_1474_, v_clsEnabled_1475_, v_oldTraces_1476_, v_msg_1477_, v_resStartStop_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_1480_ = _args[0];
lean_object* v_m_1481_ = _args[1];
lean_object* v_inst_1482_ = _args[2];
lean_object* v_inst_1483_ = _args[3];
lean_object* v_inst_1484_ = _args[4];
lean_object* v_inst_1485_ = _args[5];
lean_object* v_00_u03b5_1486_ = _args[6];
lean_object* v_always_1487_ = _args[7];
lean_object* v_inst_1488_ = _args[8];
lean_object* v_cls_1489_ = _args[9];
lean_object* v_collapsed_1490_ = _args[10];
lean_object* v_tag_1491_ = _args[11];
lean_object* v_opts_1492_ = _args[12];
lean_object* v_clsEnabled_1493_ = _args[13];
lean_object* v_oldTraces_1494_ = _args[14];
lean_object* v_msg_1495_ = _args[15];
lean_object* v_resStartStop_1496_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1497_; uint8_t v_clsEnabled_boxed_1498_; lean_object* v_res_1499_; 
v_collapsed_boxed_1497_ = lean_unbox(v_collapsed_1490_);
v_clsEnabled_boxed_1498_ = lean_unbox(v_clsEnabled_1493_);
v_res_1499_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(v_00_u03b1_1480_, v_m_1481_, v_inst_1482_, v_inst_1483_, v_inst_1484_, v_inst_1485_, v_00_u03b5_1486_, v_always_1487_, v_inst_1488_, v_cls_1489_, v_collapsed_boxed_1497_, v_tag_1491_, v_opts_1492_, v_clsEnabled_boxed_1498_, v_oldTraces_1494_, v_msg_1495_, v_resStartStop_1496_);
lean_dec_ref(v_opts_1492_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_always_1504_, lean_object* v_inst_1505_, lean_object* v_cls_1506_, uint8_t v_collapsed_1507_, lean_object* v_tag_1508_, lean_object* v_opts_1509_, uint8_t v_clsEnabled_1510_, lean_object* v_oldTraces_1511_, lean_object* v_msg_1512_, lean_object* v_resStartStop_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1500_, v_inst_1501_, v_inst_1502_, v_inst_1503_, v_always_1504_, v_inst_1505_, v_cls_1506_, v_collapsed_1507_, v_tag_1508_, v_opts_1509_, v_clsEnabled_1510_, v_oldTraces_1511_, v_msg_1512_, v_resStartStop_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object* v_inst_1515_, lean_object* v_inst_1516_, lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_always_1519_, lean_object* v_inst_1520_, lean_object* v_cls_1521_, lean_object* v_collapsed_1522_, lean_object* v_tag_1523_, lean_object* v_opts_1524_, lean_object* v_clsEnabled_1525_, lean_object* v_oldTraces_1526_, lean_object* v_msg_1527_, lean_object* v_resStartStop_1528_){
_start:
{
uint8_t v_collapsed_boxed_1529_; uint8_t v_clsEnabled_boxed_1530_; lean_object* v_res_1531_; 
v_collapsed_boxed_1529_ = lean_unbox(v_collapsed_1522_);
v_clsEnabled_boxed_1530_ = lean_unbox(v_clsEnabled_1525_);
v_res_1531_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1515_, v_inst_1516_, v_inst_1517_, v_inst_1518_, v_always_1519_, v_inst_1520_, v_cls_1521_, v_collapsed_boxed_1529_, v_tag_1523_, v_opts_1524_, v_clsEnabled_boxed_1530_, v_oldTraces_1526_, v_msg_1527_, v_resStartStop_1528_);
lean_dec_ref(v_opts_1524_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object* v_toPure_1532_, lean_object* v_ex_1533_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_ex_1533_);
v___x_1535_ = lean_apply_2(v_toPure_1532_, lean_box(0), v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object* v_toPure_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_a_1537_);
v___x_1539_ = lean_apply_2(v_toPure_1536_, lean_box(0), v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object* v_start_1540_, lean_object* v_a_1541_, lean_object* v_toPure_1542_, lean_object* v_stop_1543_){
_start:
{
double v___x_1544_; double v___x_1545_; double v___x_1546_; double v___x_1547_; double v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1544_ = lean_float_of_nat(v_start_1540_);
v___x_1545_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1546_ = lean_float_div(v___x_1544_, v___x_1545_);
v___x_1547_ = lean_float_of_nat(v_stop_1543_);
v___x_1548_ = lean_float_div(v___x_1547_, v___x_1545_);
v___x_1549_ = lean_box_float(v___x_1546_);
v___x_1550_ = lean_box_float(v___x_1548_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_a_1541_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_apply_2(v_toPure_1542_, lean_box(0), v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object* v_start_1554_, lean_object* v_toPure_1555_, lean_object* v_toBind_1556_, lean_object* v___x_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v___f_1559_; lean_object* v___x_1560_; 
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1559_, 0, v_start_1554_);
lean_closure_set(v___f_1559_, 1, v_a_1558_);
lean_closure_set(v___f_1559_, 2, v_toPure_1555_);
v___x_1560_ = lean_apply_4(v_toBind_1556_, lean_box(0), lean_box(0), v___x_1557_, v___f_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object* v_toPure_1561_, lean_object* v_toBind_1562_, lean_object* v___x_1563_, lean_object* v___x_1564_, lean_object* v_start_1565_){
_start:
{
lean_object* v___f_1566_; lean_object* v___x_1567_; 
lean_inc(v_toBind_1562_);
v___f_1566_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1566_, 0, v_start_1565_);
lean_closure_set(v___f_1566_, 1, v_toPure_1561_);
lean_closure_set(v___f_1566_, 2, v_toBind_1562_);
lean_closure_set(v___f_1566_, 3, v___x_1563_);
v___x_1567_ = lean_apply_4(v_toBind_1562_, lean_box(0), lean_box(0), v___x_1564_, v___f_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object* v_start_1568_, lean_object* v_a_1569_, lean_object* v_toPure_1570_, lean_object* v_stop_1571_){
_start:
{
double v___x_1572_; double v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1572_ = lean_float_of_nat(v_start_1568_);
v___x_1573_ = lean_float_of_nat(v_stop_1571_);
v___x_1574_ = lean_box_float(v___x_1572_);
v___x_1575_ = lean_box_float(v___x_1573_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v_a_1569_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = lean_apply_2(v_toPure_1570_, lean_box(0), v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object* v_start_1579_, lean_object* v_toPure_1580_, lean_object* v_toBind_1581_, lean_object* v___x_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v___f_1584_; lean_object* v___x_1585_; 
v___f_1584_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__6), 4, 3);
lean_closure_set(v___f_1584_, 0, v_start_1579_);
lean_closure_set(v___f_1584_, 1, v_a_1583_);
lean_closure_set(v___f_1584_, 2, v_toPure_1580_);
v___x_1585_ = lean_apply_4(v_toBind_1581_, lean_box(0), lean_box(0), v___x_1582_, v___f_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object* v_toPure_1586_, lean_object* v_toBind_1587_, lean_object* v___x_1588_, lean_object* v___x_1589_, lean_object* v_start_1590_){
_start:
{
lean_object* v___f_1591_; lean_object* v___x_1592_; 
lean_inc(v_toBind_1587_);
v___f_1591_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1591_, 0, v_start_1590_);
lean_closure_set(v___f_1591_, 1, v_toPure_1586_);
lean_closure_set(v___f_1591_, 2, v_toBind_1587_);
lean_closure_set(v___f_1591_, 3, v___x_1588_);
v___x_1592_ = lean_apply_4(v_toBind_1587_, lean_box(0), lean_box(0), v___x_1589_, v___f_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object* v_always_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_cls_1599_, uint8_t v_collapsed_1600_, lean_object* v_tag_1601_, lean_object* v_opts_1602_, uint8_t v_clsEnabled_1603_, lean_object* v_msg_1604_, lean_object* v_toPure_1605_, lean_object* v_toBind_1606_, lean_object* v_k_1607_, lean_object* v_inst_1608_, lean_object* v_oldTraces_1609_){
_start:
{
lean_object* v_tryCatch_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___f_1613_; lean_object* v___f_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v_tryCatch_1610_ = lean_ctor_get(v_always_1593_, 1);
lean_inc(v_tryCatch_1610_);
v___x_1611_ = lean_box(v_collapsed_1600_);
v___x_1612_ = lean_box(v_clsEnabled_1603_);
lean_inc_ref(v_opts_1602_);
v___f_1613_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1613_, 0, v_inst_1594_);
lean_closure_set(v___f_1613_, 1, v_inst_1595_);
lean_closure_set(v___f_1613_, 2, v_inst_1596_);
lean_closure_set(v___f_1613_, 3, v_inst_1597_);
lean_closure_set(v___f_1613_, 4, v_always_1593_);
lean_closure_set(v___f_1613_, 5, v_inst_1598_);
lean_closure_set(v___f_1613_, 6, v_cls_1599_);
lean_closure_set(v___f_1613_, 7, v___x_1611_);
lean_closure_set(v___f_1613_, 8, v_tag_1601_);
lean_closure_set(v___f_1613_, 9, v_opts_1602_);
lean_closure_set(v___f_1613_, 10, v___x_1612_);
lean_closure_set(v___f_1613_, 11, v_oldTraces_1609_);
lean_closure_set(v___f_1613_, 12, v_msg_1604_);
lean_inc_n(v_toPure_1605_, 2);
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1614_, 0, v_toPure_1605_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1615_, 0, v_toPure_1605_);
lean_inc(v_toBind_1606_);
v___x_1616_ = lean_apply_4(v_toBind_1606_, lean_box(0), lean_box(0), v_k_1607_, v___f_1615_);
v___x_1617_ = lean_apply_3(v_tryCatch_1610_, lean_box(0), v___x_1616_, v___f_1614_);
v___x_1618_ = l_Lean_KVMap_instValueBool;
v___x_1619_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1620_ = l_Lean_Option_get___redArg(v___x_1618_, v_opts_1602_, v___x_1619_);
lean_dec_ref(v_opts_1602_);
v___x_1621_ = lean_unbox(v___x_1620_);
lean_dec(v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1622_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1623_ = lean_apply_2(v_inst_1608_, lean_box(0), v___x_1622_);
lean_inc(v___x_1623_);
lean_inc_n(v_toBind_1606_, 2);
v___f_1624_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1624_, 0, v_toPure_1605_);
lean_closure_set(v___f_1624_, 1, v_toBind_1606_);
lean_closure_set(v___f_1624_, 2, v___x_1623_);
lean_closure_set(v___f_1624_, 3, v___x_1617_);
v___x_1625_ = lean_apply_4(v_toBind_1606_, lean_box(0), lean_box(0), v___x_1623_, v___f_1624_);
v___x_1626_ = lean_apply_4(v_toBind_1606_, lean_box(0), lean_box(0), v___x_1625_, v___f_1613_);
return v___x_1626_;
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___f_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1627_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1628_ = lean_apply_2(v_inst_1608_, lean_box(0), v___x_1627_);
lean_inc(v___x_1628_);
lean_inc_n(v_toBind_1606_, 2);
v___f_1629_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_1629_, 0, v_toPure_1605_);
lean_closure_set(v___f_1629_, 1, v_toBind_1606_);
lean_closure_set(v___f_1629_, 2, v___x_1628_);
lean_closure_set(v___f_1629_, 3, v___x_1617_);
v___x_1630_ = lean_apply_4(v_toBind_1606_, lean_box(0), lean_box(0), v___x_1628_, v___f_1629_);
v___x_1631_ = lean_apply_4(v_toBind_1606_, lean_box(0), lean_box(0), v___x_1630_, v___f_1613_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_always_1632_ = _args[0];
lean_object* v_inst_1633_ = _args[1];
lean_object* v_inst_1634_ = _args[2];
lean_object* v_inst_1635_ = _args[3];
lean_object* v_inst_1636_ = _args[4];
lean_object* v_inst_1637_ = _args[5];
lean_object* v_cls_1638_ = _args[6];
lean_object* v_collapsed_1639_ = _args[7];
lean_object* v_tag_1640_ = _args[8];
lean_object* v_opts_1641_ = _args[9];
lean_object* v_clsEnabled_1642_ = _args[10];
lean_object* v_msg_1643_ = _args[11];
lean_object* v_toPure_1644_ = _args[12];
lean_object* v_toBind_1645_ = _args[13];
lean_object* v_k_1646_ = _args[14];
lean_object* v_inst_1647_ = _args[15];
lean_object* v_oldTraces_1648_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1649_; uint8_t v_clsEnabled_boxed_1650_; lean_object* v_res_1651_; 
v_collapsed_boxed_1649_ = lean_unbox(v_collapsed_1639_);
v_clsEnabled_boxed_1650_ = lean_unbox(v_clsEnabled_1642_);
v_res_1651_ = l_Lean_withTraceNode___redArg___lam__9(v_always_1632_, v_inst_1633_, v_inst_1634_, v_inst_1635_, v_inst_1636_, v_inst_1637_, v_cls_1638_, v_collapsed_boxed_1649_, v_tag_1640_, v_opts_1641_, v_clsEnabled_boxed_1650_, v_msg_1643_, v_toPure_1644_, v_toBind_1645_, v_k_1646_, v_inst_1647_, v_oldTraces_1648_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object* v_always_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_cls_1658_, uint8_t v_collapsed_1659_, lean_object* v_tag_1660_, lean_object* v_opts_1661_, lean_object* v_msg_1662_, lean_object* v_toPure_1663_, lean_object* v_toBind_1664_, lean_object* v_k_1665_, lean_object* v_inst_1666_, uint8_t v_clsEnabled_1667_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___f_1670_; 
v___x_1668_ = lean_box(v_collapsed_1659_);
v___x_1669_ = lean_box(v_clsEnabled_1667_);
lean_inc(v_k_1665_);
lean_inc(v_toBind_1664_);
lean_inc_ref(v_opts_1661_);
lean_inc_ref(v_inst_1654_);
lean_inc_ref(v_inst_1653_);
v___f_1670_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_1670_, 0, v_always_1652_);
lean_closure_set(v___f_1670_, 1, v_inst_1653_);
lean_closure_set(v___f_1670_, 2, v_inst_1654_);
lean_closure_set(v___f_1670_, 3, v_inst_1655_);
lean_closure_set(v___f_1670_, 4, v_inst_1656_);
lean_closure_set(v___f_1670_, 5, v_inst_1657_);
lean_closure_set(v___f_1670_, 6, v_cls_1658_);
lean_closure_set(v___f_1670_, 7, v___x_1668_);
lean_closure_set(v___f_1670_, 8, v_tag_1660_);
lean_closure_set(v___f_1670_, 9, v_opts_1661_);
lean_closure_set(v___f_1670_, 10, v___x_1669_);
lean_closure_set(v___f_1670_, 11, v_msg_1662_);
lean_closure_set(v___f_1670_, 12, v_toPure_1663_);
lean_closure_set(v___f_1670_, 13, v_toBind_1664_);
lean_closure_set(v___f_1670_, 14, v_k_1665_);
lean_closure_set(v___f_1670_, 15, v_inst_1666_);
if (v_clsEnabled_1667_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1674_ = l_Lean_KVMap_instValueBool;
v___x_1675_ = l_Lean_trace_profiler;
v___x_1676_ = l_Lean_Option_get___redArg(v___x_1674_, v_opts_1661_, v___x_1675_);
lean_dec_ref(v_opts_1661_);
v___x_1677_ = lean_unbox(v___x_1676_);
lean_dec(v___x_1676_);
if (v___x_1677_ == 0)
{
lean_dec_ref(v___f_1670_);
lean_dec(v_toBind_1664_);
lean_dec_ref(v_inst_1654_);
lean_dec_ref(v_inst_1653_);
return v_k_1665_;
}
else
{
lean_dec(v_k_1665_);
goto v___jp_1671_;
}
}
else
{
lean_dec(v_k_1665_);
lean_dec_ref(v_opts_1661_);
goto v___jp_1671_;
}
v___jp_1671_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1653_, v_inst_1654_);
v___x_1673_ = lean_apply_4(v_toBind_1664_, lean_box(0), lean_box(0), v___x_1672_, v___f_1670_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object* v_always_1678_, lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_cls_1684_, lean_object* v_collapsed_1685_, lean_object* v_tag_1686_, lean_object* v_opts_1687_, lean_object* v_msg_1688_, lean_object* v_toPure_1689_, lean_object* v_toBind_1690_, lean_object* v_k_1691_, lean_object* v_inst_1692_, lean_object* v_clsEnabled_1693_){
_start:
{
uint8_t v_collapsed_boxed_1694_; uint8_t v_clsEnabled_boxed_1695_; lean_object* v_res_1696_; 
v_collapsed_boxed_1694_ = lean_unbox(v_collapsed_1685_);
v_clsEnabled_boxed_1695_ = lean_unbox(v_clsEnabled_1693_);
v_res_1696_ = l_Lean_withTraceNode___redArg___lam__10(v_always_1678_, v_inst_1679_, v_inst_1680_, v_inst_1681_, v_inst_1682_, v_inst_1683_, v_cls_1684_, v_collapsed_boxed_1694_, v_tag_1686_, v_opts_1687_, v_msg_1688_, v_toPure_1689_, v_toBind_1690_, v_k_1691_, v_inst_1692_, v_clsEnabled_boxed_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object* v_k_1697_, lean_object* v_inst_1698_, lean_object* v_toApplicative_1699_, lean_object* v_always_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_cls_1705_, uint8_t v_collapsed_1706_, lean_object* v_tag_1707_, lean_object* v_msg_1708_, lean_object* v_toBind_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_opts_1712_){
_start:
{
uint8_t v_hasTrace_1713_; 
v_hasTrace_1713_ = lean_ctor_get_uint8(v_opts_1712_, sizeof(void*)*1);
if (v_hasTrace_1713_ == 0)
{
lean_dec_ref(v_opts_1712_);
lean_dec(v_inst_1711_);
lean_dec(v_inst_1710_);
lean_dec(v_toBind_1709_);
lean_dec(v_msg_1708_);
lean_dec_ref(v_tag_1707_);
lean_dec(v_cls_1705_);
lean_dec_ref(v_inst_1704_);
lean_dec(v_inst_1703_);
lean_dec_ref(v_inst_1702_);
lean_dec_ref(v_inst_1701_);
lean_dec_ref(v_always_1700_);
lean_dec_ref(v_toApplicative_1699_);
lean_dec_ref(v_inst_1698_);
return v_k_1697_;
}
else
{
lean_object* v_getInheritedTraceOptions_1714_; lean_object* v_toPure_1715_; lean_object* v___x_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_getInheritedTraceOptions_1714_ = lean_ctor_get(v_inst_1698_, 2);
lean_inc(v_getInheritedTraceOptions_1714_);
v_toPure_1715_ = lean_ctor_get(v_toApplicative_1699_, 1);
lean_inc_n(v_toPure_1715_, 2);
lean_dec_ref(v_toApplicative_1699_);
v___x_1716_ = lean_box(v_collapsed_1706_);
lean_inc_n(v_toBind_1709_, 3);
lean_inc(v_cls_1705_);
v___f_1717_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_1717_, 0, v_always_1700_);
lean_closure_set(v___f_1717_, 1, v_inst_1701_);
lean_closure_set(v___f_1717_, 2, v_inst_1698_);
lean_closure_set(v___f_1717_, 3, v_inst_1702_);
lean_closure_set(v___f_1717_, 4, v_inst_1703_);
lean_closure_set(v___f_1717_, 5, v_inst_1704_);
lean_closure_set(v___f_1717_, 6, v_cls_1705_);
lean_closure_set(v___f_1717_, 7, v___x_1716_);
lean_closure_set(v___f_1717_, 8, v_tag_1707_);
lean_closure_set(v___f_1717_, 9, v_opts_1712_);
lean_closure_set(v___f_1717_, 10, v_msg_1708_);
lean_closure_set(v___f_1717_, 11, v_toPure_1715_);
lean_closure_set(v___f_1717_, 12, v_toBind_1709_);
lean_closure_set(v___f_1717_, 13, v_k_1697_);
lean_closure_set(v___f_1717_, 14, v_inst_1710_);
v___f_1718_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1718_, 0, v_toPure_1715_);
lean_closure_set(v___f_1718_, 1, v_cls_1705_);
lean_closure_set(v___f_1718_, 2, v_toBind_1709_);
lean_closure_set(v___f_1718_, 3, v_inst_1711_);
v___x_1719_ = lean_apply_4(v_toBind_1709_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1714_, v___f_1718_);
v___x_1720_ = lean_apply_4(v_toBind_1709_, lean_box(0), lean_box(0), v___x_1719_, v___f_1717_);
return v___x_1720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13___boxed(lean_object* v_k_1721_, lean_object* v_inst_1722_, lean_object* v_toApplicative_1723_, lean_object* v_always_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_cls_1729_, lean_object* v_collapsed_1730_, lean_object* v_tag_1731_, lean_object* v_msg_1732_, lean_object* v_toBind_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_opts_1736_){
_start:
{
uint8_t v_collapsed_boxed_1737_; lean_object* v_res_1738_; 
v_collapsed_boxed_1737_ = lean_unbox(v_collapsed_1730_);
v_res_1738_ = l_Lean_withTraceNode___redArg___lam__13(v_k_1721_, v_inst_1722_, v_toApplicative_1723_, v_always_1724_, v_inst_1725_, v_inst_1726_, v_inst_1727_, v_inst_1728_, v_cls_1729_, v_collapsed_boxed_1737_, v_tag_1731_, v_msg_1732_, v_toBind_1733_, v_inst_1734_, v_inst_1735_, v_opts_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_always_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_cls_1747_, lean_object* v_msg_1748_, lean_object* v_k_1749_, uint8_t v_collapsed_1750_, lean_object* v_tag_1751_){
_start:
{
lean_object* v_toApplicative_1752_; lean_object* v_toBind_1753_; lean_object* v___x_1754_; lean_object* v___f_1755_; lean_object* v___x_1756_; 
v_toApplicative_1752_ = lean_ctor_get(v_inst_1739_, 0);
lean_inc_ref(v_toApplicative_1752_);
v_toBind_1753_ = lean_ctor_get(v_inst_1739_, 1);
lean_inc_n(v_toBind_1753_, 2);
v___x_1754_ = lean_box(v_collapsed_1750_);
lean_inc(v_inst_1743_);
v___f_1755_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1755_, 0, v_k_1749_);
lean_closure_set(v___f_1755_, 1, v_inst_1740_);
lean_closure_set(v___f_1755_, 2, v_toApplicative_1752_);
lean_closure_set(v___f_1755_, 3, v_always_1744_);
lean_closure_set(v___f_1755_, 4, v_inst_1739_);
lean_closure_set(v___f_1755_, 5, v_inst_1741_);
lean_closure_set(v___f_1755_, 6, v_inst_1742_);
lean_closure_set(v___f_1755_, 7, v_inst_1746_);
lean_closure_set(v___f_1755_, 8, v_cls_1747_);
lean_closure_set(v___f_1755_, 9, v___x_1754_);
lean_closure_set(v___f_1755_, 10, v_tag_1751_);
lean_closure_set(v___f_1755_, 11, v_msg_1748_);
lean_closure_set(v___f_1755_, 12, v_toBind_1753_);
lean_closure_set(v___f_1755_, 13, v_inst_1745_);
lean_closure_set(v___f_1755_, 14, v_inst_1743_);
v___x_1756_ = lean_apply_4(v_toBind_1753_, lean_box(0), lean_box(0), v_inst_1743_, v___f_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_inst_1761_, lean_object* v_always_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_cls_1765_, lean_object* v_msg_1766_, lean_object* v_k_1767_, lean_object* v_collapsed_1768_, lean_object* v_tag_1769_){
_start:
{
uint8_t v_collapsed_boxed_1770_; lean_object* v_res_1771_; 
v_collapsed_boxed_1770_ = lean_unbox(v_collapsed_1768_);
v_res_1771_ = l_Lean_withTraceNode___redArg(v_inst_1757_, v_inst_1758_, v_inst_1759_, v_inst_1760_, v_inst_1761_, v_always_1762_, v_inst_1763_, v_inst_1764_, v_cls_1765_, v_msg_1766_, v_k_1767_, v_collapsed_boxed_1770_, v_tag_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object* v_00_u03b1_1772_, lean_object* v_m_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_00_u03b5_1779_, lean_object* v_always_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_cls_1783_, lean_object* v_msg_1784_, lean_object* v_k_1785_, uint8_t v_collapsed_1786_, lean_object* v_tag_1787_){
_start:
{
lean_object* v_toApplicative_1788_; lean_object* v_toBind_1789_; lean_object* v___x_1790_; lean_object* v___f_1791_; lean_object* v___x_1792_; 
v_toApplicative_1788_ = lean_ctor_get(v_inst_1774_, 0);
lean_inc_ref(v_toApplicative_1788_);
v_toBind_1789_ = lean_ctor_get(v_inst_1774_, 1);
lean_inc_n(v_toBind_1789_, 2);
v___x_1790_ = lean_box(v_collapsed_1786_);
lean_inc(v_inst_1778_);
v___f_1791_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1791_, 0, v_k_1785_);
lean_closure_set(v___f_1791_, 1, v_inst_1775_);
lean_closure_set(v___f_1791_, 2, v_toApplicative_1788_);
lean_closure_set(v___f_1791_, 3, v_always_1780_);
lean_closure_set(v___f_1791_, 4, v_inst_1774_);
lean_closure_set(v___f_1791_, 5, v_inst_1776_);
lean_closure_set(v___f_1791_, 6, v_inst_1777_);
lean_closure_set(v___f_1791_, 7, v_inst_1782_);
lean_closure_set(v___f_1791_, 8, v_cls_1783_);
lean_closure_set(v___f_1791_, 9, v___x_1790_);
lean_closure_set(v___f_1791_, 10, v_tag_1787_);
lean_closure_set(v___f_1791_, 11, v_msg_1784_);
lean_closure_set(v___f_1791_, 12, v_toBind_1789_);
lean_closure_set(v___f_1791_, 13, v_inst_1781_);
lean_closure_set(v___f_1791_, 14, v_inst_1778_);
v___x_1792_ = lean_apply_4(v_toBind_1789_, lean_box(0), lean_box(0), v_inst_1778_, v___f_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object* v_00_u03b1_1793_, lean_object* v_m_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_, lean_object* v_inst_1799_, lean_object* v_00_u03b5_1800_, lean_object* v_always_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_cls_1804_, lean_object* v_msg_1805_, lean_object* v_k_1806_, lean_object* v_collapsed_1807_, lean_object* v_tag_1808_){
_start:
{
uint8_t v_collapsed_boxed_1809_; lean_object* v_res_1810_; 
v_collapsed_boxed_1809_ = lean_unbox(v_collapsed_1807_);
v_res_1810_ = l_Lean_withTraceNode(v_00_u03b1_1793_, v_m_1794_, v_inst_1795_, v_inst_1796_, v_inst_1797_, v_inst_1798_, v_inst_1799_, v_00_u03b5_1800_, v_always_1801_, v_inst_1802_, v_inst_1803_, v_cls_1804_, v_msg_1805_, v_k_1806_, v_collapsed_boxed_1809_, v_tag_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object* v_self_1811_){
_start:
{
lean_object* v_fst_1812_; 
v_fst_1812_ = lean_ctor_get(v_self_1811_, 0);
lean_inc(v_fst_1812_);
return v_fst_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object* v_self_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_1813_);
lean_dec_ref(v_self_1813_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object* v_toPure_1815_, lean_object* v_x_1816_){
_start:
{
if (lean_obj_tag(v_x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_a_1817_ = lean_ctor_get(v_x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref(v_x_1816_);
v___x_1818_ = l_Lean_Exception_toMessageData(v_a_1817_);
v___x_1819_ = lean_apply_2(v_toPure_1815_, lean_box(0), v___x_1818_);
return v___x_1819_;
}
else
{
lean_object* v_a_1820_; lean_object* v_snd_1821_; lean_object* v___x_1822_; 
v_a_1820_ = lean_ctor_get(v_x_1816_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v_x_1816_);
v_snd_1821_ = lean_ctor_get(v_a_1820_, 1);
lean_inc(v_snd_1821_);
lean_dec(v_a_1820_);
v___x_1822_ = lean_apply_2(v_toPure_1815_, lean_box(0), v_snd_1821_);
return v___x_1822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object* v_toPure_1823_, lean_object* v_ex_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_ex_1824_);
v___x_1826_ = lean_apply_2(v_toPure_1823_, lean_box(0), v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object* v_toPure_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1829_, 0, v_a_1828_);
v___x_1830_ = lean_apply_2(v_toPure_1827_, lean_box(0), v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v___f_1836_, lean_object* v_cls_1837_, uint8_t v_collapsed_1838_, lean_object* v_tag_1839_, lean_object* v_opts_1840_, uint8_t v_clsEnabled_1841_, lean_object* v_oldTraces_1842_, lean_object* v_msg_1843_, lean_object* v_resStartStop_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1831_, v_inst_1832_, v_inst_1833_, v_inst_1834_, v_inst_1835_, v___f_1836_, v_cls_1837_, v_collapsed_1838_, v_tag_1839_, v_opts_1840_, v_clsEnabled_1841_, v_oldTraces_1842_, v_msg_1843_, v_resStartStop_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3___boxed(lean_object* v_inst_1846_, lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v___f_1851_, lean_object* v_cls_1852_, lean_object* v_collapsed_1853_, lean_object* v_tag_1854_, lean_object* v_opts_1855_, lean_object* v_clsEnabled_1856_, lean_object* v_oldTraces_1857_, lean_object* v_msg_1858_, lean_object* v_resStartStop_1859_){
_start:
{
uint8_t v_collapsed_boxed_1860_; uint8_t v_clsEnabled_boxed_1861_; lean_object* v_res_1862_; 
v_collapsed_boxed_1860_ = lean_unbox(v_collapsed_1853_);
v_clsEnabled_boxed_1861_ = lean_unbox(v_clsEnabled_1856_);
v_res_1862_ = l_Lean_withTraceNode_x27___redArg___lam__3(v_inst_1846_, v_inst_1847_, v_inst_1848_, v_inst_1849_, v_inst_1850_, v___f_1851_, v_cls_1852_, v_collapsed_boxed_1860_, v_tag_1854_, v_opts_1855_, v_clsEnabled_boxed_1861_, v_oldTraces_1857_, v_msg_1858_, v_resStartStop_1859_);
lean_dec_ref(v_opts_1855_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object* v_start_1863_, lean_object* v_a_1864_, lean_object* v_toPure_1865_, lean_object* v_stop_1866_){
_start:
{
double v___x_1867_; double v___x_1868_; double v___x_1869_; double v___x_1870_; double v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1867_ = lean_float_of_nat(v_start_1863_);
v___x_1868_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1869_ = lean_float_div(v___x_1867_, v___x_1868_);
v___x_1870_ = lean_float_of_nat(v_stop_1866_);
v___x_1871_ = lean_float_div(v___x_1870_, v___x_1868_);
v___x_1872_ = lean_box_float(v___x_1869_);
v___x_1873_ = lean_box_float(v___x_1871_);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v_a_1864_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = lean_apply_2(v_toPure_1865_, lean_box(0), v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object* v_start_1877_, lean_object* v_toPure_1878_, lean_object* v_toBind_1879_, lean_object* v___x_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v___f_1882_; lean_object* v___x_1883_; 
v___f_1882_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__5), 4, 3);
lean_closure_set(v___f_1882_, 0, v_start_1877_);
lean_closure_set(v___f_1882_, 1, v_a_1881_);
lean_closure_set(v___f_1882_, 2, v_toPure_1878_);
v___x_1883_ = lean_apply_4(v_toBind_1879_, lean_box(0), lean_box(0), v___x_1880_, v___f_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object* v_toPure_1884_, lean_object* v_toBind_1885_, lean_object* v___x_1886_, lean_object* v___x_1887_, lean_object* v_start_1888_){
_start:
{
lean_object* v___f_1889_; lean_object* v___x_1890_; 
lean_inc(v_toBind_1885_);
v___f_1889_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__6), 5, 4);
lean_closure_set(v___f_1889_, 0, v_start_1888_);
lean_closure_set(v___f_1889_, 1, v_toPure_1884_);
lean_closure_set(v___f_1889_, 2, v_toBind_1885_);
lean_closure_set(v___f_1889_, 3, v___x_1886_);
v___x_1890_ = lean_apply_4(v_toBind_1885_, lean_box(0), lean_box(0), v___x_1887_, v___f_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object* v_start_1891_, lean_object* v_a_1892_, lean_object* v_toPure_1893_, lean_object* v_stop_1894_){
_start:
{
double v___x_1895_; double v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1895_ = lean_float_of_nat(v_start_1891_);
v___x_1896_ = lean_float_of_nat(v_stop_1894_);
v___x_1897_ = lean_box_float(v___x_1895_);
v___x_1898_ = lean_box_float(v___x_1896_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v_a_1892_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_apply_2(v_toPure_1893_, lean_box(0), v___x_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object* v_start_1902_, lean_object* v_toPure_1903_, lean_object* v_toBind_1904_, lean_object* v___x_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___f_1907_; lean_object* v___x_1908_; 
v___f_1907_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__8), 4, 3);
lean_closure_set(v___f_1907_, 0, v_start_1902_);
lean_closure_set(v___f_1907_, 1, v_a_1906_);
lean_closure_set(v___f_1907_, 2, v_toPure_1903_);
v___x_1908_ = lean_apply_4(v_toBind_1904_, lean_box(0), lean_box(0), v___x_1905_, v___f_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object* v_toPure_1909_, lean_object* v_toBind_1910_, lean_object* v___x_1911_, lean_object* v___x_1912_, lean_object* v_start_1913_){
_start:
{
lean_object* v___f_1914_; lean_object* v___x_1915_; 
lean_inc(v_toBind_1910_);
v___f_1914_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__9), 5, 4);
lean_closure_set(v___f_1914_, 0, v_start_1913_);
lean_closure_set(v___f_1914_, 1, v_toPure_1909_);
lean_closure_set(v___f_1914_, 2, v_toBind_1910_);
lean_closure_set(v___f_1914_, 3, v___x_1911_);
v___x_1915_ = lean_apply_4(v_toBind_1910_, lean_box(0), lean_box(0), v___x_1912_, v___f_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object* v_inst_1916_, lean_object* v_inst_1917_, lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_inst_1920_, lean_object* v___f_1921_, lean_object* v_cls_1922_, uint8_t v_collapsed_1923_, lean_object* v_tag_1924_, lean_object* v_opts_1925_, uint8_t v_clsEnabled_1926_, lean_object* v_msg_1927_, lean_object* v_toBind_1928_, lean_object* v_k_1929_, lean_object* v___f_1930_, lean_object* v___f_1931_, lean_object* v_inst_1932_, lean_object* v_toPure_1933_, lean_object* v_oldTraces_1934_){
_start:
{
lean_object* v_tryCatch_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___f_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v_tryCatch_1935_ = lean_ctor_get(v_inst_1916_, 1);
lean_inc(v_tryCatch_1935_);
v___x_1936_ = lean_box(v_collapsed_1923_);
v___x_1937_ = lean_box(v_clsEnabled_1926_);
lean_inc_ref(v_opts_1925_);
v___f_1938_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_1938_, 0, v_inst_1917_);
lean_closure_set(v___f_1938_, 1, v_inst_1918_);
lean_closure_set(v___f_1938_, 2, v_inst_1919_);
lean_closure_set(v___f_1938_, 3, v_inst_1920_);
lean_closure_set(v___f_1938_, 4, v_inst_1916_);
lean_closure_set(v___f_1938_, 5, v___f_1921_);
lean_closure_set(v___f_1938_, 6, v_cls_1922_);
lean_closure_set(v___f_1938_, 7, v___x_1936_);
lean_closure_set(v___f_1938_, 8, v_tag_1924_);
lean_closure_set(v___f_1938_, 9, v_opts_1925_);
lean_closure_set(v___f_1938_, 10, v___x_1937_);
lean_closure_set(v___f_1938_, 11, v_oldTraces_1934_);
lean_closure_set(v___f_1938_, 12, v_msg_1927_);
lean_inc(v_toBind_1928_);
v___x_1939_ = lean_apply_4(v_toBind_1928_, lean_box(0), lean_box(0), v_k_1929_, v___f_1930_);
v___x_1940_ = lean_apply_3(v_tryCatch_1935_, lean_box(0), v___x_1939_, v___f_1931_);
v___x_1941_ = l_Lean_KVMap_instValueBool;
v___x_1942_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1943_ = l_Lean_Option_get___redArg(v___x_1941_, v_opts_1925_, v___x_1942_);
lean_dec_ref(v_opts_1925_);
v___x_1944_ = lean_unbox(v___x_1943_);
lean_dec(v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___f_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1945_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1946_ = lean_apply_2(v_inst_1932_, lean_box(0), v___x_1945_);
lean_inc(v___x_1946_);
lean_inc_n(v_toBind_1928_, 2);
v___f_1947_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1947_, 0, v_toPure_1933_);
lean_closure_set(v___f_1947_, 1, v_toBind_1928_);
lean_closure_set(v___f_1947_, 2, v___x_1946_);
lean_closure_set(v___f_1947_, 3, v___x_1940_);
v___x_1948_ = lean_apply_4(v_toBind_1928_, lean_box(0), lean_box(0), v___x_1946_, v___f_1947_);
v___x_1949_ = lean_apply_4(v_toBind_1928_, lean_box(0), lean_box(0), v___x_1948_, v___f_1938_);
return v___x_1949_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___f_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1950_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1951_ = lean_apply_2(v_inst_1932_, lean_box(0), v___x_1950_);
lean_inc(v___x_1951_);
lean_inc_n(v_toBind_1928_, 2);
v___f_1952_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__10), 5, 4);
lean_closure_set(v___f_1952_, 0, v_toPure_1933_);
lean_closure_set(v___f_1952_, 1, v_toBind_1928_);
lean_closure_set(v___f_1952_, 2, v___x_1951_);
lean_closure_set(v___f_1952_, 3, v___x_1940_);
v___x_1953_ = lean_apply_4(v_toBind_1928_, lean_box(0), lean_box(0), v___x_1951_, v___f_1952_);
v___x_1954_ = lean_apply_4(v_toBind_1928_, lean_box(0), lean_box(0), v___x_1953_, v___f_1938_);
return v___x_1954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_1955_ = _args[0];
lean_object* v_inst_1956_ = _args[1];
lean_object* v_inst_1957_ = _args[2];
lean_object* v_inst_1958_ = _args[3];
lean_object* v_inst_1959_ = _args[4];
lean_object* v___f_1960_ = _args[5];
lean_object* v_cls_1961_ = _args[6];
lean_object* v_collapsed_1962_ = _args[7];
lean_object* v_tag_1963_ = _args[8];
lean_object* v_opts_1964_ = _args[9];
lean_object* v_clsEnabled_1965_ = _args[10];
lean_object* v_msg_1966_ = _args[11];
lean_object* v_toBind_1967_ = _args[12];
lean_object* v_k_1968_ = _args[13];
lean_object* v___f_1969_ = _args[14];
lean_object* v___f_1970_ = _args[15];
lean_object* v_inst_1971_ = _args[16];
lean_object* v_toPure_1972_ = _args[17];
lean_object* v_oldTraces_1973_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_1974_; uint8_t v_clsEnabled_boxed_1975_; lean_object* v_res_1976_; 
v_collapsed_boxed_1974_ = lean_unbox(v_collapsed_1962_);
v_clsEnabled_boxed_1975_ = lean_unbox(v_clsEnabled_1965_);
v_res_1976_ = l_Lean_withTraceNode_x27___redArg___lam__11(v_inst_1955_, v_inst_1956_, v_inst_1957_, v_inst_1958_, v_inst_1959_, v___f_1960_, v_cls_1961_, v_collapsed_boxed_1974_, v_tag_1963_, v_opts_1964_, v_clsEnabled_boxed_1975_, v_msg_1966_, v_toBind_1967_, v_k_1968_, v___f_1969_, v___f_1970_, v_inst_1971_, v_toPure_1972_, v_oldTraces_1973_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_inst_1981_, lean_object* v___f_1982_, lean_object* v_cls_1983_, uint8_t v_collapsed_1984_, lean_object* v_tag_1985_, lean_object* v_opts_1986_, lean_object* v_msg_1987_, lean_object* v_toBind_1988_, lean_object* v_k_1989_, lean_object* v___f_1990_, lean_object* v___f_1991_, lean_object* v_inst_1992_, lean_object* v_toPure_1993_, uint8_t v_clsEnabled_1994_){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___f_1997_; 
v___x_1995_ = lean_box(v_collapsed_1984_);
v___x_1996_ = lean_box(v_clsEnabled_1994_);
lean_inc(v_k_1989_);
lean_inc(v_toBind_1988_);
lean_inc_ref(v_opts_1986_);
lean_inc_ref(v_inst_1979_);
lean_inc_ref(v_inst_1978_);
v___f_1997_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__11___boxed), 19, 18);
lean_closure_set(v___f_1997_, 0, v_inst_1977_);
lean_closure_set(v___f_1997_, 1, v_inst_1978_);
lean_closure_set(v___f_1997_, 2, v_inst_1979_);
lean_closure_set(v___f_1997_, 3, v_inst_1980_);
lean_closure_set(v___f_1997_, 4, v_inst_1981_);
lean_closure_set(v___f_1997_, 5, v___f_1982_);
lean_closure_set(v___f_1997_, 6, v_cls_1983_);
lean_closure_set(v___f_1997_, 7, v___x_1995_);
lean_closure_set(v___f_1997_, 8, v_tag_1985_);
lean_closure_set(v___f_1997_, 9, v_opts_1986_);
lean_closure_set(v___f_1997_, 10, v___x_1996_);
lean_closure_set(v___f_1997_, 11, v_msg_1987_);
lean_closure_set(v___f_1997_, 12, v_toBind_1988_);
lean_closure_set(v___f_1997_, 13, v_k_1989_);
lean_closure_set(v___f_1997_, 14, v___f_1990_);
lean_closure_set(v___f_1997_, 15, v___f_1991_);
lean_closure_set(v___f_1997_, 16, v_inst_1992_);
lean_closure_set(v___f_1997_, 17, v_toPure_1993_);
if (v_clsEnabled_1994_ == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2001_ = l_Lean_KVMap_instValueBool;
v___x_2002_ = l_Lean_trace_profiler;
v___x_2003_ = l_Lean_Option_get___redArg(v___x_2001_, v_opts_1986_, v___x_2002_);
lean_dec_ref(v_opts_1986_);
v___x_2004_ = lean_unbox(v___x_2003_);
lean_dec(v___x_2003_);
if (v___x_2004_ == 0)
{
lean_dec_ref(v___f_1997_);
lean_dec(v_toBind_1988_);
lean_dec_ref(v_inst_1979_);
lean_dec_ref(v_inst_1978_);
return v_k_1989_;
}
else
{
lean_dec(v_k_1989_);
goto v___jp_1998_;
}
}
else
{
lean_dec(v_k_1989_);
lean_dec_ref(v_opts_1986_);
goto v___jp_1998_;
}
v___jp_1998_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1978_, v_inst_1979_);
v___x_2000_ = lean_apply_4(v_toBind_1988_, lean_box(0), lean_box(0), v___x_1999_, v___f_1997_);
return v___x_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_inst_2005_ = _args[0];
lean_object* v_inst_2006_ = _args[1];
lean_object* v_inst_2007_ = _args[2];
lean_object* v_inst_2008_ = _args[3];
lean_object* v_inst_2009_ = _args[4];
lean_object* v___f_2010_ = _args[5];
lean_object* v_cls_2011_ = _args[6];
lean_object* v_collapsed_2012_ = _args[7];
lean_object* v_tag_2013_ = _args[8];
lean_object* v_opts_2014_ = _args[9];
lean_object* v_msg_2015_ = _args[10];
lean_object* v_toBind_2016_ = _args[11];
lean_object* v_k_2017_ = _args[12];
lean_object* v___f_2018_ = _args[13];
lean_object* v___f_2019_ = _args[14];
lean_object* v_inst_2020_ = _args[15];
lean_object* v_toPure_2021_ = _args[16];
lean_object* v_clsEnabled_2022_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2023_; uint8_t v_clsEnabled_boxed_2024_; lean_object* v_res_2025_; 
v_collapsed_boxed_2023_ = lean_unbox(v_collapsed_2012_);
v_clsEnabled_boxed_2024_ = lean_unbox(v_clsEnabled_2022_);
v_res_2025_ = l_Lean_withTraceNode_x27___redArg___lam__12(v_inst_2005_, v_inst_2006_, v_inst_2007_, v_inst_2008_, v_inst_2009_, v___f_2010_, v_cls_2011_, v_collapsed_boxed_2023_, v_tag_2013_, v_opts_2014_, v_msg_2015_, v_toBind_2016_, v_k_2017_, v___f_2018_, v___f_2019_, v_inst_2020_, v_toPure_2021_, v_clsEnabled_boxed_2024_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object* v_k_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_inst_2031_, lean_object* v___f_2032_, lean_object* v_cls_2033_, uint8_t v_collapsed_2034_, lean_object* v_tag_2035_, lean_object* v_msg_2036_, lean_object* v_toBind_2037_, lean_object* v___f_2038_, lean_object* v___f_2039_, lean_object* v_inst_2040_, lean_object* v_toPure_2041_, lean_object* v___f_2042_, lean_object* v_opts_2043_){
_start:
{
uint8_t v_hasTrace_2044_; 
v_hasTrace_2044_ = lean_ctor_get_uint8(v_opts_2043_, sizeof(void*)*1);
if (v_hasTrace_2044_ == 0)
{
lean_dec_ref(v_opts_2043_);
lean_dec(v___f_2042_);
lean_dec(v_toPure_2041_);
lean_dec(v_inst_2040_);
lean_dec(v___f_2039_);
lean_dec(v___f_2038_);
lean_dec(v_toBind_2037_);
lean_dec(v_msg_2036_);
lean_dec_ref(v_tag_2035_);
lean_dec(v_cls_2033_);
lean_dec_ref(v___f_2032_);
lean_dec(v_inst_2031_);
lean_dec_ref(v_inst_2030_);
lean_dec_ref(v_inst_2029_);
lean_dec_ref(v_inst_2028_);
lean_dec_ref(v_inst_2027_);
return v_k_2026_;
}
else
{
lean_object* v_getInheritedTraceOptions_2045_; lean_object* v___x_2046_; lean_object* v___f_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_getInheritedTraceOptions_2045_ = lean_ctor_get(v_inst_2027_, 2);
lean_inc(v_getInheritedTraceOptions_2045_);
v___x_2046_ = lean_box(v_collapsed_2034_);
lean_inc_n(v_toBind_2037_, 2);
v___f_2047_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_2047_, 0, v_inst_2028_);
lean_closure_set(v___f_2047_, 1, v_inst_2029_);
lean_closure_set(v___f_2047_, 2, v_inst_2027_);
lean_closure_set(v___f_2047_, 3, v_inst_2030_);
lean_closure_set(v___f_2047_, 4, v_inst_2031_);
lean_closure_set(v___f_2047_, 5, v___f_2032_);
lean_closure_set(v___f_2047_, 6, v_cls_2033_);
lean_closure_set(v___f_2047_, 7, v___x_2046_);
lean_closure_set(v___f_2047_, 8, v_tag_2035_);
lean_closure_set(v___f_2047_, 9, v_opts_2043_);
lean_closure_set(v___f_2047_, 10, v_msg_2036_);
lean_closure_set(v___f_2047_, 11, v_toBind_2037_);
lean_closure_set(v___f_2047_, 12, v_k_2026_);
lean_closure_set(v___f_2047_, 13, v___f_2038_);
lean_closure_set(v___f_2047_, 14, v___f_2039_);
lean_closure_set(v___f_2047_, 15, v_inst_2040_);
lean_closure_set(v___f_2047_, 16, v_toPure_2041_);
v___x_2048_ = lean_apply_4(v_toBind_2037_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2045_, v___f_2042_);
v___x_2049_ = lean_apply_4(v_toBind_2037_, lean_box(0), lean_box(0), v___x_2048_, v___f_2047_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_k_2050_ = _args[0];
lean_object* v_inst_2051_ = _args[1];
lean_object* v_inst_2052_ = _args[2];
lean_object* v_inst_2053_ = _args[3];
lean_object* v_inst_2054_ = _args[4];
lean_object* v_inst_2055_ = _args[5];
lean_object* v___f_2056_ = _args[6];
lean_object* v_cls_2057_ = _args[7];
lean_object* v_collapsed_2058_ = _args[8];
lean_object* v_tag_2059_ = _args[9];
lean_object* v_msg_2060_ = _args[10];
lean_object* v_toBind_2061_ = _args[11];
lean_object* v___f_2062_ = _args[12];
lean_object* v___f_2063_ = _args[13];
lean_object* v_inst_2064_ = _args[14];
lean_object* v_toPure_2065_ = _args[15];
lean_object* v___f_2066_ = _args[16];
lean_object* v_opts_2067_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2068_; lean_object* v_res_2069_; 
v_collapsed_boxed_2068_ = lean_unbox(v_collapsed_2058_);
v_res_2069_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_k_2050_, v_inst_2051_, v_inst_2052_, v_inst_2053_, v_inst_2054_, v_inst_2055_, v___f_2056_, v_cls_2057_, v_collapsed_boxed_2068_, v_tag_2059_, v_msg_2060_, v_toBind_2061_, v___f_2062_, v___f_2063_, v_inst_2064_, v_toPure_2065_, v___f_2066_, v_opts_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_inst_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_cls_2078_, lean_object* v_k_2079_, uint8_t v_collapsed_2080_, lean_object* v_tag_2081_){
_start:
{
lean_object* v_toApplicative_2082_; lean_object* v_toFunctor_2083_; lean_object* v_toBind_2084_; lean_object* v_toPure_2085_; lean_object* v_map_2086_; lean_object* v___f_2087_; lean_object* v_msg_2088_; lean_object* v___f_2089_; lean_object* v___f_2090_; lean_object* v___f_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; lean_object* v___f_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_toApplicative_2082_ = lean_ctor_get(v_inst_2071_, 0);
v_toFunctor_2083_ = lean_ctor_get(v_toApplicative_2082_, 0);
v_toBind_2084_ = lean_ctor_get(v_inst_2071_, 1);
lean_inc_n(v_toBind_2084_, 3);
v_toPure_2085_ = lean_ctor_get(v_toApplicative_2082_, 1);
lean_inc_n(v_toPure_2085_, 5);
v_map_2086_ = lean_ctor_get(v_toFunctor_2083_, 0);
lean_inc(v_map_2086_);
v___f_2087_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2088_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2088_, 0, v_toPure_2085_);
lean_inc(v_inst_2075_);
lean_inc(v_cls_2078_);
v___f_2089_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2089_, 0, v_toPure_2085_);
lean_closure_set(v___f_2089_, 1, v_cls_2078_);
lean_closure_set(v___f_2089_, 2, v_toBind_2084_);
lean_closure_set(v___f_2089_, 3, v_inst_2075_);
v___f_2090_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2090_, 0, v_toPure_2085_);
v___f_2091_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2091_, 0, v_toPure_2085_);
v___f_2092_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2093_ = lean_box(v_collapsed_2080_);
v___f_2094_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2094_, 0, v_k_2079_);
lean_closure_set(v___f_2094_, 1, v_inst_2072_);
lean_closure_set(v___f_2094_, 2, v_inst_2076_);
lean_closure_set(v___f_2094_, 3, v_inst_2071_);
lean_closure_set(v___f_2094_, 4, v_inst_2073_);
lean_closure_set(v___f_2094_, 5, v_inst_2074_);
lean_closure_set(v___f_2094_, 6, v___f_2092_);
lean_closure_set(v___f_2094_, 7, v_cls_2078_);
lean_closure_set(v___f_2094_, 8, v___x_2093_);
lean_closure_set(v___f_2094_, 9, v_tag_2081_);
lean_closure_set(v___f_2094_, 10, v_msg_2088_);
lean_closure_set(v___f_2094_, 11, v_toBind_2084_);
lean_closure_set(v___f_2094_, 12, v___f_2091_);
lean_closure_set(v___f_2094_, 13, v___f_2090_);
lean_closure_set(v___f_2094_, 14, v_inst_2077_);
lean_closure_set(v___f_2094_, 15, v_toPure_2085_);
lean_closure_set(v___f_2094_, 16, v___f_2089_);
v___x_2095_ = lean_apply_4(v_toBind_2084_, lean_box(0), lean_box(0), v_inst_2075_, v___f_2094_);
v___x_2096_ = lean_apply_4(v_map_2086_, lean_box(0), lean_box(0), v___f_2087_, v___x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_cls_2104_, lean_object* v_k_2105_, lean_object* v_collapsed_2106_, lean_object* v_tag_2107_){
_start:
{
uint8_t v_collapsed_boxed_2108_; lean_object* v_res_2109_; 
v_collapsed_boxed_2108_ = lean_unbox(v_collapsed_2106_);
v_res_2109_ = l_Lean_withTraceNode_x27___redArg(v_inst_2097_, v_inst_2098_, v_inst_2099_, v_inst_2100_, v_inst_2101_, v_inst_2102_, v_inst_2103_, v_cls_2104_, v_k_2105_, v_collapsed_boxed_2108_, v_tag_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object* v_00_u03b1_2110_, lean_object* v_m_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_cls_2119_, lean_object* v_k_2120_, uint8_t v_collapsed_2121_, lean_object* v_tag_2122_){
_start:
{
lean_object* v_toApplicative_2123_; lean_object* v_toFunctor_2124_; lean_object* v_toBind_2125_; lean_object* v_toPure_2126_; lean_object* v_map_2127_; lean_object* v___f_2128_; lean_object* v_msg_2129_; lean_object* v___f_2130_; lean_object* v___f_2131_; lean_object* v___f_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; lean_object* v___f_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_toApplicative_2123_ = lean_ctor_get(v_inst_2112_, 0);
v_toFunctor_2124_ = lean_ctor_get(v_toApplicative_2123_, 0);
v_toBind_2125_ = lean_ctor_get(v_inst_2112_, 1);
lean_inc_n(v_toBind_2125_, 3);
v_toPure_2126_ = lean_ctor_get(v_toApplicative_2123_, 1);
lean_inc_n(v_toPure_2126_, 5);
v_map_2127_ = lean_ctor_get(v_toFunctor_2124_, 0);
lean_inc(v_map_2127_);
v___f_2128_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2129_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2129_, 0, v_toPure_2126_);
lean_inc(v_inst_2116_);
lean_inc(v_cls_2119_);
v___f_2130_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2130_, 0, v_toPure_2126_);
lean_closure_set(v___f_2130_, 1, v_cls_2119_);
lean_closure_set(v___f_2130_, 2, v_toBind_2125_);
lean_closure_set(v___f_2130_, 3, v_inst_2116_);
v___f_2131_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2131_, 0, v_toPure_2126_);
v___f_2132_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2132_, 0, v_toPure_2126_);
v___f_2133_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2134_ = lean_box(v_collapsed_2121_);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2135_, 0, v_k_2120_);
lean_closure_set(v___f_2135_, 1, v_inst_2113_);
lean_closure_set(v___f_2135_, 2, v_inst_2117_);
lean_closure_set(v___f_2135_, 3, v_inst_2112_);
lean_closure_set(v___f_2135_, 4, v_inst_2114_);
lean_closure_set(v___f_2135_, 5, v_inst_2115_);
lean_closure_set(v___f_2135_, 6, v___f_2133_);
lean_closure_set(v___f_2135_, 7, v_cls_2119_);
lean_closure_set(v___f_2135_, 8, v___x_2134_);
lean_closure_set(v___f_2135_, 9, v_tag_2122_);
lean_closure_set(v___f_2135_, 10, v_msg_2129_);
lean_closure_set(v___f_2135_, 11, v_toBind_2125_);
lean_closure_set(v___f_2135_, 12, v___f_2132_);
lean_closure_set(v___f_2135_, 13, v___f_2131_);
lean_closure_set(v___f_2135_, 14, v_inst_2118_);
lean_closure_set(v___f_2135_, 15, v_toPure_2126_);
lean_closure_set(v___f_2135_, 16, v___f_2130_);
v___x_2136_ = lean_apply_4(v_toBind_2125_, lean_box(0), lean_box(0), v_inst_2116_, v___f_2135_);
v___x_2137_ = lean_apply_4(v_map_2127_, lean_box(0), lean_box(0), v___f_2128_, v___x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object* v_00_u03b1_2138_, lean_object* v_m_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_inst_2143_, lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_, lean_object* v_cls_2147_, lean_object* v_k_2148_, lean_object* v_collapsed_2149_, lean_object* v_tag_2150_){
_start:
{
uint8_t v_collapsed_boxed_2151_; lean_object* v_res_2152_; 
v_collapsed_boxed_2151_ = lean_unbox(v_collapsed_2149_);
v_res_2152_ = l_Lean_withTraceNode_x27(v_00_u03b1_2138_, v_m_2139_, v_inst_2140_, v_inst_2141_, v_inst_2142_, v_inst_2143_, v_inst_2144_, v_inst_2145_, v_inst_2146_, v_cls_2147_, v_k_2148_, v_collapsed_boxed_2151_, v_tag_2150_);
return v_res_2152_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__4(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__3));
v___x_2162_ = l_Lean_mkAtom(v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__5(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__4, &l_Lean_registerTraceClass___auto__1___closed__4_once, _init_l_Lean_registerTraceClass___auto__1___closed__4);
v___x_2164_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2165_ = lean_array_push(v___x_2164_, v___x_2163_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__6(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2166_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__5, &l_Lean_registerTraceClass___auto__1___closed__5_once, _init_l_Lean_registerTraceClass___auto__1___closed__5);
v___x_2167_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__2));
v___x_2168_ = lean_box(2);
v___x_2169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___x_2167_);
lean_ctor_set(v___x_2169_, 2, v___x_2166_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__7(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__6, &l_Lean_registerTraceClass___auto__1___closed__6_once, _init_l_Lean_registerTraceClass___auto__1___closed__6);
v___x_2171_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_2172_ = lean_array_push(v___x_2171_, v___x_2170_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2173_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__7, &l_Lean_registerTraceClass___auto__1___closed__7_once, _init_l_Lean_registerTraceClass___auto__1___closed__7);
v___x_2174_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_2175_ = lean_box(2);
v___x_2176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v___x_2174_);
lean_ctor_set(v___x_2176_, 2, v___x_2173_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__8, &l_Lean_registerTraceClass___auto__1___closed__8_once, _init_l_Lean_registerTraceClass___auto__1___closed__8);
v___x_2178_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2179_ = lean_array_push(v___x_2178_, v___x_2177_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__9, &l_Lean_registerTraceClass___auto__1___closed__9_once, _init_l_Lean_registerTraceClass___auto__1___closed__9);
v___x_2181_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2182_ = lean_box(2);
v___x_2183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v___x_2181_);
lean_ctor_set(v___x_2183_, 2, v___x_2180_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__11(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__10, &l_Lean_registerTraceClass___auto__1___closed__10_once, _init_l_Lean_registerTraceClass___auto__1___closed__10);
v___x_2185_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2186_ = lean_array_push(v___x_2185_, v___x_2184_);
return v___x_2186_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2187_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__11, &l_Lean_registerTraceClass___auto__1___closed__11_once, _init_l_Lean_registerTraceClass___auto__1___closed__11);
v___x_2188_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_2189_ = lean_box(2);
v___x_2190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v___x_2188_);
lean_ctor_set(v___x_2190_, 2, v___x_2187_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__12, &l_Lean_registerTraceClass___auto__1___closed__12_once, _init_l_Lean_registerTraceClass___auto__1___closed__12);
v___x_2192_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2193_ = lean_array_push(v___x_2192_, v___x_2191_);
return v___x_2193_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2194_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__13, &l_Lean_registerTraceClass___auto__1___closed__13_once, _init_l_Lean_registerTraceClass___auto__1___closed__13);
v___x_2195_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_2196_ = lean_box(2);
v___x_2197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
lean_ctor_set(v___x_2197_, 1, v___x_2195_);
lean_ctor_set(v___x_2197_, 2, v___x_2194_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1(void){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__14, &l_Lean_registerTraceClass___auto__1___closed__14_once, _init_l_Lean_registerTraceClass___auto__1___closed__14);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
if (lean_obj_tag(v_x_2200_) == 0)
{
return v_x_2199_;
}
else
{
lean_object* v_key_2201_; lean_object* v_value_2202_; lean_object* v_tail_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2229_; 
v_key_2201_ = lean_ctor_get(v_x_2200_, 0);
v_value_2202_ = lean_ctor_get(v_x_2200_, 1);
v_tail_2203_ = lean_ctor_get(v_x_2200_, 2);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_x_2200_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2205_ = v_x_2200_;
v_isShared_2206_ = v_isSharedCheck_2229_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_tail_2203_);
lean_inc(v_value_2202_);
lean_inc(v_key_2201_);
lean_dec(v_x_2200_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2229_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; uint64_t v___y_2209_; 
v___x_2207_ = lean_array_get_size(v_x_2199_);
if (lean_obj_tag(v_key_2201_) == 0)
{
uint64_t v___x_2227_; 
v___x_2227_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2209_ = v___x_2227_;
goto v___jp_2208_;
}
else
{
uint64_t v_hash_2228_; 
v_hash_2228_ = lean_ctor_get_uint64(v_key_2201_, sizeof(void*)*2);
v___y_2209_ = v_hash_2228_;
goto v___jp_2208_;
}
v___jp_2208_:
{
uint64_t v___x_2210_; uint64_t v___x_2211_; uint64_t v_fold_2212_; uint64_t v___x_2213_; uint64_t v___x_2214_; uint64_t v___x_2215_; size_t v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2210_ = 32ULL;
v___x_2211_ = lean_uint64_shift_right(v___y_2209_, v___x_2210_);
v_fold_2212_ = lean_uint64_xor(v___y_2209_, v___x_2211_);
v___x_2213_ = 16ULL;
v___x_2214_ = lean_uint64_shift_right(v_fold_2212_, v___x_2213_);
v___x_2215_ = lean_uint64_xor(v_fold_2212_, v___x_2214_);
v___x_2216_ = lean_uint64_to_usize(v___x_2215_);
v___x_2217_ = lean_usize_of_nat(v___x_2207_);
v___x_2218_ = ((size_t)1ULL);
v___x_2219_ = lean_usize_sub(v___x_2217_, v___x_2218_);
v___x_2220_ = lean_usize_land(v___x_2216_, v___x_2219_);
v___x_2221_ = lean_array_uget_borrowed(v_x_2199_, v___x_2220_);
lean_inc(v___x_2221_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 2, v___x_2221_);
v___x_2223_ = v___x_2205_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_key_2201_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_value_2202_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_array_uset(v_x_2199_, v___x_2220_, v___x_2223_);
v_x_2199_ = v___x_2224_;
v_x_2200_ = v_tail_2203_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object* v_i_2230_, lean_object* v_source_2231_, lean_object* v_target_2232_){
_start:
{
lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2233_ = lean_array_get_size(v_source_2231_);
v___x_2234_ = lean_nat_dec_lt(v_i_2230_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_dec_ref(v_source_2231_);
lean_dec(v_i_2230_);
return v_target_2232_;
}
else
{
lean_object* v_es_2235_; lean_object* v___x_2236_; lean_object* v_source_2237_; lean_object* v_target_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_es_2235_ = lean_array_fget(v_source_2231_, v_i_2230_);
v___x_2236_ = lean_box(0);
v_source_2237_ = lean_array_fset(v_source_2231_, v_i_2230_, v___x_2236_);
v_target_2238_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_2232_, v_es_2235_);
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = lean_nat_add(v_i_2230_, v___x_2239_);
lean_dec(v_i_2230_);
v_i_2230_ = v___x_2240_;
v_source_2231_ = v_source_2237_;
v_target_2232_ = v_target_2238_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object* v_data_2242_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v_nbuckets_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2243_ = lean_array_get_size(v_data_2242_);
v___x_2244_ = lean_unsigned_to_nat(2u);
v_nbuckets_2245_ = lean_nat_mul(v___x_2243_, v___x_2244_);
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = lean_box(0);
v___x_2248_ = lean_mk_array(v_nbuckets_2245_, v___x_2247_);
v___x_2249_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_2246_, v_data_2242_, v___x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object* v_m_2250_, lean_object* v_a_2251_, lean_object* v_b_2252_){
_start:
{
lean_object* v_size_2253_; lean_object* v_buckets_2254_; lean_object* v___x_2255_; uint64_t v___y_2257_; 
v_size_2253_ = lean_ctor_get(v_m_2250_, 0);
v_buckets_2254_ = lean_ctor_get(v_m_2250_, 1);
v___x_2255_ = lean_array_get_size(v_buckets_2254_);
if (lean_obj_tag(v_a_2251_) == 0)
{
uint64_t v___x_2294_; 
v___x_2294_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2257_ = v___x_2294_;
goto v___jp_2256_;
}
else
{
uint64_t v_hash_2295_; 
v_hash_2295_ = lean_ctor_get_uint64(v_a_2251_, sizeof(void*)*2);
v___y_2257_ = v_hash_2295_;
goto v___jp_2256_;
}
v___jp_2256_:
{
uint64_t v___x_2258_; uint64_t v___x_2259_; uint64_t v_fold_2260_; uint64_t v___x_2261_; uint64_t v___x_2262_; uint64_t v___x_2263_; size_t v___x_2264_; size_t v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; size_t v___x_2268_; lean_object* v_bkt_2269_; uint8_t v___x_2270_; 
v___x_2258_ = 32ULL;
v___x_2259_ = lean_uint64_shift_right(v___y_2257_, v___x_2258_);
v_fold_2260_ = lean_uint64_xor(v___y_2257_, v___x_2259_);
v___x_2261_ = 16ULL;
v___x_2262_ = lean_uint64_shift_right(v_fold_2260_, v___x_2261_);
v___x_2263_ = lean_uint64_xor(v_fold_2260_, v___x_2262_);
v___x_2264_ = lean_uint64_to_usize(v___x_2263_);
v___x_2265_ = lean_usize_of_nat(v___x_2255_);
v___x_2266_ = ((size_t)1ULL);
v___x_2267_ = lean_usize_sub(v___x_2265_, v___x_2266_);
v___x_2268_ = lean_usize_land(v___x_2264_, v___x_2267_);
v_bkt_2269_ = lean_array_uget_borrowed(v_buckets_2254_, v___x_2268_);
v___x_2270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_2251_, v_bkt_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2291_; 
lean_inc_ref(v_buckets_2254_);
lean_inc(v_size_2253_);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_m_2250_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; lean_object* v_unused_2293_; 
v_unused_2292_ = lean_ctor_get(v_m_2250_, 1);
lean_dec(v_unused_2292_);
v_unused_2293_ = lean_ctor_get(v_m_2250_, 0);
lean_dec(v_unused_2293_);
v___x_2272_ = v_m_2250_;
v_isShared_2273_ = v_isSharedCheck_2291_;
goto v_resetjp_2271_;
}
else
{
lean_dec(v_m_2250_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2291_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v_size_x27_2275_; lean_object* v___x_2276_; lean_object* v_buckets_x27_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2274_ = lean_unsigned_to_nat(1u);
v_size_x27_2275_ = lean_nat_add(v_size_2253_, v___x_2274_);
lean_dec(v_size_2253_);
lean_inc(v_bkt_2269_);
v___x_2276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2276_, 0, v_a_2251_);
lean_ctor_set(v___x_2276_, 1, v_b_2252_);
lean_ctor_set(v___x_2276_, 2, v_bkt_2269_);
v_buckets_x27_2277_ = lean_array_uset(v_buckets_2254_, v___x_2268_, v___x_2276_);
v___x_2278_ = lean_unsigned_to_nat(4u);
v___x_2279_ = lean_nat_mul(v_size_x27_2275_, v___x_2278_);
v___x_2280_ = lean_unsigned_to_nat(3u);
v___x_2281_ = lean_nat_div(v___x_2279_, v___x_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_array_get_size(v_buckets_x27_2277_);
v___x_2283_ = lean_nat_dec_le(v___x_2281_, v___x_2282_);
lean_dec(v___x_2281_);
if (v___x_2283_ == 0)
{
lean_object* v_val_2284_; lean_object* v___x_2286_; 
v_val_2284_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_2277_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 1, v_val_2284_);
lean_ctor_set(v___x_2272_, 0, v_size_x27_2275_);
v___x_2286_ = v___x_2272_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_size_x27_2275_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_val_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
else
{
lean_object* v___x_2289_; 
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 1, v_buckets_x27_2277_);
lean_ctor_set(v___x_2272_, 0, v_size_x27_2275_);
v___x_2289_ = v___x_2272_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_size_x27_2275_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_buckets_x27_2277_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_dec(v_b_2252_);
lean_dec(v_a_2251_);
return v_m_2250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object* v_traceClassName_2299_, uint8_t v_inherited_2300_, lean_object* v_ref_2301_){
_start:
{
lean_object* v___x_2303_; lean_object* v_optionName_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2303_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v_optionName_2304_ = l_Lean_Name_append(v___x_2303_, v_traceClassName_2299_);
v___x_2305_ = ((lean_object*)(l_Lean_registerTraceClass___closed__0));
v___x_2306_ = ((lean_object*)(l_Lean_registerTraceClass___closed__1));
v___x_2307_ = lean_box(0);
lean_inc_n(v_optionName_2304_, 2);
v___x_2308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2308_, 0, v_optionName_2304_);
lean_ctor_set(v___x_2308_, 1, v_ref_2301_);
lean_ctor_set(v___x_2308_, 2, v___x_2305_);
lean_ctor_set(v___x_2308_, 3, v___x_2306_);
lean_ctor_set(v___x_2308_, 4, v___x_2307_);
v___x_2309_ = lean_register_option(v_optionName_2304_, v___x_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2325_; 
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v___x_2309_, 0);
lean_dec(v_unused_2326_);
v___x_2311_ = v___x_2309_;
v_isShared_2312_ = v_isSharedCheck_2325_;
goto v_resetjp_2310_;
}
else
{
lean_dec(v___x_2309_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2325_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
if (v_inherited_2300_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
lean_dec(v_optionName_2304_);
v___x_2313_ = lean_box(0);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v___x_2313_);
v___x_2315_ = v___x_2311_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2317_ = l_Lean_inheritedTraceOptions;
v___x_2318_ = lean_st_ref_take(v___x_2317_);
v___x_2319_ = lean_box(0);
v___x_2320_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2318_, v_optionName_2304_, v___x_2319_);
v___x_2321_ = lean_st_ref_set(v___x_2317_, v___x_2320_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v___x_2321_);
v___x_2323_ = v___x_2311_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
else
{
lean_dec(v_optionName_2304_);
return v___x_2309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object* v_traceClassName_2327_, lean_object* v_inherited_2328_, lean_object* v_ref_2329_, lean_object* v_a_2330_){
_start:
{
uint8_t v_inherited_boxed_2331_; lean_object* v_res_2332_; 
v_inherited_boxed_2331_ = lean_unbox(v_inherited_2328_);
v_res_2332_ = l_Lean_registerTraceClass(v_traceClassName_2327_, v_inherited_boxed_2331_, v_ref_2329_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(lean_object* v_00_u03b2_2333_, lean_object* v_m_2334_, lean_object* v_a_2335_, lean_object* v_b_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v_m_2334_, v_a_2335_, v_b_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object* v_00_u03b2_2338_, lean_object* v_data_2339_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_data_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2341_, lean_object* v_i_2342_, lean_object* v_source_2343_, lean_object* v_target_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_i_2342_, v_source_2343_, v_target_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2347_, v_x_2348_);
return v___x_2349_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_2360_ = l_String_toRawSubstring_x27(v___x_2359_);
return v___x_2360_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12));
v___x_2366_ = l_String_toRawSubstring_x27(v___x_2365_);
return v___x_2366_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18));
v___x_2373_ = l_String_toRawSubstring_x27(v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31(void){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Array_mkArray0(lean_box(0));
return v___x_2401_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40));
v___x_2428_ = l_String_toRawSubstring_x27(v___x_2427_);
return v___x_2428_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57));
v___x_2464_ = l_String_toRawSubstring_x27(v___x_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object* v_id_2486_, lean_object* v_s_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v_msg_2586_; lean_object* v_quotContext_2587_; lean_object* v_currMacroScope_2588_; lean_object* v_ref_2589_; lean_object* v___y_2590_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
lean_inc(v_s_2487_);
v___x_2636_ = l_Lean_Syntax_getKind(v_s_2487_);
v___x_2637_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49));
v___x_2638_ = lean_name_eq(v___x_2636_, v___x_2637_);
lean_dec(v___x_2636_);
if (v___x_2638_ == 0)
{
lean_object* v_quotContext_2639_; lean_object* v_currMacroScope_2640_; lean_object* v_ref_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_quotContext_2639_ = lean_ctor_get(v_a_2488_, 1);
v_currMacroScope_2640_ = lean_ctor_get(v_a_2488_, 2);
v_ref_2641_ = lean_ctor_get(v_a_2488_, 5);
v___x_2642_ = l_Lean_SourceInfo_fromRef(v_ref_2641_, v___x_2638_);
v___x_2643_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51));
v___x_2644_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52));
v___x_2645_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
lean_inc_n(v___x_2642_, 8);
v___x_2646_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2642_);
lean_ctor_set(v___x_2646_, 1, v___x_2645_);
v___x_2647_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2648_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2649_ = lean_box(0);
lean_inc_n(v_currMacroScope_2640_, 3);
lean_inc_n(v_quotContext_2639_, 3);
v___x_2650_ = l_Lean_addMacroScope(v_quotContext_2639_, v___x_2649_, v_currMacroScope_2640_);
v___x_2651_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55));
v___x_2652_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2642_);
lean_ctor_set(v___x_2652_, 1, v___x_2648_);
lean_ctor_set(v___x_2652_, 2, v___x_2650_);
lean_ctor_set(v___x_2652_, 3, v___x_2651_);
v___x_2653_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2647_, v___x_2652_);
v___x_2654_ = l_Lean_Syntax_node2(v___x_2642_, v___x_2644_, v___x_2646_, v___x_2653_);
v___x_2655_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56));
v___x_2656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2642_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2658_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58);
v___x_2659_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59));
v___x_2660_ = l_Lean_addMacroScope(v_quotContext_2639_, v___x_2659_, v_currMacroScope_2640_);
v___x_2661_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64));
v___x_2662_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2642_);
lean_ctor_set(v___x_2662_, 1, v___x_2658_);
lean_ctor_set(v___x_2662_, 2, v___x_2660_);
lean_ctor_set(v___x_2662_, 3, v___x_2661_);
v___x_2663_ = l_Lean_Syntax_node1(v___x_2642_, v___x_2657_, v___x_2662_);
v___x_2664_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2642_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = l_Lean_Syntax_node5(v___x_2642_, v___x_2643_, v___x_2654_, v_s_2487_, v___x_2656_, v___x_2663_, v___x_2665_);
v_msg_2586_ = v___x_2666_;
v_quotContext_2587_ = v_quotContext_2639_;
v_currMacroScope_2588_ = v_currMacroScope_2640_;
v_ref_2589_ = v_ref_2641_;
v___y_2590_ = v_a_2489_;
goto v___jp_2585_;
}
else
{
lean_object* v_quotContext_2667_; lean_object* v_currMacroScope_2668_; lean_object* v_ref_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v_quotContext_2667_ = lean_ctor_get(v_a_2488_, 1);
v_currMacroScope_2668_ = lean_ctor_get(v_a_2488_, 2);
v_ref_2669_ = lean_ctor_get(v_a_2488_, 5);
v___x_2670_ = 0;
v___x_2671_ = l_Lean_SourceInfo_fromRef(v_ref_2669_, v___x_2670_);
v___x_2672_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66));
v___x_2673_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67));
lean_inc(v___x_2671_);
v___x_2674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2671_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = l_Lean_Syntax_node2(v___x_2671_, v___x_2672_, v___x_2674_, v_s_2487_);
lean_inc(v_currMacroScope_2668_);
lean_inc(v_quotContext_2667_);
v_msg_2586_ = v___x_2675_;
v_quotContext_2587_ = v_quotContext_2667_;
v_currMacroScope_2588_ = v_currMacroScope_2668_;
v_ref_2589_ = v_ref_2669_;
v___y_2590_ = v_a_2489_;
goto v___jp_2585_;
}
v___jp_2490_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_inc_n(v___y_2506_, 8);
lean_inc(v___y_2495_);
lean_inc_n(v___y_2505_, 29);
v___x_2515_ = l_Lean_Syntax_node5(v___y_2505_, v___y_2495_, v___y_2510_, v___y_2506_, v___y_2506_, v___y_2501_, v___y_2514_);
lean_inc(v___y_2499_);
v___x_2516_ = l_Lean_Syntax_node1(v___y_2505_, v___y_2499_, v___x_2515_);
lean_inc(v___y_2509_);
v___x_2517_ = l_Lean_Syntax_node4(v___y_2505_, v___y_2509_, v___y_2494_, v___y_2506_, v___y_2498_, v___x_2516_);
lean_inc_n(v___y_2507_, 3);
v___x_2518_ = l_Lean_Syntax_node2(v___y_2505_, v___y_2507_, v___x_2517_, v___y_2506_);
v___x_2519_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0));
lean_inc_ref_n(v___y_2511_, 7);
lean_inc_ref_n(v___y_2513_, 7);
lean_inc_ref_n(v___y_2500_, 10);
v___x_2520_ = l_Lean_Name_mkStr4(v___y_2500_, v___y_2513_, v___y_2511_, v___x_2519_);
v___x_2521_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1));
v___x_2522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___y_2505_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2));
v___x_2524_ = l_Lean_Name_mkStr4(v___y_2500_, v___y_2513_, v___y_2511_, v___x_2523_);
v___x_2525_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3));
v___x_2526_ = l_Lean_Name_mkStr4(v___y_2500_, v___y_2513_, v___y_2511_, v___x_2525_);
v___x_2527_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4));
v___x_2528_ = l_Lean_Name_mkStr4(v___y_2500_, v___y_2513_, v___y_2511_, v___x_2527_);
v___x_2529_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
v___x_2530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___y_2505_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2532_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2533_ = lean_box(0);
lean_inc_n(v___y_2497_, 2);
lean_inc_n(v___y_2512_, 2);
v___x_2534_ = l_Lean_addMacroScope(v___y_2512_, v___x_2533_, v___y_2497_);
v___x_2535_ = l_Lean_Name_mkStr1(v___y_2500_);
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_inc_n(v___y_2493_, 2);
v___x_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v___y_2493_);
v___x_2538_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2538_, 0, v___y_2505_);
lean_ctor_set(v___x_2538_, 1, v___x_2532_);
lean_ctor_set(v___x_2538_, 2, v___x_2534_);
lean_ctor_set(v___x_2538_, 3, v___x_2537_);
v___x_2539_ = l_Lean_Syntax_node1(v___y_2505_, v___x_2531_, v___x_2538_);
v___x_2540_ = l_Lean_Syntax_node2(v___y_2505_, v___x_2528_, v___x_2530_, v___x_2539_);
v___x_2541_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9));
v___x_2542_ = l_Lean_Name_mkStr4(v___y_2500_, v___y_2513_, v___y_2511_, v___x_2541_);
v___x_2543_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10));
v___x_2544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___y_2505_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11));
v___x_2546_ = l_Lean_Name_mkStr4(v___y_2500_, v___y_2513_, v___y_2511_, v___x_2545_);
v___x_2547_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13);
v___x_2548_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14));
v___x_2549_ = l_Lean_Name_mkStr2(v___y_2500_, v___x_2548_);
lean_inc(v___x_2549_);
v___x_2550_ = l_Lean_addMacroScope(v___y_2512_, v___x_2549_, v___y_2497_);
v___x_2551_ = lean_box(0);
v___x_2552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2549_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
lean_ctor_set(v___x_2553_, 1, v___y_2493_);
v___x_2554_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2554_, 0, v___y_2505_);
lean_ctor_set(v___x_2554_, 1, v___x_2547_);
lean_ctor_set(v___x_2554_, 2, v___x_2550_);
lean_ctor_set(v___x_2554_, 3, v___x_2553_);
lean_inc(v___y_2492_);
lean_inc_n(v___y_2508_, 4);
v___x_2555_ = l_Lean_Syntax_node1(v___y_2505_, v___y_2508_, v___y_2492_);
lean_inc(v___x_2546_);
v___x_2556_ = l_Lean_Syntax_node2(v___y_2505_, v___x_2546_, v___x_2554_, v___x_2555_);
v___x_2557_ = l_Lean_Syntax_node2(v___y_2505_, v___x_2542_, v___x_2544_, v___x_2556_);
v___x_2558_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___y_2505_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = l_Lean_Syntax_node3(v___y_2505_, v___x_2526_, v___x_2540_, v___x_2557_, v___x_2559_);
v___x_2561_ = l_Lean_Syntax_node2(v___y_2505_, v___x_2524_, v___y_2506_, v___x_2560_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___y_2505_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17));
v___x_2565_ = l_Lean_Name_mkStr4(v___y_2500_, v___y_2513_, v___y_2511_, v___x_2564_);
v___x_2566_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19);
v___x_2567_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20));
v___x_2568_ = l_Lean_Name_mkStr2(v___y_2500_, v___x_2567_);
lean_inc(v___x_2568_);
v___x_2569_ = l_Lean_addMacroScope(v___y_2512_, v___x_2568_, v___y_2497_);
v___x_2570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2568_);
lean_ctor_set(v___x_2570_, 1, v___x_2551_);
v___x_2571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_ctor_set(v___x_2571_, 1, v___y_2493_);
v___x_2572_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2572_, 0, v___y_2505_);
lean_ctor_set(v___x_2572_, 1, v___x_2566_);
lean_ctor_set(v___x_2572_, 2, v___x_2569_);
lean_ctor_set(v___x_2572_, 3, v___x_2571_);
v___x_2573_ = l_Lean_Syntax_node2(v___y_2505_, v___y_2508_, v___y_2492_, v___y_2504_);
v___x_2574_ = l_Lean_Syntax_node2(v___y_2505_, v___x_2546_, v___x_2572_, v___x_2573_);
v___x_2575_ = l_Lean_Syntax_node1(v___y_2505_, v___x_2565_, v___x_2574_);
v___x_2576_ = l_Lean_Syntax_node2(v___y_2505_, v___y_2507_, v___x_2575_, v___y_2506_);
v___x_2577_ = l_Lean_Syntax_node1(v___y_2505_, v___y_2508_, v___x_2576_);
lean_inc_n(v___y_2503_, 2);
v___x_2578_ = l_Lean_Syntax_node1(v___y_2505_, v___y_2503_, v___x_2577_);
v___x_2579_ = l_Lean_Syntax_node6(v___y_2505_, v___x_2520_, v___x_2522_, v___x_2561_, v___x_2563_, v___x_2578_, v___y_2506_, v___y_2506_);
v___x_2580_ = l_Lean_Syntax_node2(v___y_2505_, v___y_2507_, v___x_2579_, v___y_2506_);
v___x_2581_ = l_Lean_Syntax_node2(v___y_2505_, v___y_2508_, v___x_2518_, v___x_2580_);
v___x_2582_ = l_Lean_Syntax_node1(v___y_2505_, v___y_2503_, v___x_2581_);
lean_inc(v___y_2496_);
v___x_2583_ = l_Lean_Syntax_node2(v___y_2505_, v___y_2496_, v___y_2491_, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___y_2502_);
return v___x_2584_;
}
v___jp_2585_:
{
uint8_t v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2591_ = 0;
v___x_2592_ = l_Lean_SourceInfo_fromRef(v_ref_2589_, v___x_2591_);
v___x_2593_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0));
v___x_2594_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1));
v___x_2595_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__0));
v___x_2596_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22));
v___x_2597_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23));
lean_inc_n(v___x_2592_, 7);
v___x_2598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2592_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25));
v___x_2600_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2601_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27));
v___x_2602_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2603_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
v___x_2604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2592_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31);
v___x_2606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2592_);
lean_ctor_set(v___x_2606_, 1, v___x_2600_);
lean_ctor_set(v___x_2606_, 2, v___x_2605_);
v___x_2607_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33));
lean_inc_ref(v___x_2606_);
v___x_2608_ = l_Lean_Syntax_node1(v___x_2592_, v___x_2607_, v___x_2606_);
v___x_2609_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35));
v___x_2610_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37));
v___x_2611_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39));
v___x_2612_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41);
v___x_2613_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42));
lean_inc(v_currMacroScope_2588_);
lean_inc(v_quotContext_2587_);
v___x_2614_ = l_Lean_addMacroScope(v_quotContext_2587_, v___x_2613_, v_currMacroScope_2588_);
v___x_2615_ = lean_box(0);
v___x_2616_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2592_);
lean_ctor_set(v___x_2616_, 1, v___x_2612_);
lean_ctor_set(v___x_2616_, 2, v___x_2614_);
lean_ctor_set(v___x_2616_, 3, v___x_2615_);
lean_inc_ref(v___x_2616_);
v___x_2617_ = l_Lean_Syntax_node1(v___x_2592_, v___x_2611_, v___x_2616_);
v___x_2618_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43));
v___x_2619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2592_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = l_Lean_Syntax_getId(v_id_2486_);
v___x_2621_ = lean_erase_macro_scopes(v___x_2620_);
lean_inc(v___x_2621_);
v___x_2622_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2615_, v___x_2621_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_quoteNameMk(v___x_2621_);
v___y_2491_ = v___x_2598_;
v___y_2492_ = v___x_2616_;
v___y_2493_ = v___x_2615_;
v___y_2494_ = v___x_2604_;
v___y_2495_ = v___x_2610_;
v___y_2496_ = v___x_2596_;
v___y_2497_ = v_currMacroScope_2588_;
v___y_2498_ = v___x_2608_;
v___y_2499_ = v___x_2609_;
v___y_2500_ = v___x_2593_;
v___y_2501_ = v___x_2619_;
v___y_2502_ = v___y_2590_;
v___y_2503_ = v___x_2599_;
v___y_2504_ = v_msg_2586_;
v___y_2505_ = v___x_2592_;
v___y_2506_ = v___x_2606_;
v___y_2507_ = v___x_2601_;
v___y_2508_ = v___x_2600_;
v___y_2509_ = v___x_2602_;
v___y_2510_ = v___x_2617_;
v___y_2511_ = v___x_2595_;
v___y_2512_ = v_quotContext_2587_;
v___y_2513_ = v___x_2594_;
v___y_2514_ = v___x_2623_;
goto v___jp_2490_;
}
else
{
lean_object* v_val_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec(v___x_2621_);
v_val_2624_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_val_2624_);
lean_dec_ref(v___x_2622_);
v___x_2625_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45));
v___x_2626_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46));
v___x_2627_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47));
v___x_2628_ = lean_string_intercalate(v___x_2627_, v_val_2624_);
v___x_2629_ = lean_string_append(v___x_2626_, v___x_2628_);
lean_dec_ref(v___x_2628_);
v___x_2630_ = lean_box(2);
v___x_2631_ = l_Lean_Syntax_mkNameLit(v___x_2629_, v___x_2630_);
v___x_2632_ = lean_unsigned_to_nat(1u);
v___x_2633_ = lean_mk_empty_array_with_capacity(v___x_2632_);
v___x_2634_ = lean_array_push(v___x_2633_, v___x_2631_);
v___x_2635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2630_);
lean_ctor_set(v___x_2635_, 1, v___x_2625_);
lean_ctor_set(v___x_2635_, 2, v___x_2634_);
v___y_2491_ = v___x_2598_;
v___y_2492_ = v___x_2616_;
v___y_2493_ = v___x_2615_;
v___y_2494_ = v___x_2604_;
v___y_2495_ = v___x_2610_;
v___y_2496_ = v___x_2596_;
v___y_2497_ = v_currMacroScope_2588_;
v___y_2498_ = v___x_2608_;
v___y_2499_ = v___x_2609_;
v___y_2500_ = v___x_2593_;
v___y_2501_ = v___x_2619_;
v___y_2502_ = v___y_2590_;
v___y_2503_ = v___x_2599_;
v___y_2504_ = v_msg_2586_;
v___y_2505_ = v___x_2592_;
v___y_2506_ = v___x_2606_;
v___y_2507_ = v___x_2601_;
v___y_2508_ = v___x_2600_;
v___y_2509_ = v___x_2602_;
v___y_2510_ = v___x_2617_;
v___y_2511_ = v___x_2595_;
v___y_2512_ = v_quotContext_2587_;
v___y_2513_ = v___x_2594_;
v___y_2514_ = v___x_2635_;
goto v___jp_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object* v_id_2676_, lean_object* v_s_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v_id_2676_, v_s_2677_, v_a_2678_, v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_id_2676_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object* v_x_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2738_ = ((lean_object*)(l_Lean_doElemTrace_x5b___x5d_____00__closed__1));
lean_inc(v_x_2735_);
v___x_2739_ = l_Lean_Syntax_isOfKind(v_x_2735_, v___x_2738_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_dec(v_x_2735_);
v___x_2740_ = lean_box(1);
v___x_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
lean_ctor_set(v___x_2741_, 1, v_a_2737_);
return v___x_2741_;
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v_a_2747_; lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
v___x_2742_ = lean_unsigned_to_nat(1u);
v___x_2743_ = l_Lean_Syntax_getArg(v_x_2735_, v___x_2742_);
v___x_2744_ = lean_unsigned_to_nat(3u);
v___x_2745_ = l_Lean_Syntax_getArg(v_x_2735_, v___x_2744_);
lean_dec(v_x_2735_);
v___x_2746_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v___x_2743_, v___x_2745_, v_a_2736_, v_a_2737_);
lean_dec(v___x_2743_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_a_2748_ = lean_ctor_get(v___x_2746_, 1);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2746_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2747_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object* v_x_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(v_x_2756_, v_a_2757_, v_a_2758_);
lean_dec_ref(v_a_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object* v_inst_2760_, lean_object* v_inst_2761_, lean_object* v_inst_2762_, lean_object* v_inst_2763_, lean_object* v_always_2764_, lean_object* v_inst_2765_, lean_object* v_cls_2766_, uint8_t v_collapsed_2767_, lean_object* v_tag_2768_, lean_object* v_opts_2769_, uint8_t v_clsEnabled_2770_, lean_object* v_oldTraces_2771_, lean_object* v_ref_2772_, lean_object* v_msg_2773_, lean_object* v_resStartStop_2774_){
_start:
{
lean_object* v___x_2775_; lean_object* v_snd_2776_; lean_object* v_fst_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2843_; 
v___x_2775_ = l_Lean_KVMap_instValueBool;
v_snd_2776_ = lean_ctor_get(v_resStartStop_2774_, 1);
v_fst_2777_ = lean_ctor_get(v_resStartStop_2774_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_resStartStop_2774_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2779_ = v_resStartStop_2774_;
v_isShared_2780_ = v_isSharedCheck_2843_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_snd_2776_);
lean_inc(v_fst_2777_);
lean_dec(v_resStartStop_2774_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2843_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_fst_2781_; lean_object* v_snd_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2842_; 
v_fst_2781_ = lean_ctor_get(v_snd_2776_, 0);
v_snd_2782_ = lean_ctor_get(v_snd_2776_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_snd_2776_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2784_ = v_snd_2776_;
v_isShared_2785_ = v_isSharedCheck_2842_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_snd_2782_);
lean_inc(v_fst_2781_);
lean_dec(v_snd_2776_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2842_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___f_2786_; lean_object* v___f_2787_; lean_object* v___y_2789_; lean_object* v_data_2790_; lean_object* v___x_2794_; lean_object* v___x_2795_; uint8_t v___y_2816_; double v___y_2822_; uint8_t v___x_2827_; 
lean_inc_ref(v_oldTraces_2771_);
v___f_2786_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2786_, 0, v_oldTraces_2771_);
lean_inc(v_fst_2777_);
lean_inc_ref(v_inst_2760_);
v___f_2787_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2787_, 0, v_always_2764_);
lean_closure_set(v___f_2787_, 1, v_inst_2760_);
lean_closure_set(v___f_2787_, 2, v_fst_2777_);
v___x_2794_ = l_Lean_trace_profiler;
v___x_2795_ = l_Lean_Option_get___redArg(v___x_2775_, v_opts_2769_, v___x_2794_);
v___x_2827_ = lean_unbox(v___x_2795_);
if (v___x_2827_ == 0)
{
uint8_t v___x_2828_; 
v___x_2828_ = lean_unbox(v___x_2795_);
v___y_2816_ = v___x_2828_;
goto v___jp_2815_;
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2829_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2830_ = l_Lean_Option_get___redArg(v___x_2775_, v_opts_2769_, v___x_2829_);
v___x_2831_ = lean_unbox(v___x_2830_);
lean_dec(v___x_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; double v___x_2835_; double v___x_2836_; double v___x_2837_; 
v___x_2832_ = l_Lean_KVMap_instValueNat;
v___x_2833_ = l_Lean_trace_profiler_threshold;
v___x_2834_ = l_Lean_Option_get___redArg(v___x_2832_, v_opts_2769_, v___x_2833_);
v___x_2835_ = lean_float_of_nat(v___x_2834_);
v___x_2836_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_2837_ = lean_float_div(v___x_2835_, v___x_2836_);
v___y_2822_ = v___x_2837_;
goto v___jp_2821_;
}
else
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; double v___x_2841_; 
v___x_2838_ = l_Lean_KVMap_instValueNat;
v___x_2839_ = l_Lean_trace_profiler_threshold;
v___x_2840_ = l_Lean_Option_get___redArg(v___x_2838_, v_opts_2769_, v___x_2839_);
v___x_2841_ = lean_float_of_nat(v___x_2840_);
v___y_2822_ = v___x_2841_;
goto v___jp_2821_;
}
}
v___jp_2788_:
{
lean_object* v_toBind_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_toBind_2791_ = lean_ctor_get(v_inst_2760_, 1);
lean_inc(v_toBind_2791_);
v___x_2792_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_2760_, v_inst_2761_, v_inst_2762_, v_inst_2763_, v_oldTraces_2771_, v_data_2790_, v_ref_2772_, v___y_2789_);
v___x_2793_ = lean_apply_4(v_toBind_2791_, lean_box(0), lean_box(0), v___x_2792_, v___f_2787_);
return v___x_2793_;
}
v___jp_2796_:
{
lean_object* v_result_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2803_; 
v_result_2797_ = lean_apply_1(v_inst_2765_, v_fst_2777_);
v___x_2798_ = lean_unbox(v_result_2797_);
v___x_2799_ = l_Lean_TraceResult_toEmoji(v___x_2798_);
v___x_2800_ = l_Lean_stringToMessageData(v___x_2799_);
v___x_2801_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
if (v_isShared_2785_ == 0)
{
lean_ctor_set_tag(v___x_2784_, 7);
lean_ctor_set(v___x_2784_, 1, v___x_2801_);
lean_ctor_set(v___x_2784_, 0, v___x_2800_);
v___x_2803_ = v___x_2784_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v_msg_2805_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set_tag(v___x_2779_, 7);
lean_ctor_set(v___x_2779_, 1, v_msg_2773_);
lean_ctor_set(v___x_2779_, 0, v___x_2803_);
v_msg_2805_ = v___x_2779_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_msg_2773_);
v_msg_2805_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
lean_object* v___x_2806_; double v___x_2807_; lean_object* v_data_2808_; uint8_t v___x_2809_; 
v___x_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2806_, 0, v_result_2797_);
v___x_2807_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_2768_);
lean_inc_ref(v___x_2806_);
lean_inc(v_cls_2766_);
v_data_2808_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2808_, 0, v_cls_2766_);
lean_ctor_set(v_data_2808_, 1, v___x_2806_);
lean_ctor_set(v_data_2808_, 2, v_tag_2768_);
lean_ctor_set_float(v_data_2808_, sizeof(void*)*3, v___x_2807_);
lean_ctor_set_float(v_data_2808_, sizeof(void*)*3 + 8, v___x_2807_);
lean_ctor_set_uint8(v_data_2808_, sizeof(void*)*3 + 16, v_collapsed_2767_);
v___x_2809_ = lean_unbox(v___x_2795_);
lean_dec(v___x_2795_);
if (v___x_2809_ == 0)
{
lean_dec_ref(v___x_2806_);
lean_dec(v_snd_2782_);
lean_dec(v_fst_2781_);
lean_dec_ref(v_tag_2768_);
lean_dec(v_cls_2766_);
v___y_2789_ = v_msg_2805_;
v_data_2790_ = v_data_2808_;
goto v___jp_2788_;
}
else
{
lean_object* v_data_2810_; double v___x_2811_; double v___x_2812_; 
lean_dec_ref(v_data_2808_);
v_data_2810_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2810_, 0, v_cls_2766_);
lean_ctor_set(v_data_2810_, 1, v___x_2806_);
lean_ctor_set(v_data_2810_, 2, v_tag_2768_);
v___x_2811_ = lean_unbox_float(v_fst_2781_);
lean_dec(v_fst_2781_);
lean_ctor_set_float(v_data_2810_, sizeof(void*)*3, v___x_2811_);
v___x_2812_ = lean_unbox_float(v_snd_2782_);
lean_dec(v_snd_2782_);
lean_ctor_set_float(v_data_2810_, sizeof(void*)*3 + 8, v___x_2812_);
lean_ctor_set_uint8(v_data_2810_, sizeof(void*)*3 + 16, v_collapsed_2767_);
v___y_2789_ = v_msg_2805_;
v_data_2790_ = v_data_2810_;
goto v___jp_2788_;
}
}
}
}
v___jp_2815_:
{
if (v_clsEnabled_2770_ == 0)
{
if (v___y_2816_ == 0)
{
lean_object* v_toBind_2817_; lean_object* v_modifyTraceState_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_dec(v___x_2795_);
lean_del_object(v___x_2784_);
lean_dec(v_snd_2782_);
lean_dec(v_fst_2781_);
lean_del_object(v___x_2779_);
lean_dec(v_fst_2777_);
lean_dec_ref(v_msg_2773_);
lean_dec(v_ref_2772_);
lean_dec_ref(v_oldTraces_2771_);
lean_dec_ref(v_tag_2768_);
lean_dec(v_cls_2766_);
lean_dec_ref(v_inst_2765_);
lean_dec(v_inst_2763_);
lean_dec_ref(v_inst_2762_);
v_toBind_2817_ = lean_ctor_get(v_inst_2760_, 1);
lean_inc(v_toBind_2817_);
lean_dec_ref(v_inst_2760_);
v_modifyTraceState_2818_ = lean_ctor_get(v_inst_2761_, 0);
lean_inc(v_modifyTraceState_2818_);
lean_dec_ref(v_inst_2761_);
v___x_2819_ = lean_apply_1(v_modifyTraceState_2818_, v___f_2786_);
v___x_2820_ = lean_apply_4(v_toBind_2817_, lean_box(0), lean_box(0), v___x_2819_, v___f_2787_);
return v___x_2820_;
}
else
{
lean_dec_ref(v___f_2786_);
goto v___jp_2796_;
}
}
else
{
lean_dec_ref(v___f_2786_);
goto v___jp_2796_;
}
}
v___jp_2821_:
{
double v___x_2823_; double v___x_2824_; double v___x_2825_; uint8_t v___x_2826_; 
v___x_2823_ = lean_unbox_float(v_snd_2782_);
v___x_2824_ = lean_unbox_float(v_fst_2781_);
v___x_2825_ = lean_float_sub(v___x_2823_, v___x_2824_);
v___x_2826_ = lean_float_decLt(v___y_2822_, v___x_2825_);
v___y_2816_ = v___x_2826_;
goto v___jp_2815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object* v_inst_2844_, lean_object* v_inst_2845_, lean_object* v_inst_2846_, lean_object* v_inst_2847_, lean_object* v_always_2848_, lean_object* v_inst_2849_, lean_object* v_cls_2850_, lean_object* v_collapsed_2851_, lean_object* v_tag_2852_, lean_object* v_opts_2853_, lean_object* v_clsEnabled_2854_, lean_object* v_oldTraces_2855_, lean_object* v_ref_2856_, lean_object* v_msg_2857_, lean_object* v_resStartStop_2858_){
_start:
{
uint8_t v_collapsed_boxed_2859_; uint8_t v_clsEnabled_boxed_2860_; lean_object* v_res_2861_; 
v_collapsed_boxed_2859_ = lean_unbox(v_collapsed_2851_);
v_clsEnabled_boxed_2860_ = lean_unbox(v_clsEnabled_2854_);
v_res_2861_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2844_, v_inst_2845_, v_inst_2846_, v_inst_2847_, v_always_2848_, v_inst_2849_, v_cls_2850_, v_collapsed_boxed_2859_, v_tag_2852_, v_opts_2853_, v_clsEnabled_boxed_2860_, v_oldTraces_2855_, v_ref_2856_, v_msg_2857_, v_resStartStop_2858_);
lean_dec_ref(v_opts_2853_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object* v_00_u03b1_2862_, lean_object* v_m_2863_, lean_object* v_inst_2864_, lean_object* v_inst_2865_, lean_object* v_00_u03b5_2866_, lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_always_2869_, lean_object* v_inst_2870_, lean_object* v_cls_2871_, uint8_t v_collapsed_2872_, lean_object* v_tag_2873_, lean_object* v_opts_2874_, uint8_t v_clsEnabled_2875_, lean_object* v_oldTraces_2876_, lean_object* v_ref_2877_, lean_object* v_msg_2878_, lean_object* v_resStartStop_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2864_, v_inst_2865_, v_inst_2867_, v_inst_2868_, v_always_2869_, v_inst_2870_, v_cls_2871_, v_collapsed_2872_, v_tag_2873_, v_opts_2874_, v_clsEnabled_2875_, v_oldTraces_2876_, v_ref_2877_, v_msg_2878_, v_resStartStop_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_2881_ = _args[0];
lean_object* v_m_2882_ = _args[1];
lean_object* v_inst_2883_ = _args[2];
lean_object* v_inst_2884_ = _args[3];
lean_object* v_00_u03b5_2885_ = _args[4];
lean_object* v_inst_2886_ = _args[5];
lean_object* v_inst_2887_ = _args[6];
lean_object* v_always_2888_ = _args[7];
lean_object* v_inst_2889_ = _args[8];
lean_object* v_cls_2890_ = _args[9];
lean_object* v_collapsed_2891_ = _args[10];
lean_object* v_tag_2892_ = _args[11];
lean_object* v_opts_2893_ = _args[12];
lean_object* v_clsEnabled_2894_ = _args[13];
lean_object* v_oldTraces_2895_ = _args[14];
lean_object* v_ref_2896_ = _args[15];
lean_object* v_msg_2897_ = _args[16];
lean_object* v_resStartStop_2898_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2899_; uint8_t v_clsEnabled_boxed_2900_; lean_object* v_res_2901_; 
v_collapsed_boxed_2899_ = lean_unbox(v_collapsed_2891_);
v_clsEnabled_boxed_2900_ = lean_unbox(v_clsEnabled_2894_);
v_res_2901_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(v_00_u03b1_2881_, v_m_2882_, v_inst_2883_, v_inst_2884_, v_00_u03b5_2885_, v_inst_2886_, v_inst_2887_, v_always_2888_, v_inst_2889_, v_cls_2890_, v_collapsed_boxed_2899_, v_tag_2892_, v_opts_2893_, v_clsEnabled_boxed_2900_, v_oldTraces_2895_, v_ref_2896_, v_msg_2897_, v_resStartStop_2898_);
lean_dec_ref(v_opts_2893_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object* v_inst_2902_, lean_object* v_____do__lift_2903_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = lean_apply_1(v_inst_2902_, v_____do__lift_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_always_2909_, lean_object* v_inst_2910_, lean_object* v_cls_2911_, uint8_t v_collapsed_2912_, lean_object* v_tag_2913_, lean_object* v_opts_2914_, uint8_t v_clsEnabled_2915_, lean_object* v_oldTraces_2916_, lean_object* v_ref_2917_, lean_object* v_msg_2918_, lean_object* v_resStartStop_2919_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2905_, v_inst_2906_, v_inst_2907_, v_inst_2908_, v_always_2909_, v_inst_2910_, v_cls_2911_, v_collapsed_2912_, v_tag_2913_, v_opts_2914_, v_clsEnabled_2915_, v_oldTraces_2916_, v_ref_2917_, v_msg_2918_, v_resStartStop_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_always_2925_, lean_object* v_inst_2926_, lean_object* v_cls_2927_, lean_object* v_collapsed_2928_, lean_object* v_tag_2929_, lean_object* v_opts_2930_, lean_object* v_clsEnabled_2931_, lean_object* v_oldTraces_2932_, lean_object* v_ref_2933_, lean_object* v_msg_2934_, lean_object* v_resStartStop_2935_){
_start:
{
uint8_t v_collapsed_boxed_2936_; uint8_t v_clsEnabled_boxed_2937_; lean_object* v_res_2938_; 
v_collapsed_boxed_2936_ = lean_unbox(v_collapsed_2928_);
v_clsEnabled_boxed_2937_ = lean_unbox(v_clsEnabled_2931_);
v_res_2938_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_2921_, v_inst_2922_, v_inst_2923_, v_inst_2924_, v_always_2925_, v_inst_2926_, v_cls_2927_, v_collapsed_boxed_2936_, v_tag_2929_, v_opts_2930_, v_clsEnabled_boxed_2937_, v_oldTraces_2932_, v_ref_2933_, v_msg_2934_, v_resStartStop_2935_);
lean_dec_ref(v_opts_2930_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object* v_always_2939_, lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_inst_2944_, lean_object* v_cls_2945_, uint8_t v_collapsed_2946_, lean_object* v_tag_2947_, lean_object* v_opts_2948_, uint8_t v_clsEnabled_2949_, lean_object* v_oldTraces_2950_, lean_object* v_ref_2951_, lean_object* v_toPure_2952_, lean_object* v_toBind_2953_, lean_object* v_k_2954_, lean_object* v_inst_2955_, lean_object* v_msg_2956_){
_start:
{
lean_object* v_tryCatch_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___f_2960_; lean_object* v___f_2961_; lean_object* v___f_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v_tryCatch_2957_ = lean_ctor_get(v_always_2939_, 1);
lean_inc(v_tryCatch_2957_);
v___x_2958_ = lean_box(v_collapsed_2946_);
v___x_2959_ = lean_box(v_clsEnabled_2949_);
lean_inc_ref(v_opts_2948_);
v___f_2960_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__1___boxed), 15, 14);
lean_closure_set(v___f_2960_, 0, v_inst_2940_);
lean_closure_set(v___f_2960_, 1, v_inst_2941_);
lean_closure_set(v___f_2960_, 2, v_inst_2942_);
lean_closure_set(v___f_2960_, 3, v_inst_2943_);
lean_closure_set(v___f_2960_, 4, v_always_2939_);
lean_closure_set(v___f_2960_, 5, v_inst_2944_);
lean_closure_set(v___f_2960_, 6, v_cls_2945_);
lean_closure_set(v___f_2960_, 7, v___x_2958_);
lean_closure_set(v___f_2960_, 8, v_tag_2947_);
lean_closure_set(v___f_2960_, 9, v_opts_2948_);
lean_closure_set(v___f_2960_, 10, v___x_2959_);
lean_closure_set(v___f_2960_, 11, v_oldTraces_2950_);
lean_closure_set(v___f_2960_, 12, v_ref_2951_);
lean_closure_set(v___f_2960_, 13, v_msg_2956_);
lean_inc_n(v_toPure_2952_, 2);
v___f_2961_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2961_, 0, v_toPure_2952_);
v___f_2962_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2962_, 0, v_toPure_2952_);
lean_inc(v_toBind_2953_);
v___x_2963_ = lean_apply_4(v_toBind_2953_, lean_box(0), lean_box(0), v_k_2954_, v___f_2962_);
v___x_2964_ = lean_apply_3(v_tryCatch_2957_, lean_box(0), v___x_2963_, v___f_2961_);
v___x_2965_ = l_Lean_KVMap_instValueBool;
v___x_2966_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2967_ = l_Lean_Option_get___redArg(v___x_2965_, v_opts_2948_, v___x_2966_);
lean_dec_ref(v_opts_2948_);
v___x_2968_ = lean_unbox(v___x_2967_);
lean_dec(v___x_2967_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___f_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2969_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_2970_ = lean_apply_2(v_inst_2955_, lean_box(0), v___x_2969_);
lean_inc(v___x_2970_);
lean_inc_n(v_toBind_2953_, 2);
v___f_2971_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_2971_, 0, v_toPure_2952_);
lean_closure_set(v___f_2971_, 1, v_toBind_2953_);
lean_closure_set(v___f_2971_, 2, v___x_2970_);
lean_closure_set(v___f_2971_, 3, v___x_2964_);
v___x_2972_ = lean_apply_4(v_toBind_2953_, lean_box(0), lean_box(0), v___x_2970_, v___f_2971_);
v___x_2973_ = lean_apply_4(v_toBind_2953_, lean_box(0), lean_box(0), v___x_2972_, v___f_2960_);
return v___x_2973_;
}
else
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___f_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2974_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_2975_ = lean_apply_2(v_inst_2955_, lean_box(0), v___x_2974_);
lean_inc(v___x_2975_);
lean_inc_n(v_toBind_2953_, 2);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_2976_, 0, v_toPure_2952_);
lean_closure_set(v___f_2976_, 1, v_toBind_2953_);
lean_closure_set(v___f_2976_, 2, v___x_2975_);
lean_closure_set(v___f_2976_, 3, v___x_2964_);
v___x_2977_ = lean_apply_4(v_toBind_2953_, lean_box(0), lean_box(0), v___x_2975_, v___f_2976_);
v___x_2978_ = lean_apply_4(v_toBind_2953_, lean_box(0), lean_box(0), v___x_2977_, v___f_2960_);
return v___x_2978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_2979_ = _args[0];
lean_object* v_inst_2980_ = _args[1];
lean_object* v_inst_2981_ = _args[2];
lean_object* v_inst_2982_ = _args[3];
lean_object* v_inst_2983_ = _args[4];
lean_object* v_inst_2984_ = _args[5];
lean_object* v_cls_2985_ = _args[6];
lean_object* v_collapsed_2986_ = _args[7];
lean_object* v_tag_2987_ = _args[8];
lean_object* v_opts_2988_ = _args[9];
lean_object* v_clsEnabled_2989_ = _args[10];
lean_object* v_oldTraces_2990_ = _args[11];
lean_object* v_ref_2991_ = _args[12];
lean_object* v_toPure_2992_ = _args[13];
lean_object* v_toBind_2993_ = _args[14];
lean_object* v_k_2994_ = _args[15];
lean_object* v_inst_2995_ = _args[16];
lean_object* v_msg_2996_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2997_; uint8_t v_clsEnabled_boxed_2998_; lean_object* v_res_2999_; 
v_collapsed_boxed_2997_ = lean_unbox(v_collapsed_2986_);
v_clsEnabled_boxed_2998_ = lean_unbox(v_clsEnabled_2989_);
v_res_2999_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_always_2979_, v_inst_2980_, v_inst_2981_, v_inst_2982_, v_inst_2983_, v_inst_2984_, v_cls_2985_, v_collapsed_boxed_2997_, v_tag_2987_, v_opts_2988_, v_clsEnabled_boxed_2998_, v_oldTraces_2990_, v_ref_2991_, v_toPure_2992_, v_toBind_2993_, v_k_2994_, v_inst_2995_, v_msg_2996_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object* v_always_3000_, lean_object* v_inst_3001_, lean_object* v_inst_3002_, lean_object* v_inst_3003_, lean_object* v_inst_3004_, lean_object* v_inst_3005_, lean_object* v_cls_3006_, uint8_t v_collapsed_3007_, lean_object* v_tag_3008_, lean_object* v_opts_3009_, uint8_t v_clsEnabled_3010_, lean_object* v_oldTraces_3011_, lean_object* v_toPure_3012_, lean_object* v_toBind_3013_, lean_object* v_k_3014_, lean_object* v_inst_3015_, lean_object* v_msg_3016_, lean_object* v___f_3017_, lean_object* v_withRef_3018_, lean_object* v_getRef_3019_, lean_object* v_ref_3020_){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___f_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___f_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3021_ = lean_box(v_collapsed_3007_);
v___x_3022_ = lean_box(v_clsEnabled_3010_);
lean_inc_n(v_toBind_3013_, 3);
lean_inc(v_ref_3020_);
v___f_3023_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__10___boxed), 18, 17);
lean_closure_set(v___f_3023_, 0, v_always_3000_);
lean_closure_set(v___f_3023_, 1, v_inst_3001_);
lean_closure_set(v___f_3023_, 2, v_inst_3002_);
lean_closure_set(v___f_3023_, 3, v_inst_3003_);
lean_closure_set(v___f_3023_, 4, v_inst_3004_);
lean_closure_set(v___f_3023_, 5, v_inst_3005_);
lean_closure_set(v___f_3023_, 6, v_cls_3006_);
lean_closure_set(v___f_3023_, 7, v___x_3021_);
lean_closure_set(v___f_3023_, 8, v_tag_3008_);
lean_closure_set(v___f_3023_, 9, v_opts_3009_);
lean_closure_set(v___f_3023_, 10, v___x_3022_);
lean_closure_set(v___f_3023_, 11, v_oldTraces_3011_);
lean_closure_set(v___f_3023_, 12, v_ref_3020_);
lean_closure_set(v___f_3023_, 13, v_toPure_3012_);
lean_closure_set(v___f_3023_, 14, v_toBind_3013_);
lean_closure_set(v___f_3023_, 15, v_k_3014_);
lean_closure_set(v___f_3023_, 16, v_inst_3015_);
v___x_3024_ = lean_box(0);
v___x_3025_ = lean_apply_1(v_msg_3016_, v___x_3024_);
v___x_3026_ = lean_apply_4(v_toBind_3013_, lean_box(0), lean_box(0), v___x_3025_, v___f_3017_);
v___f_3027_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3027_, 0, v_ref_3020_);
lean_closure_set(v___f_3027_, 1, v_withRef_3018_);
lean_closure_set(v___f_3027_, 2, v___x_3026_);
v___x_3028_ = lean_apply_4(v_toBind_3013_, lean_box(0), lean_box(0), v_getRef_3019_, v___f_3027_);
v___x_3029_ = lean_apply_4(v_toBind_3013_, lean_box(0), lean_box(0), v___x_3028_, v___f_3023_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_3030_ = _args[0];
lean_object* v_inst_3031_ = _args[1];
lean_object* v_inst_3032_ = _args[2];
lean_object* v_inst_3033_ = _args[3];
lean_object* v_inst_3034_ = _args[4];
lean_object* v_inst_3035_ = _args[5];
lean_object* v_cls_3036_ = _args[6];
lean_object* v_collapsed_3037_ = _args[7];
lean_object* v_tag_3038_ = _args[8];
lean_object* v_opts_3039_ = _args[9];
lean_object* v_clsEnabled_3040_ = _args[10];
lean_object* v_oldTraces_3041_ = _args[11];
lean_object* v_toPure_3042_ = _args[12];
lean_object* v_toBind_3043_ = _args[13];
lean_object* v_k_3044_ = _args[14];
lean_object* v_inst_3045_ = _args[15];
lean_object* v_msg_3046_ = _args[16];
lean_object* v___f_3047_ = _args[17];
lean_object* v_withRef_3048_ = _args[18];
lean_object* v_getRef_3049_ = _args[19];
lean_object* v_ref_3050_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_3051_; uint8_t v_clsEnabled_boxed_3052_; lean_object* v_res_3053_; 
v_collapsed_boxed_3051_ = lean_unbox(v_collapsed_3037_);
v_clsEnabled_boxed_3052_ = lean_unbox(v_clsEnabled_3040_);
v_res_3053_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_always_3030_, v_inst_3031_, v_inst_3032_, v_inst_3033_, v_inst_3034_, v_inst_3035_, v_cls_3036_, v_collapsed_boxed_3051_, v_tag_3038_, v_opts_3039_, v_clsEnabled_boxed_3052_, v_oldTraces_3041_, v_toPure_3042_, v_toBind_3043_, v_k_3044_, v_inst_3045_, v_msg_3046_, v___f_3047_, v_withRef_3048_, v_getRef_3049_, v_ref_3050_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object* v_inst_3054_, lean_object* v_always_3055_, lean_object* v_inst_3056_, lean_object* v_inst_3057_, lean_object* v_inst_3058_, lean_object* v_inst_3059_, lean_object* v_cls_3060_, uint8_t v_collapsed_3061_, lean_object* v_tag_3062_, lean_object* v_opts_3063_, uint8_t v_clsEnabled_3064_, lean_object* v_toPure_3065_, lean_object* v_toBind_3066_, lean_object* v_k_3067_, lean_object* v_inst_3068_, lean_object* v_msg_3069_, lean_object* v___f_3070_, lean_object* v_oldTraces_3071_){
_start:
{
lean_object* v_getRef_3072_; lean_object* v_withRef_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___f_3076_; lean_object* v___x_3077_; 
v_getRef_3072_ = lean_ctor_get(v_inst_3054_, 0);
lean_inc_n(v_getRef_3072_, 2);
v_withRef_3073_ = lean_ctor_get(v_inst_3054_, 1);
lean_inc(v_withRef_3073_);
v___x_3074_ = lean_box(v_collapsed_3061_);
v___x_3075_ = lean_box(v_clsEnabled_3064_);
lean_inc(v_toBind_3066_);
v___f_3076_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__3___boxed), 21, 20);
lean_closure_set(v___f_3076_, 0, v_always_3055_);
lean_closure_set(v___f_3076_, 1, v_inst_3056_);
lean_closure_set(v___f_3076_, 2, v_inst_3057_);
lean_closure_set(v___f_3076_, 3, v_inst_3054_);
lean_closure_set(v___f_3076_, 4, v_inst_3058_);
lean_closure_set(v___f_3076_, 5, v_inst_3059_);
lean_closure_set(v___f_3076_, 6, v_cls_3060_);
lean_closure_set(v___f_3076_, 7, v___x_3074_);
lean_closure_set(v___f_3076_, 8, v_tag_3062_);
lean_closure_set(v___f_3076_, 9, v_opts_3063_);
lean_closure_set(v___f_3076_, 10, v___x_3075_);
lean_closure_set(v___f_3076_, 11, v_oldTraces_3071_);
lean_closure_set(v___f_3076_, 12, v_toPure_3065_);
lean_closure_set(v___f_3076_, 13, v_toBind_3066_);
lean_closure_set(v___f_3076_, 14, v_k_3067_);
lean_closure_set(v___f_3076_, 15, v_inst_3068_);
lean_closure_set(v___f_3076_, 16, v_msg_3069_);
lean_closure_set(v___f_3076_, 17, v___f_3070_);
lean_closure_set(v___f_3076_, 18, v_withRef_3073_);
lean_closure_set(v___f_3076_, 19, v_getRef_3072_);
v___x_3077_ = lean_apply_4(v_toBind_3066_, lean_box(0), lean_box(0), v_getRef_3072_, v___f_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_3078_ = _args[0];
lean_object* v_always_3079_ = _args[1];
lean_object* v_inst_3080_ = _args[2];
lean_object* v_inst_3081_ = _args[3];
lean_object* v_inst_3082_ = _args[4];
lean_object* v_inst_3083_ = _args[5];
lean_object* v_cls_3084_ = _args[6];
lean_object* v_collapsed_3085_ = _args[7];
lean_object* v_tag_3086_ = _args[8];
lean_object* v_opts_3087_ = _args[9];
lean_object* v_clsEnabled_3088_ = _args[10];
lean_object* v_toPure_3089_ = _args[11];
lean_object* v_toBind_3090_ = _args[12];
lean_object* v_k_3091_ = _args[13];
lean_object* v_inst_3092_ = _args[14];
lean_object* v_msg_3093_ = _args[15];
lean_object* v___f_3094_ = _args[16];
lean_object* v_oldTraces_3095_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3096_; uint8_t v_clsEnabled_boxed_3097_; lean_object* v_res_3098_; 
v_collapsed_boxed_3096_ = lean_unbox(v_collapsed_3085_);
v_clsEnabled_boxed_3097_ = lean_unbox(v_clsEnabled_3088_);
v_res_3098_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3078_, v_always_3079_, v_inst_3080_, v_inst_3081_, v_inst_3082_, v_inst_3083_, v_cls_3084_, v_collapsed_boxed_3096_, v_tag_3086_, v_opts_3087_, v_clsEnabled_boxed_3097_, v_toPure_3089_, v_toBind_3090_, v_k_3091_, v_inst_3092_, v_msg_3093_, v___f_3094_, v_oldTraces_3095_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object* v_inst_3099_, lean_object* v_always_3100_, lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_inst_3104_, lean_object* v_cls_3105_, uint8_t v_collapsed_3106_, lean_object* v_tag_3107_, lean_object* v_opts_3108_, lean_object* v_toPure_3109_, lean_object* v_toBind_3110_, lean_object* v_k_3111_, lean_object* v_inst_3112_, lean_object* v_msg_3113_, lean_object* v___f_3114_, uint8_t v_clsEnabled_3115_){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___f_3118_; 
v___x_3116_ = lean_box(v_collapsed_3106_);
v___x_3117_ = lean_box(v_clsEnabled_3115_);
lean_inc(v_k_3111_);
lean_inc(v_toBind_3110_);
lean_inc_ref(v_opts_3108_);
lean_inc_ref(v_inst_3102_);
lean_inc_ref(v_inst_3101_);
v___f_3118_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__2___boxed), 18, 17);
lean_closure_set(v___f_3118_, 0, v_inst_3099_);
lean_closure_set(v___f_3118_, 1, v_always_3100_);
lean_closure_set(v___f_3118_, 2, v_inst_3101_);
lean_closure_set(v___f_3118_, 3, v_inst_3102_);
lean_closure_set(v___f_3118_, 4, v_inst_3103_);
lean_closure_set(v___f_3118_, 5, v_inst_3104_);
lean_closure_set(v___f_3118_, 6, v_cls_3105_);
lean_closure_set(v___f_3118_, 7, v___x_3116_);
lean_closure_set(v___f_3118_, 8, v_tag_3107_);
lean_closure_set(v___f_3118_, 9, v_opts_3108_);
lean_closure_set(v___f_3118_, 10, v___x_3117_);
lean_closure_set(v___f_3118_, 11, v_toPure_3109_);
lean_closure_set(v___f_3118_, 12, v_toBind_3110_);
lean_closure_set(v___f_3118_, 13, v_k_3111_);
lean_closure_set(v___f_3118_, 14, v_inst_3112_);
lean_closure_set(v___f_3118_, 15, v_msg_3113_);
lean_closure_set(v___f_3118_, 16, v___f_3114_);
if (v_clsEnabled_3115_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; 
v___x_3122_ = l_Lean_KVMap_instValueBool;
v___x_3123_ = l_Lean_trace_profiler;
v___x_3124_ = l_Lean_Option_get___redArg(v___x_3122_, v_opts_3108_, v___x_3123_);
lean_dec_ref(v_opts_3108_);
v___x_3125_ = lean_unbox(v___x_3124_);
lean_dec(v___x_3124_);
if (v___x_3125_ == 0)
{
lean_dec_ref(v___f_3118_);
lean_dec(v_toBind_3110_);
lean_dec_ref(v_inst_3102_);
lean_dec_ref(v_inst_3101_);
return v_k_3111_;
}
else
{
lean_dec(v_k_3111_);
goto v___jp_3119_;
}
}
else
{
lean_dec(v_k_3111_);
lean_dec_ref(v_opts_3108_);
goto v___jp_3119_;
}
v___jp_3119_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3101_, v_inst_3102_);
v___x_3121_ = lean_apply_4(v_toBind_3110_, lean_box(0), lean_box(0), v___x_3120_, v___f_3118_);
return v___x_3121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_3126_ = _args[0];
lean_object* v_always_3127_ = _args[1];
lean_object* v_inst_3128_ = _args[2];
lean_object* v_inst_3129_ = _args[3];
lean_object* v_inst_3130_ = _args[4];
lean_object* v_inst_3131_ = _args[5];
lean_object* v_cls_3132_ = _args[6];
lean_object* v_collapsed_3133_ = _args[7];
lean_object* v_tag_3134_ = _args[8];
lean_object* v_opts_3135_ = _args[9];
lean_object* v_toPure_3136_ = _args[10];
lean_object* v_toBind_3137_ = _args[11];
lean_object* v_k_3138_ = _args[12];
lean_object* v_inst_3139_ = _args[13];
lean_object* v_msg_3140_ = _args[14];
lean_object* v___f_3141_ = _args[15];
lean_object* v_clsEnabled_3142_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3143_; uint8_t v_clsEnabled_boxed_3144_; lean_object* v_res_3145_; 
v_collapsed_boxed_3143_ = lean_unbox(v_collapsed_3133_);
v_clsEnabled_boxed_3144_ = lean_unbox(v_clsEnabled_3142_);
v_res_3145_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3126_, v_always_3127_, v_inst_3128_, v_inst_3129_, v_inst_3130_, v_inst_3131_, v_cls_3132_, v_collapsed_boxed_3143_, v_tag_3134_, v_opts_3135_, v_toPure_3136_, v_toBind_3137_, v_k_3138_, v_inst_3139_, v_msg_3140_, v___f_3141_, v_clsEnabled_boxed_3144_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object* v_k_3146_, lean_object* v_inst_3147_, lean_object* v_toApplicative_3148_, lean_object* v_inst_3149_, lean_object* v_always_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_cls_3154_, uint8_t v_collapsed_3155_, lean_object* v_tag_3156_, lean_object* v_toBind_3157_, lean_object* v_inst_3158_, lean_object* v_msg_3159_, lean_object* v___f_3160_, lean_object* v_inst_3161_, lean_object* v_opts_3162_){
_start:
{
uint8_t v_hasTrace_3163_; 
v_hasTrace_3163_ = lean_ctor_get_uint8(v_opts_3162_, sizeof(void*)*1);
if (v_hasTrace_3163_ == 0)
{
lean_dec_ref(v_opts_3162_);
lean_dec(v_inst_3161_);
lean_dec(v___f_3160_);
lean_dec(v_msg_3159_);
lean_dec(v_inst_3158_);
lean_dec(v_toBind_3157_);
lean_dec_ref(v_tag_3156_);
lean_dec(v_cls_3154_);
lean_dec_ref(v_inst_3153_);
lean_dec(v_inst_3152_);
lean_dec_ref(v_inst_3151_);
lean_dec_ref(v_always_3150_);
lean_dec_ref(v_inst_3149_);
lean_dec_ref(v_toApplicative_3148_);
lean_dec_ref(v_inst_3147_);
return v_k_3146_;
}
else
{
lean_object* v_getInheritedTraceOptions_3164_; lean_object* v_toPure_3165_; lean_object* v___x_3166_; lean_object* v___f_3167_; lean_object* v___f_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_getInheritedTraceOptions_3164_ = lean_ctor_get(v_inst_3147_, 2);
lean_inc(v_getInheritedTraceOptions_3164_);
v_toPure_3165_ = lean_ctor_get(v_toApplicative_3148_, 1);
lean_inc_n(v_toPure_3165_, 2);
lean_dec_ref(v_toApplicative_3148_);
v___x_3166_ = lean_box(v_collapsed_3155_);
lean_inc_n(v_toBind_3157_, 3);
lean_inc(v_cls_3154_);
v___f_3167_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_3167_, 0, v_inst_3149_);
lean_closure_set(v___f_3167_, 1, v_always_3150_);
lean_closure_set(v___f_3167_, 2, v_inst_3151_);
lean_closure_set(v___f_3167_, 3, v_inst_3147_);
lean_closure_set(v___f_3167_, 4, v_inst_3152_);
lean_closure_set(v___f_3167_, 5, v_inst_3153_);
lean_closure_set(v___f_3167_, 6, v_cls_3154_);
lean_closure_set(v___f_3167_, 7, v___x_3166_);
lean_closure_set(v___f_3167_, 8, v_tag_3156_);
lean_closure_set(v___f_3167_, 9, v_opts_3162_);
lean_closure_set(v___f_3167_, 10, v_toPure_3165_);
lean_closure_set(v___f_3167_, 11, v_toBind_3157_);
lean_closure_set(v___f_3167_, 12, v_k_3146_);
lean_closure_set(v___f_3167_, 13, v_inst_3158_);
lean_closure_set(v___f_3167_, 14, v_msg_3159_);
lean_closure_set(v___f_3167_, 15, v___f_3160_);
v___f_3168_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3168_, 0, v_toPure_3165_);
lean_closure_set(v___f_3168_, 1, v_cls_3154_);
lean_closure_set(v___f_3168_, 2, v_toBind_3157_);
lean_closure_set(v___f_3168_, 3, v_inst_3161_);
v___x_3169_ = lean_apply_4(v_toBind_3157_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3164_, v___f_3168_);
v___x_3170_ = lean_apply_4(v_toBind_3157_, lean_box(0), lean_box(0), v___x_3169_, v___f_3167_);
return v___x_3170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_k_3171_ = _args[0];
lean_object* v_inst_3172_ = _args[1];
lean_object* v_toApplicative_3173_ = _args[2];
lean_object* v_inst_3174_ = _args[3];
lean_object* v_always_3175_ = _args[4];
lean_object* v_inst_3176_ = _args[5];
lean_object* v_inst_3177_ = _args[6];
lean_object* v_inst_3178_ = _args[7];
lean_object* v_cls_3179_ = _args[8];
lean_object* v_collapsed_3180_ = _args[9];
lean_object* v_tag_3181_ = _args[10];
lean_object* v_toBind_3182_ = _args[11];
lean_object* v_inst_3183_ = _args[12];
lean_object* v_msg_3184_ = _args[13];
lean_object* v___f_3185_ = _args[14];
lean_object* v_inst_3186_ = _args[15];
lean_object* v_opts_3187_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3188_; lean_object* v_res_3189_; 
v_collapsed_boxed_3188_ = lean_unbox(v_collapsed_3180_);
v_res_3189_ = l_Lean_withTraceNodeBefore___redArg___lam__7(v_k_3171_, v_inst_3172_, v_toApplicative_3173_, v_inst_3174_, v_always_3175_, v_inst_3176_, v_inst_3177_, v_inst_3178_, v_cls_3179_, v_collapsed_boxed_3188_, v_tag_3181_, v_toBind_3182_, v_inst_3183_, v_msg_3184_, v___f_3185_, v_inst_3186_, v_opts_3187_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_inst_3193_, lean_object* v_inst_3194_, lean_object* v_always_3195_, lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_cls_3198_, lean_object* v_msg_3199_, lean_object* v_k_3200_, uint8_t v_collapsed_3201_, lean_object* v_tag_3202_){
_start:
{
lean_object* v_toApplicative_3203_; lean_object* v_toBind_3204_; lean_object* v___f_3205_; lean_object* v___x_3206_; lean_object* v___f_3207_; lean_object* v___x_3208_; 
v_toApplicative_3203_ = lean_ctor_get(v_inst_3190_, 0);
lean_inc_ref(v_toApplicative_3203_);
v_toBind_3204_ = lean_ctor_get(v_inst_3190_, 1);
lean_inc_n(v_toBind_3204_, 2);
lean_inc(v_inst_3193_);
v___f_3205_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3205_, 0, v_inst_3193_);
v___x_3206_ = lean_box(v_collapsed_3201_);
lean_inc(v_inst_3194_);
v___f_3207_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3207_, 0, v_k_3200_);
lean_closure_set(v___f_3207_, 1, v_inst_3191_);
lean_closure_set(v___f_3207_, 2, v_toApplicative_3203_);
lean_closure_set(v___f_3207_, 3, v_inst_3192_);
lean_closure_set(v___f_3207_, 4, v_always_3195_);
lean_closure_set(v___f_3207_, 5, v_inst_3190_);
lean_closure_set(v___f_3207_, 6, v_inst_3193_);
lean_closure_set(v___f_3207_, 7, v_inst_3197_);
lean_closure_set(v___f_3207_, 8, v_cls_3198_);
lean_closure_set(v___f_3207_, 9, v___x_3206_);
lean_closure_set(v___f_3207_, 10, v_tag_3202_);
lean_closure_set(v___f_3207_, 11, v_toBind_3204_);
lean_closure_set(v___f_3207_, 12, v_inst_3196_);
lean_closure_set(v___f_3207_, 13, v_msg_3199_);
lean_closure_set(v___f_3207_, 14, v___f_3205_);
lean_closure_set(v___f_3207_, 15, v_inst_3194_);
v___x_3208_ = lean_apply_4(v_toBind_3204_, lean_box(0), lean_box(0), v_inst_3194_, v___f_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_always_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_cls_3217_, lean_object* v_msg_3218_, lean_object* v_k_3219_, lean_object* v_collapsed_3220_, lean_object* v_tag_3221_){
_start:
{
uint8_t v_collapsed_boxed_3222_; lean_object* v_res_3223_; 
v_collapsed_boxed_3222_ = lean_unbox(v_collapsed_3220_);
v_res_3223_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3209_, v_inst_3210_, v_inst_3211_, v_inst_3212_, v_inst_3213_, v_always_3214_, v_inst_3215_, v_inst_3216_, v_cls_3217_, v_msg_3218_, v_k_3219_, v_collapsed_boxed_3222_, v_tag_3221_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object* v_00_u03b1_3224_, lean_object* v_m_3225_, lean_object* v_inst_3226_, lean_object* v_inst_3227_, lean_object* v_00_u03b5_3228_, lean_object* v_inst_3229_, lean_object* v_inst_3230_, lean_object* v_inst_3231_, lean_object* v_always_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_cls_3235_, lean_object* v_msg_3236_, lean_object* v_k_3237_, uint8_t v_collapsed_3238_, lean_object* v_tag_3239_){
_start:
{
lean_object* v_toApplicative_3240_; lean_object* v_toBind_3241_; lean_object* v___f_3242_; lean_object* v___x_3243_; lean_object* v___f_3244_; lean_object* v___x_3245_; 
v_toApplicative_3240_ = lean_ctor_get(v_inst_3226_, 0);
lean_inc_ref(v_toApplicative_3240_);
v_toBind_3241_ = lean_ctor_get(v_inst_3226_, 1);
lean_inc_n(v_toBind_3241_, 2);
lean_inc(v_inst_3230_);
v___f_3242_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3242_, 0, v_inst_3230_);
v___x_3243_ = lean_box(v_collapsed_3238_);
lean_inc(v_inst_3231_);
v___f_3244_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3244_, 0, v_k_3237_);
lean_closure_set(v___f_3244_, 1, v_inst_3227_);
lean_closure_set(v___f_3244_, 2, v_toApplicative_3240_);
lean_closure_set(v___f_3244_, 3, v_inst_3229_);
lean_closure_set(v___f_3244_, 4, v_always_3232_);
lean_closure_set(v___f_3244_, 5, v_inst_3226_);
lean_closure_set(v___f_3244_, 6, v_inst_3230_);
lean_closure_set(v___f_3244_, 7, v_inst_3234_);
lean_closure_set(v___f_3244_, 8, v_cls_3235_);
lean_closure_set(v___f_3244_, 9, v___x_3243_);
lean_closure_set(v___f_3244_, 10, v_tag_3239_);
lean_closure_set(v___f_3244_, 11, v_toBind_3241_);
lean_closure_set(v___f_3244_, 12, v_inst_3233_);
lean_closure_set(v___f_3244_, 13, v_msg_3236_);
lean_closure_set(v___f_3244_, 14, v___f_3242_);
lean_closure_set(v___f_3244_, 15, v_inst_3231_);
v___x_3245_ = lean_apply_4(v_toBind_3241_, lean_box(0), lean_box(0), v_inst_3231_, v___f_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object* v_00_u03b1_3246_, lean_object* v_m_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_00_u03b5_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_always_3254_, lean_object* v_inst_3255_, lean_object* v_inst_3256_, lean_object* v_cls_3257_, lean_object* v_msg_3258_, lean_object* v_k_3259_, lean_object* v_collapsed_3260_, lean_object* v_tag_3261_){
_start:
{
uint8_t v_collapsed_boxed_3262_; lean_object* v_res_3263_; 
v_collapsed_boxed_3262_ = lean_unbox(v_collapsed_3260_);
v_res_3263_ = l_Lean_withTraceNodeBefore(v_00_u03b1_3246_, v_m_3247_, v_inst_3248_, v_inst_3249_, v_00_u03b5_3250_, v_inst_3251_, v_inst_3252_, v_inst_3253_, v_always_3254_, v_inst_3255_, v_inst_3256_, v_cls_3257_, v_msg_3258_, v_k_3259_, v_collapsed_boxed_3262_, v_tag_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0(lean_object* v_toApplicative_3264_, lean_object* v_____s_3265_){
_start:
{
lean_object* v_toPure_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_toPure_3266_ = lean_ctor_get(v_toApplicative_3264_, 1);
lean_inc(v_toPure_3266_);
lean_dec_ref(v_toApplicative_3264_);
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_apply_2(v_toPure_3266_, lean_box(0), v___x_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__1(lean_object* v_x_3269_, lean_object* v_x_3270_){
_start:
{
lean_object* v_fst_3271_; lean_object* v_fst_3272_; lean_object* v_fst_3273_; lean_object* v_fst_3274_; uint8_t v___x_3275_; 
v_fst_3271_ = lean_ctor_get(v_x_3269_, 0);
v_fst_3272_ = lean_ctor_get(v_x_3270_, 0);
v_fst_3273_ = lean_ctor_get(v_fst_3271_, 0);
v_fst_3274_ = lean_ctor_get(v_fst_3272_, 0);
v___x_3275_ = l_String_instDecidableLtRaw___aux__1(v_fst_3273_, v_fst_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1___boxed(lean_object* v_x_3276_, lean_object* v_x_3277_){
_start:
{
uint8_t v_res_3278_; lean_object* v_r_3279_; 
v_res_3278_ = l_Lean_addTraceAsMessages___redArg___lam__1(v_x_3276_, v_x_3277_);
lean_dec_ref(v_x_3277_);
lean_dec_ref(v_x_3276_);
v_r_3279_ = lean_box(v_res_3278_);
return v_r_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object* v_x1_3280_, lean_object* v_x2_3281_, lean_object* v_x3_3282_){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v_x2_3281_);
lean_ctor_set(v___x_3283_, 1, v_x3_3282_);
v___x_3284_ = lean_array_push(v_x1_3280_, v___x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object* v_toApplicative_3285_, lean_object* v___x_3286_, lean_object* v_r_3287_){
_start:
{
lean_object* v_toPure_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_toPure_3288_ = lean_ctor_get(v_toApplicative_3285_, 1);
lean_inc(v_toPure_3288_);
lean_dec_ref(v_toApplicative_3285_);
v___x_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3286_);
v___x_3290_ = lean_apply_2(v_toPure_3288_, lean_box(0), v___x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object* v_____do__lift_3291_, lean_object* v___x_3292_, lean_object* v_fst_3293_, lean_object* v_snd_3294_, lean_object* v_logMessage_3295_, lean_object* v_toBind_3296_, lean_object* v___f_3297_, lean_object* v_____do__lift_3298_){
_start:
{
uint8_t v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3299_ = 0;
v___x_3300_ = l_Lean_Elab_mkMessageCore(v_____do__lift_3291_, v_____do__lift_3298_, v___x_3292_, v___x_3299_, v_fst_3293_, v_snd_3294_);
v___x_3301_ = lean_apply_1(v_logMessage_3295_, v___x_3300_);
v___x_3302_ = lean_apply_4(v_toBind_3296_, lean_box(0), lean_box(0), v___x_3301_, v___f_3297_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object* v_____do__lift_3303_, lean_object* v___x_3304_, lean_object* v_fst_3305_, lean_object* v_snd_3306_, lean_object* v_logMessage_3307_, lean_object* v_toBind_3308_, lean_object* v___f_3309_, lean_object* v_____do__lift_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_addTraceAsMessages___redArg___lam__4(v_____do__lift_3303_, v___x_3304_, v_fst_3305_, v_snd_3306_, v_logMessage_3307_, v_toBind_3308_, v___f_3309_, v_____do__lift_3310_);
lean_dec(v_snd_3306_);
lean_dec(v_fst_3305_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object* v___x_3312_, lean_object* v_fst_3313_, lean_object* v_snd_3314_, lean_object* v_logMessage_3315_, lean_object* v_toBind_3316_, lean_object* v___f_3317_, lean_object* v_toMonadFileMap_3318_, lean_object* v_____do__lift_3319_){
_start:
{
lean_object* v___f_3320_; lean_object* v___x_3321_; 
lean_inc(v_toBind_3316_);
v___f_3320_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_3320_, 0, v_____do__lift_3319_);
lean_closure_set(v___f_3320_, 1, v___x_3312_);
lean_closure_set(v___f_3320_, 2, v_fst_3313_);
lean_closure_set(v___f_3320_, 3, v_snd_3314_);
lean_closure_set(v___f_3320_, 4, v_logMessage_3315_);
lean_closure_set(v___f_3320_, 5, v_toBind_3316_);
lean_closure_set(v___f_3320_, 6, v___f_3317_);
v___x_3321_ = lean_apply_4(v_toBind_3316_, lean_box(0), lean_box(0), v_toMonadFileMap_3318_, v___f_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object* v___x_3322_, uint8_t v___x_3323_, lean_object* v_inst_3324_, lean_object* v_toBind_3325_, lean_object* v___f_3326_, lean_object* v_a_3327_, lean_object* v_x_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_fst_3330_; lean_object* v_snd_3331_; lean_object* v_fst_3332_; lean_object* v_snd_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3353_; 
v_fst_3330_ = lean_ctor_get(v_a_3327_, 0);
lean_inc(v_fst_3330_);
v_snd_3331_ = lean_ctor_get(v_a_3327_, 1);
lean_inc(v_snd_3331_);
lean_dec_ref(v_a_3327_);
v_fst_3332_ = lean_ctor_get(v_fst_3330_, 0);
v_snd_3333_ = lean_ctor_get(v_fst_3330_, 1);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_fst_3330_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3335_ = v_fst_3330_;
v_isShared_3336_ = v_isSharedCheck_3353_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_snd_3333_);
lean_inc(v_fst_3332_);
lean_dec(v_fst_3330_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3353_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; double v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v_toMonadFileMap_3342_; lean_object* v_getFileName_3343_; lean_object* v_logMessage_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_float_of_nat(v___x_3322_);
v___x_3340_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_3341_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3341_, 0, v___x_3337_);
lean_ctor_set(v___x_3341_, 1, v___x_3338_);
lean_ctor_set(v___x_3341_, 2, v___x_3340_);
lean_ctor_set_float(v___x_3341_, sizeof(void*)*3, v___x_3339_);
lean_ctor_set_float(v___x_3341_, sizeof(void*)*3 + 8, v___x_3339_);
lean_ctor_set_uint8(v___x_3341_, sizeof(void*)*3 + 16, v___x_3323_);
v_toMonadFileMap_3342_ = lean_ctor_get(v_inst_3324_, 0);
lean_inc(v_toMonadFileMap_3342_);
v_getFileName_3343_ = lean_ctor_get(v_inst_3324_, 2);
lean_inc(v_getFileName_3343_);
v_logMessage_3344_ = lean_ctor_get(v_inst_3324_, 4);
lean_inc(v_logMessage_3344_);
lean_dec_ref(v_inst_3324_);
v___x_3345_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_3346_ = l_Lean_MessageData_nil;
v___x_3347_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3341_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
lean_ctor_set(v___x_3347_, 2, v_snd_3331_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set_tag(v___x_3335_, 8);
lean_ctor_set(v___x_3335_, 1, v___x_3347_);
lean_ctor_set(v___x_3335_, 0, v___x_3345_);
v___x_3349_ = v___x_3335_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3345_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___f_3350_; lean_object* v___x_3351_; 
lean_inc(v_toBind_3325_);
v___f_3350_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__5), 8, 7);
lean_closure_set(v___f_3350_, 0, v___x_3349_);
lean_closure_set(v___f_3350_, 1, v_fst_3332_);
lean_closure_set(v___f_3350_, 2, v_snd_3333_);
lean_closure_set(v___f_3350_, 3, v_logMessage_3344_);
lean_closure_set(v___f_3350_, 4, v_toBind_3325_);
lean_closure_set(v___f_3350_, 5, v___f_3326_);
lean_closure_set(v___f_3350_, 6, v_toMonadFileMap_3342_);
v___x_3351_ = lean_apply_4(v_toBind_3325_, lean_box(0), lean_box(0), v_getFileName_3343_, v___f_3350_);
return v___x_3351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object* v___x_3354_, lean_object* v___x_3355_, lean_object* v_inst_3356_, lean_object* v_toBind_3357_, lean_object* v___f_3358_, lean_object* v_a_3359_, lean_object* v_x_3360_, lean_object* v___y_3361_){
_start:
{
uint8_t v___x_1915__boxed_3362_; lean_object* v_res_3363_; 
v___x_1915__boxed_3362_ = lean_unbox(v___x_3355_);
v_res_3363_ = l_Lean_addTraceAsMessages___redArg___lam__6(v___x_3354_, v___x_1915__boxed_3362_, v_inst_3356_, v_toBind_3357_, v___f_3358_, v_a_3359_, v_x_3360_, v___y_3361_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object* v___x_3364_, lean_object* v___f_3365_, lean_object* v_acc_3366_, lean_object* v_l_3367_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_3364_, v___f_3365_, v_acc_3366_, v_l_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object* v_toApplicative_3369_, uint8_t v___x_3370_, lean_object* v_inst_3371_, lean_object* v_toBind_3372_, lean_object* v_inst_3373_, lean_object* v___f_3374_, lean_object* v___f_3375_, lean_object* v___f_3376_, lean_object* v_____s_3377_){
_start:
{
lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3404_; lean_object* v_size_3411_; lean_object* v_buckets_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; 
v_size_3411_ = lean_ctor_get(v_____s_3377_, 0);
lean_inc(v_size_3411_);
v_buckets_3412_ = lean_ctor_get(v_____s_3377_, 1);
lean_inc_ref(v_buckets_3412_);
lean_dec_ref(v_____s_3377_);
v___x_3413_ = lean_mk_empty_array_with_capacity(v_size_3411_);
lean_dec(v_size_3411_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v___x_3415_ = lean_unsigned_to_nat(0u);
v___x_3416_ = lean_array_get_size(v_buckets_3412_);
v___x_3417_ = lean_nat_dec_lt(v___x_3415_, v___x_3416_);
if (v___x_3417_ == 0)
{
lean_dec_ref(v_buckets_3412_);
lean_dec_ref(v___f_3376_);
v___y_3404_ = v___x_3413_;
goto v___jp_3403_;
}
else
{
lean_object* v___f_3418_; uint8_t v___x_3419_; 
v___f_3418_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__7), 4, 2);
lean_closure_set(v___f_3418_, 0, v___x_3414_);
lean_closure_set(v___f_3418_, 1, v___f_3376_);
v___x_3419_ = lean_nat_dec_le(v___x_3416_, v___x_3416_);
if (v___x_3419_ == 0)
{
if (v___x_3417_ == 0)
{
lean_dec_ref(v___f_3418_);
lean_dec_ref(v_buckets_3412_);
v___y_3404_ = v___x_3413_;
goto v___jp_3403_;
}
else
{
size_t v___x_3420_; size_t v___x_3421_; lean_object* v___x_3422_; 
v___x_3420_ = ((size_t)0ULL);
v___x_3421_ = lean_usize_of_nat(v___x_3416_);
v___x_3422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3414_, v___f_3418_, v_buckets_3412_, v___x_3420_, v___x_3421_, v___x_3413_);
v___y_3404_ = v___x_3422_;
goto v___jp_3403_;
}
}
else
{
size_t v___x_3423_; size_t v___x_3424_; lean_object* v___x_3425_; 
v___x_3423_ = ((size_t)0ULL);
v___x_3424_ = lean_usize_of_nat(v___x_3416_);
v___x_3425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3414_, v___f_3418_, v_buckets_3412_, v___x_3423_, v___x_3424_, v___x_3413_);
v___y_3404_ = v___x_3425_;
goto v___jp_3403_;
}
}
v___jp_3378_:
{
lean_object* v___x_3381_; lean_object* v___f_3382_; lean_object* v___x_3383_; lean_object* v___f_3384_; size_t v_sz_3385_; size_t v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3381_ = lean_box(0);
v___f_3382_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3382_, 0, v_toApplicative_3369_);
lean_closure_set(v___f_3382_, 1, v___x_3381_);
v___x_3383_ = lean_box(v___x_3370_);
lean_inc(v_toBind_3372_);
v___f_3384_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__6___boxed), 8, 5);
lean_closure_set(v___f_3384_, 0, v___y_3379_);
lean_closure_set(v___f_3384_, 1, v___x_3383_);
lean_closure_set(v___f_3384_, 2, v_inst_3371_);
lean_closure_set(v___f_3384_, 3, v_toBind_3372_);
lean_closure_set(v___f_3384_, 4, v___f_3382_);
v_sz_3385_ = lean_array_size(v___y_3380_);
v___x_3386_ = ((size_t)0ULL);
v___x_3387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3373_, v___y_3380_, v___f_3384_, v_sz_3385_, v___x_3386_, v___x_3381_);
v___x_3388_ = lean_apply_4(v_toBind_3372_, lean_box(0), lean_box(0), v___x_3387_, v___f_3374_);
return v___x_3388_;
}
v___jp_3389_:
{
lean_object* v___x_3395_; 
v___x_3395_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_3375_, v___y_3392_, v___y_3393_, v___y_3391_, v___y_3394_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_3394_);
lean_dec(v___y_3392_);
v___y_3379_ = v___y_3390_;
v___y_3380_ = v___x_3395_;
goto v___jp_3378_;
}
v___jp_3396_:
{
uint8_t v___x_3402_; 
v___x_3402_ = lean_nat_dec_le(v___y_3401_, v___y_3399_);
if (v___x_3402_ == 0)
{
lean_dec(v___y_3399_);
lean_inc(v___y_3401_);
v___y_3390_ = v___y_3397_;
v___y_3391_ = v___y_3401_;
v___y_3392_ = v___y_3398_;
v___y_3393_ = v___y_3400_;
v___y_3394_ = v___y_3401_;
goto v___jp_3389_;
}
else
{
v___y_3390_ = v___y_3397_;
v___y_3391_ = v___y_3401_;
v___y_3392_ = v___y_3398_;
v___y_3393_ = v___y_3400_;
v___y_3394_ = v___y_3399_;
goto v___jp_3389_;
}
}
v___jp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3405_ = lean_unsigned_to_nat(0u);
v___x_3406_ = lean_array_get_size(v___y_3404_);
v___x_3407_ = lean_nat_dec_eq(v___x_3406_, v___x_3405_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
v___x_3408_ = lean_unsigned_to_nat(1u);
v___x_3409_ = lean_nat_sub(v___x_3406_, v___x_3408_);
v___x_3410_ = lean_nat_dec_le(v___x_3405_, v___x_3409_);
if (v___x_3410_ == 0)
{
lean_inc(v___x_3409_);
v___y_3397_ = v___x_3405_;
v___y_3398_ = v___x_3406_;
v___y_3399_ = v___x_3409_;
v___y_3400_ = v___y_3404_;
v___y_3401_ = v___x_3409_;
goto v___jp_3396_;
}
else
{
v___y_3397_ = v___x_3405_;
v___y_3398_ = v___x_3406_;
v___y_3399_ = v___x_3409_;
v___y_3400_ = v___y_3404_;
v___y_3401_ = v___x_3405_;
goto v___jp_3396_;
}
}
else
{
lean_dec_ref(v___f_3375_);
v___y_3379_ = v___x_3405_;
v___y_3380_ = v___y_3404_;
goto v___jp_3378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object* v_toApplicative_3426_, lean_object* v___x_3427_, lean_object* v_inst_3428_, lean_object* v_toBind_3429_, lean_object* v_inst_3430_, lean_object* v___f_3431_, lean_object* v___f_3432_, lean_object* v___f_3433_, lean_object* v_____s_3434_){
_start:
{
uint8_t v___x_2003__boxed_3435_; lean_object* v_res_3436_; 
v___x_2003__boxed_3435_ = lean_unbox(v___x_3427_);
v_res_3436_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_toApplicative_3426_, v___x_2003__boxed_3435_, v_inst_3428_, v_toBind_3429_, v_inst_3430_, v___f_3431_, v___f_3432_, v___f_3433_, v_____s_3434_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object* v_traceElem_3437_, lean_object* v_toApplicative_3438_, lean_object* v___f_3439_, lean_object* v___f_3440_, lean_object* v_____s_3441_, uint8_t v___x_3442_, lean_object* v_____do__lift_3443_){
_start:
{
lean_object* v_ref_3444_; lean_object* v_msg_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3470_; 
v_ref_3444_ = lean_ctor_get(v_traceElem_3437_, 0);
v_msg_3445_ = lean_ctor_get(v_traceElem_3437_, 1);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_traceElem_3437_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3447_ = v_traceElem_3437_;
v_isShared_3448_ = v_isSharedCheck_3470_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_msg_3445_);
lean_inc(v_ref_3444_);
lean_dec(v_traceElem_3437_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3470_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v_ref_3462_; lean_object* v___y_3464_; lean_object* v___x_3467_; 
v_ref_3462_ = l_Lean_replaceRef(v_ref_3444_, v_____do__lift_3443_);
lean_dec(v_ref_3444_);
v___x_3467_ = l_Lean_Syntax_getPos_x3f(v_ref_3462_, v___x_3442_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3468_; 
v___x_3468_ = lean_unsigned_to_nat(0u);
v___y_3464_ = v___x_3468_;
goto v___jp_3463_;
}
else
{
lean_object* v_val_3469_; 
v_val_3469_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_val_3469_);
lean_dec_ref(v___x_3467_);
v___y_3464_ = v_val_3469_;
goto v___jp_3463_;
}
v___jp_3449_:
{
lean_object* v_toPure_3452_; lean_object* v___x_3454_; 
v_toPure_3452_ = lean_ctor_get(v_toApplicative_3438_, 1);
lean_inc(v_toPure_3452_);
lean_dec_ref(v_toApplicative_3438_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 1, v___y_3451_);
lean_ctor_set(v___x_3447_, 0, v___y_3450_);
v___x_3454_ = v___x_3447_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___y_3450_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v___y_3451_);
v___x_3454_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v_pos2traces_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3455_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
lean_inc_ref(v___x_3454_);
lean_inc_ref(v___f_3440_);
lean_inc_ref(v___f_3439_);
v___x_3456_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_3439_, v___f_3440_, v_____s_3441_, v___x_3454_, v___x_3455_);
v___x_3457_ = lean_array_push(v___x_3456_, v_msg_3445_);
v_pos2traces_3458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3439_, v___f_3440_, v_____s_3441_, v___x_3454_, v___x_3457_);
v___x_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3459_, 0, v_pos2traces_3458_);
v___x_3460_ = lean_apply_2(v_toPure_3452_, lean_box(0), v___x_3459_);
return v___x_3460_;
}
}
v___jp_3463_:
{
lean_object* v___x_3465_; 
v___x_3465_ = l_Lean_Syntax_getTailPos_x3f(v_ref_3462_, v___x_3442_);
lean_dec(v_ref_3462_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_inc(v___y_3464_);
v___y_3450_ = v___y_3464_;
v___y_3451_ = v___y_3464_;
goto v___jp_3449_;
}
else
{
lean_object* v_val_3466_; 
v_val_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_val_3466_);
lean_dec_ref(v___x_3465_);
v___y_3450_ = v___y_3464_;
v___y_3451_ = v_val_3466_;
goto v___jp_3449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object* v_traceElem_3471_, lean_object* v_toApplicative_3472_, lean_object* v___f_3473_, lean_object* v___f_3474_, lean_object* v_____s_3475_, lean_object* v___x_3476_, lean_object* v_____do__lift_3477_){
_start:
{
uint8_t v___x_2128__boxed_3478_; lean_object* v_res_3479_; 
v___x_2128__boxed_3478_ = lean_unbox(v___x_3476_);
v_res_3479_ = l_Lean_addTraceAsMessages___redArg___lam__9(v_traceElem_3471_, v_toApplicative_3472_, v___f_3473_, v___f_3474_, v_____s_3475_, v___x_2128__boxed_3478_, v_____do__lift_3477_);
lean_dec(v_____do__lift_3477_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object* v_inst_3480_, lean_object* v_toApplicative_3481_, lean_object* v___f_3482_, lean_object* v___f_3483_, uint8_t v___x_3484_, lean_object* v_toBind_3485_, lean_object* v_traceElem_3486_, lean_object* v_____s_3487_){
_start:
{
lean_object* v_getRef_3488_; lean_object* v___x_3489_; lean_object* v___f_3490_; lean_object* v___x_3491_; 
v_getRef_3488_ = lean_ctor_get(v_inst_3480_, 0);
lean_inc(v_getRef_3488_);
lean_dec_ref(v_inst_3480_);
v___x_3489_ = lean_box(v___x_3484_);
v___f_3490_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_3490_, 0, v_traceElem_3486_);
lean_closure_set(v___f_3490_, 1, v_toApplicative_3481_);
lean_closure_set(v___f_3490_, 2, v___f_3482_);
lean_closure_set(v___f_3490_, 3, v___f_3483_);
lean_closure_set(v___f_3490_, 4, v_____s_3487_);
lean_closure_set(v___f_3490_, 5, v___x_3489_);
v___x_3491_ = lean_apply_4(v_toBind_3485_, lean_box(0), lean_box(0), v_getRef_3488_, v___f_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object* v_inst_3492_, lean_object* v_toApplicative_3493_, lean_object* v___f_3494_, lean_object* v___f_3495_, lean_object* v___x_3496_, lean_object* v_toBind_3497_, lean_object* v_traceElem_3498_, lean_object* v_____s_3499_){
_start:
{
uint8_t v___x_2188__boxed_3500_; lean_object* v_res_3501_; 
v___x_2188__boxed_3500_ = lean_unbox(v___x_3496_);
v_res_3501_ = l_Lean_addTraceAsMessages___redArg___lam__10(v_inst_3492_, v_toApplicative_3493_, v___f_3494_, v___f_3495_, v___x_2188__boxed_3500_, v_toBind_3497_, v_traceElem_3498_, v_____s_3499_);
return v_res_3501_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___f_3503_; 
v___x_3502_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_3503_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3503_, 0, v___x_3502_);
return v___f_3503_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___f_3504_; lean_object* v___f_3505_; 
v___f_3504_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__0, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0);
v___f_3505_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3505_, 0, v___f_3504_);
lean_closure_set(v___f_3505_, 1, v___f_3504_);
return v___f_3505_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = lean_box(0);
v___x_3510_ = lean_unsigned_to_nat(16u);
v___x_3511_ = lean_mk_array(v___x_3510_, v___x_3509_);
return v___x_3511_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v_pos2traces_3514_; 
v___x_3512_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__4, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4);
v___x_3513_ = lean_unsigned_to_nat(0u);
v_pos2traces_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_3514_, 0, v___x_3513_);
lean_ctor_set(v_pos2traces_3514_, 1, v___x_3512_);
return v_pos2traces_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11(lean_object* v_inst_3515_, lean_object* v_toApplicative_3516_, lean_object* v_toBind_3517_, lean_object* v_inst_3518_, lean_object* v___f_3519_, lean_object* v_traces_3520_){
_start:
{
uint8_t v___x_3521_; 
v___x_3521_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_3520_);
if (v___x_3521_ == 0)
{
lean_object* v___f_3522_; lean_object* v___f_3523_; lean_object* v___x_3524_; lean_object* v___f_3525_; lean_object* v_pos2traces_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___f_3522_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__1, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1);
v___f_3523_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___lam__11___closed__3));
v___x_3524_ = lean_box(v___x_3521_);
lean_inc(v_toBind_3517_);
v___f_3525_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3525_, 0, v_inst_3515_);
lean_closure_set(v___f_3525_, 1, v_toApplicative_3516_);
lean_closure_set(v___f_3525_, 2, v___f_3522_);
lean_closure_set(v___f_3525_, 3, v___f_3523_);
lean_closure_set(v___f_3525_, 4, v___x_3524_);
lean_closure_set(v___f_3525_, 5, v_toBind_3517_);
v_pos2traces_3526_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__5, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5);
v___x_3527_ = l_Lean_PersistentArray_forIn___redArg(v_inst_3518_, v_traces_3520_, v_pos2traces_3526_, v___f_3525_);
v___x_3528_ = lean_apply_4(v_toBind_3517_, lean_box(0), lean_box(0), v___x_3527_, v___f_3519_);
return v___x_3528_;
}
else
{
lean_object* v_toPure_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_dec_ref(v_traces_3520_);
lean_dec(v___f_3519_);
lean_dec_ref(v_inst_3518_);
lean_dec(v_toBind_3517_);
lean_dec_ref(v_inst_3515_);
v_toPure_3529_ = lean_ctor_get(v_toApplicative_3516_, 1);
lean_inc(v_toPure_3529_);
lean_dec_ref(v_toApplicative_3516_);
v___x_3530_ = lean_box(0);
v___x_3531_ = lean_apply_2(v_toPure_3529_, lean_box(0), v___x_3530_);
return v___x_3531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12(lean_object* v___x_3532_, lean_object* v_toApplicative_3533_, lean_object* v_inst_3534_, lean_object* v_toBind_3535_, lean_object* v_inst_3536_, lean_object* v___f_3537_, lean_object* v___f_3538_, lean_object* v___f_3539_, lean_object* v_inst_3540_, lean_object* v_inst_3541_, lean_object* v_____do__lift_3542_){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = l_Lean_trace_profiler_output;
v___x_3544_ = l_Lean_Option_get_x3f___redArg(v___x_3532_, v_____do__lift_3542_, v___x_3543_);
if (lean_obj_tag(v___x_3544_) == 0)
{
uint8_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___f_3547_; lean_object* v___f_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3545_ = 1;
v___x_3546_ = lean_box(v___x_3545_);
lean_inc_ref_n(v_inst_3536_, 2);
lean_inc_n(v_toBind_3535_, 2);
lean_inc_ref(v_toApplicative_3533_);
v___f_3547_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__8___boxed), 9, 8);
lean_closure_set(v___f_3547_, 0, v_toApplicative_3533_);
lean_closure_set(v___f_3547_, 1, v___x_3546_);
lean_closure_set(v___f_3547_, 2, v_inst_3534_);
lean_closure_set(v___f_3547_, 3, v_toBind_3535_);
lean_closure_set(v___f_3547_, 4, v_inst_3536_);
lean_closure_set(v___f_3547_, 5, v___f_3537_);
lean_closure_set(v___f_3547_, 6, v___f_3538_);
lean_closure_set(v___f_3547_, 7, v___f_3539_);
v___f_3548_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__11), 6, 5);
lean_closure_set(v___f_3548_, 0, v_inst_3540_);
lean_closure_set(v___f_3548_, 1, v_toApplicative_3533_);
lean_closure_set(v___f_3548_, 2, v_toBind_3535_);
lean_closure_set(v___f_3548_, 3, v_inst_3536_);
lean_closure_set(v___f_3548_, 4, v___f_3547_);
v___x_3549_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3536_, v_inst_3541_);
v___x_3550_ = lean_apply_4(v_toBind_3535_, lean_box(0), lean_box(0), v___x_3549_, v___f_3548_);
return v___x_3550_;
}
else
{
lean_object* v_toPure_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
lean_dec_ref(v___x_3544_);
lean_dec_ref(v_inst_3541_);
lean_dec_ref(v_inst_3540_);
lean_dec_ref(v___f_3539_);
lean_dec_ref(v___f_3538_);
lean_dec(v___f_3537_);
lean_dec_ref(v_inst_3536_);
lean_dec(v_toBind_3535_);
lean_dec_ref(v_inst_3534_);
v_toPure_3551_ = lean_ctor_get(v_toApplicative_3533_, 1);
lean_inc(v_toPure_3551_);
lean_dec_ref(v_toApplicative_3533_);
v___x_3552_ = lean_box(0);
v___x_3553_ = lean_apply_2(v_toPure_3551_, lean_box(0), v___x_3552_);
return v___x_3553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12___boxed(lean_object* v___x_3554_, lean_object* v_toApplicative_3555_, lean_object* v_inst_3556_, lean_object* v_toBind_3557_, lean_object* v_inst_3558_, lean_object* v___f_3559_, lean_object* v___f_3560_, lean_object* v___f_3561_, lean_object* v_inst_3562_, lean_object* v_inst_3563_, lean_object* v_____do__lift_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_addTraceAsMessages___redArg___lam__12(v___x_3554_, v_toApplicative_3555_, v_inst_3556_, v_toBind_3557_, v_inst_3558_, v___f_3559_, v___f_3560_, v___f_3561_, v_inst_3562_, v_inst_3563_, v_____do__lift_3564_);
lean_dec_ref(v_____do__lift_3564_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object* v_inst_3568_, lean_object* v_inst_3569_, lean_object* v_inst_3570_, lean_object* v_inst_3571_, lean_object* v_inst_3572_){
_start:
{
lean_object* v___x_3573_; lean_object* v_toApplicative_3574_; lean_object* v_toBind_3575_; lean_object* v___f_3576_; lean_object* v___f_3577_; lean_object* v___f_3578_; lean_object* v___f_3579_; lean_object* v___x_3580_; 
v___x_3573_ = l_Lean_KVMap_instValueString;
v_toApplicative_3574_ = lean_ctor_get(v_inst_3569_, 0);
lean_inc_ref_n(v_toApplicative_3574_, 2);
v_toBind_3575_ = lean_ctor_get(v_inst_3569_, 1);
lean_inc_n(v_toBind_3575_, 2);
v___f_3576_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3576_, 0, v_toApplicative_3574_);
v___f_3577_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__0));
v___f_3578_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__1));
v___f_3579_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3579_, 0, v___x_3573_);
lean_closure_set(v___f_3579_, 1, v_toApplicative_3574_);
lean_closure_set(v___f_3579_, 2, v_inst_3571_);
lean_closure_set(v___f_3579_, 3, v_toBind_3575_);
lean_closure_set(v___f_3579_, 4, v_inst_3569_);
lean_closure_set(v___f_3579_, 5, v___f_3576_);
lean_closure_set(v___f_3579_, 6, v___f_3577_);
lean_closure_set(v___f_3579_, 7, v___f_3578_);
lean_closure_set(v___f_3579_, 8, v_inst_3570_);
lean_closure_set(v___f_3579_, 9, v_inst_3572_);
v___x_3580_ = lean_apply_4(v_toBind_3575_, lean_box(0), lean_box(0), v_inst_3568_, v___f_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object* v_m_3581_, lean_object* v_inst_3582_, lean_object* v_inst_3583_, lean_object* v_inst_3584_, lean_object* v_inst_3585_, lean_object* v_inst_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_addTraceAsMessages___redArg(v_inst_3582_, v_inst_3583_, v_inst_3584_, v_inst_3585_, v_inst_3586_);
return v___x_3587_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = lean_unsigned_to_nat(2826257906u);
v___x_3630_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3631_ = l_Lean_Name_num___override(v___x_3630_, v___x_3629_);
return v___x_3631_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3634_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3635_ = l_Lean_Name_str___override(v___x_3634_, v___x_3633_);
return v___x_3635_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3637_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3638_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3639_ = l_Lean_Name_str___override(v___x_3638_, v___x_3637_);
return v___x_3639_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = lean_unsigned_to_nat(2u);
v___x_3641_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3642_ = l_Lean_Name_num___override(v___x_3641_, v___x_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3644_; uint8_t v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3644_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3645_ = 0;
v___x_3646_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3647_ = l_Lean_registerTraceClass(v___x_3644_, v___x_3645_, v___x_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object* v_a_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
return v_res_3649_;
}
}
lean_object* runtime_initialize_Lean_Elab_Exception(uint8_t builtin);
lean_object* runtime_initialize_Lean_Log(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Trace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedTraceElem_default = _init_l_Lean_instInhabitedTraceElem_default();
lean_mark_persistent(l_Lean_instInhabitedTraceElem_default);
l_Lean_instInhabitedTraceElem = _init_l_Lean_instInhabitedTraceElem();
lean_mark_persistent(l_Lean_instInhabitedTraceElem);
l_Lean_instInhabitedTraceState_default = _init_l_Lean_instInhabitedTraceState_default();
lean_mark_persistent(l_Lean_instInhabitedTraceState_default);
l_Lean_instInhabitedTraceState = _init_l_Lean_instInhabitedTraceState();
lean_mark_persistent(l_Lean_instInhabitedTraceState);
res = l_Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_inheritedTraceOptions = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_inheritedTraceOptions);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_threshold);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_useHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_useHeartbeats);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_output = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_output);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_output_pp = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_output_pp);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_Trace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_MonadTrace_getInheritedTraceOptions___autoParam = _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam();
lean_mark_persistent(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam);
l_Lean_registerTraceClass___auto__1 = _init_l_Lean_registerTraceClass___auto__1();
lean_mark_persistent(l_Lean_registerTraceClass___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Exception(uint8_t builtin);
lean_object* initialize_Lean_Log(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Trace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Trace(builtin);
}
#ifdef __cplusplus
}
#endif
