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
lean_object* l_Lean_MonadCacheT_instMonadExceptOf___redArg(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEST(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_format___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BaseIO_toIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value)}};
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
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value)}};
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
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value)}};
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
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addTrace___redArg___lam__0___closed__1_value),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value)}};
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
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value)}};
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
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cls"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value),LEAN_SCALAR_PTR_LITERAL(28, 113, 141, 155, 240, 79, 69, 244)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__21_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__24_value),LEAN_SCALAR_PTR_LITERAL(55, 147, 210, 58, 86, 191, 41, 151)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__26_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__28_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__34_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "liftMethod"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37_value),LEAN_SCALAR_PTR_LITERAL(217, 228, 135, 132, 46, 84, 105, 88)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.isTracingEnabledFor"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "isTracingEnabledFor"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__44_value),LEAN_SCALAR_PTR_LITERAL(121, 60, 144, 254, 33, 118, 155, 122)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__50_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.addTrace"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "addTrace"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__54_value),LEAN_SCALAR_PTR_LITERAL(183, 216, 39, 175, 140, 178, 201, 238)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value_aux_1),((lean_object*)&l_Lean_registerTraceClass___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__60_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MessageData"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value),LEAN_SCALAR_PTR_LITERAL(117, 193, 162, 252, 67, 31, 191, 159)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63_value),LEAN_SCALAR_PTR_LITERAL(204, 233, 154, 112, 39, 152, 210, 6)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__68 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__68_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__68_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__69 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__69_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__69_value)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__70 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__70_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__71 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__71_value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__72_value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__71_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__72 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__72_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__73 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__73_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__5___boxed(lean_object**);
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
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___closed__3;
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
lean_inc(v_inst_108_);
v___f_116_ = lean_alloc_closure((void*)(l_Lean_instMonadTraceOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_116_, 0, v_modifyTraceState_110_);
lean_closure_set(v___f_116_, 1, v_inst_108_);
lean_inc(v_inst_108_);
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
lean_inc(v_toBind_159_);
lean_inc(v_inst_158_);
v___f_166_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_166_, 0, v___f_157_);
lean_closure_set(v___f_166_, 1, v_inst_158_);
lean_closure_set(v___f_166_, 2, v_toBind_159_);
lean_closure_set(v___f_166_, 3, v___f_165_);
lean_inc(v_toBind_159_);
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
lean_inc(v_toBind_175_);
v_getTraceState_176_ = lean_ctor_get(v_inst_172_, 1);
lean_inc(v_getTraceState_176_);
lean_dec_ref(v_inst_172_);
v_toPure_177_ = lean_ctor_get(v_toApplicative_174_, 1);
lean_inc(v_toPure_177_);
v___f_178_ = ((lean_object*)(l_Lean_printTraces___redArg___closed__0));
lean_inc(v_toPure_177_);
v___f_179_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_179_, 0, v_toPure_177_);
lean_inc(v_toBind_175_);
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
lean_inc(v_toBind_328_);
lean_dec_ref(v_inst_323_);
v_getInheritedTraceOptions_329_ = lean_ctor_get(v_inst_324_, 2);
lean_inc(v_getInheritedTraceOptions_329_);
lean_dec_ref(v_inst_324_);
v_toPure_330_ = lean_ctor_get(v_toApplicative_327_, 1);
lean_inc(v_toPure_330_);
lean_dec_ref(v_toApplicative_327_);
lean_inc(v_toBind_328_);
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
lean_object* v___x_338_; 
v___x_338_ = l_Lean_isTracingEnabledFor___redArg(v_inst_334_, v_inst_335_, v_inst_336_, v_cls_337_);
return v___x_338_;
}
}
LEAN_EXPORT uint8_t lean_is_trace_class_enabled(lean_object* v_opts_339_, lean_object* v_cls_340_){
_start:
{
uint8_t v_hasTrace_342_; 
v_hasTrace_342_ = lean_ctor_get_uint8(v_opts_339_, sizeof(void*)*1);
if (v_hasTrace_342_ == 0)
{
lean_dec(v_cls_340_);
lean_dec_ref(v_opts_339_);
return v_hasTrace_342_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_343_ = l_Lean_inheritedTraceOptions;
v___x_344_ = lean_st_ref_get(v___x_343_);
v___x_345_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_346_ = l_Lean_Name_append(v___x_345_, v_cls_340_);
v___x_347_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_344_, v_opts_339_, v___x_346_);
lean_dec(v___x_346_);
lean_dec_ref(v_opts_339_);
lean_dec(v___x_344_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object* v_opts_348_, lean_object* v_cls_349_, lean_object* v_a_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = lean_is_trace_class_enabled(v_opts_348_, v_cls_349_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object* v_toPure_353_, lean_object* v_s_354_){
_start:
{
lean_object* v_traces_355_; lean_object* v___x_356_; 
v_traces_355_ = lean_ctor_get(v_s_354_, 0);
lean_inc_ref(v_traces_355_);
lean_dec_ref(v_s_354_);
v___x_356_ = lean_apply_2(v_toPure_353_, lean_box(0), v_traces_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object* v_inst_357_, lean_object* v_inst_358_){
_start:
{
lean_object* v_toApplicative_359_; lean_object* v_toBind_360_; lean_object* v_getTraceState_361_; lean_object* v_toPure_362_; lean_object* v___f_363_; lean_object* v___x_364_; 
v_toApplicative_359_ = lean_ctor_get(v_inst_357_, 0);
lean_inc_ref(v_toApplicative_359_);
v_toBind_360_ = lean_ctor_get(v_inst_357_, 1);
lean_inc(v_toBind_360_);
lean_dec_ref(v_inst_357_);
v_getTraceState_361_ = lean_ctor_get(v_inst_358_, 1);
lean_inc(v_getTraceState_361_);
lean_dec_ref(v_inst_358_);
v_toPure_362_ = lean_ctor_get(v_toApplicative_359_, 1);
lean_inc(v_toPure_362_);
lean_dec_ref(v_toApplicative_359_);
v___f_363_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_363_, 0, v_toPure_362_);
v___x_364_ = lean_apply_4(v_toBind_360_, lean_box(0), lean_box(0), v_getTraceState_361_, v___f_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object* v_m_365_, lean_object* v_inst_366_, lean_object* v_inst_367_){
_start:
{
lean_object* v_toApplicative_368_; lean_object* v_toBind_369_; lean_object* v_getTraceState_370_; lean_object* v_toPure_371_; lean_object* v___f_372_; lean_object* v___x_373_; 
v_toApplicative_368_ = lean_ctor_get(v_inst_366_, 0);
lean_inc_ref(v_toApplicative_368_);
v_toBind_369_ = lean_ctor_get(v_inst_366_, 1);
lean_inc(v_toBind_369_);
lean_dec_ref(v_inst_366_);
v_getTraceState_370_ = lean_ctor_get(v_inst_367_, 1);
lean_inc(v_getTraceState_370_);
lean_dec_ref(v_inst_367_);
v_toPure_371_ = lean_ctor_get(v_toApplicative_368_, 1);
lean_inc(v_toPure_371_);
lean_dec_ref(v_toApplicative_368_);
v___f_372_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_372_, 0, v_toPure_371_);
v___x_373_ = lean_apply_4(v_toBind_369_, lean_box(0), lean_box(0), v_getTraceState_370_, v___f_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object* v_f_374_, lean_object* v_s_375_){
_start:
{
uint64_t v_tid_376_; lean_object* v_traces_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_385_; 
v_tid_376_ = lean_ctor_get_uint64(v_s_375_, sizeof(void*)*1);
v_traces_377_ = lean_ctor_get(v_s_375_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_s_375_);
if (v_isSharedCheck_385_ == 0)
{
v___x_379_ = v_s_375_;
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_traces_377_);
lean_dec(v_s_375_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = lean_apply_1(v_f_374_, v_traces_377_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
lean_ctor_set_uint64(v_reuseFailAlloc_384_, sizeof(void*)*1, v_tid_376_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object* v_inst_386_, lean_object* v_f_387_){
_start:
{
lean_object* v_modifyTraceState_388_; lean_object* v___f_389_; lean_object* v___x_390_; 
v_modifyTraceState_388_ = lean_ctor_get(v_inst_386_, 0);
lean_inc(v_modifyTraceState_388_);
lean_dec_ref(v_inst_386_);
v___f_389_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_389_, 0, v_f_387_);
v___x_390_ = lean_apply_1(v_modifyTraceState_388_, v___f_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object* v_m_391_, lean_object* v_inst_392_, lean_object* v_f_393_){
_start:
{
lean_object* v_modifyTraceState_394_; lean_object* v___f_395_; lean_object* v___x_396_; 
v_modifyTraceState_394_ = lean_ctor_get(v_inst_392_, 0);
lean_inc(v_modifyTraceState_394_);
lean_dec_ref(v_inst_392_);
v___f_395_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_395_, 0, v_f_393_);
v___x_396_ = lean_apply_1(v_modifyTraceState_394_, v___f_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object* v_s_397_, lean_object* v_x_398_){
_start:
{
lean_inc_ref(v_s_397_);
return v_s_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object* v_s_399_, lean_object* v_x_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_setTraceState___redArg___lam__0(v_s_399_, v_x_400_);
lean_dec_ref(v_x_400_);
lean_dec_ref(v_s_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object* v_inst_402_, lean_object* v_s_403_){
_start:
{
lean_object* v_modifyTraceState_404_; lean_object* v___f_405_; lean_object* v___x_406_; 
v_modifyTraceState_404_ = lean_ctor_get(v_inst_402_, 0);
lean_inc(v_modifyTraceState_404_);
lean_dec_ref(v_inst_402_);
v___f_405_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_405_, 0, v_s_403_);
v___x_406_ = lean_apply_1(v_modifyTraceState_404_, v___f_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object* v_m_407_, lean_object* v_inst_408_, lean_object* v_s_409_){
_start:
{
lean_object* v_modifyTraceState_410_; lean_object* v___f_411_; lean_object* v___x_412_; 
v_modifyTraceState_410_ = lean_ctor_get(v_inst_408_, 0);
lean_inc(v_modifyTraceState_410_);
lean_dec_ref(v_inst_408_);
v___f_411_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_411_, 0, v_s_409_);
v___x_412_ = lean_apply_1(v_modifyTraceState_410_, v___f_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object* v_s_413_){
_start:
{
uint64_t v_tid_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_424_; 
v_tid_414_ = lean_ctor_get_uint64(v_s_413_, sizeof(void*)*1);
v_isSharedCheck_424_ = !lean_is_exclusive(v_s_413_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_s_413_, 0);
lean_dec(v_unused_425_);
v___x_416_ = v_s_413_;
v_isShared_417_ = v_isSharedCheck_424_;
goto v_resetjp_415_;
}
else
{
lean_dec(v_s_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_424_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_418_ = lean_unsigned_to_nat(32u);
v___x_419_ = lean_mk_empty_array_with_capacity(v___x_418_);
lean_dec_ref(v___x_419_);
v___x_420_ = lean_obj_once(&l_Lean_resetTraceState___redArg___lam__0___closed__1, &l_Lean_resetTraceState___redArg___lam__0___closed__1_once, _init_l_Lean_resetTraceState___redArg___lam__0___closed__1);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_420_);
v___x_422_ = v___x_416_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
lean_ctor_set_uint64(v_reuseFailAlloc_423_, sizeof(void*)*1, v_tid_414_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object* v_toPure_426_, lean_object* v_oldTraces_427_, lean_object* v_____r_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_apply_2(v_toPure_426_, lean_box(0), v_oldTraces_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object* v_toPure_430_, lean_object* v_modifyTraceState_431_, lean_object* v___f_432_, lean_object* v_toBind_433_, lean_object* v_oldTraces_434_){
_start:
{
lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___f_435_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_435_, 0, v_toPure_430_);
lean_closure_set(v___f_435_, 1, v_oldTraces_434_);
v___x_436_ = lean_apply_1(v_modifyTraceState_431_, v___f_432_);
v___x_437_ = lean_apply_4(v_toBind_433_, lean_box(0), lean_box(0), v___x_436_, v___f_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object* v_inst_439_, lean_object* v_inst_440_){
_start:
{
lean_object* v_toApplicative_441_; lean_object* v_toBind_442_; lean_object* v_modifyTraceState_443_; lean_object* v_getTraceState_444_; lean_object* v_toPure_445_; lean_object* v___f_446_; lean_object* v___f_447_; lean_object* v___f_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_toApplicative_441_ = lean_ctor_get(v_inst_439_, 0);
lean_inc_ref(v_toApplicative_441_);
v_toBind_442_ = lean_ctor_get(v_inst_439_, 1);
lean_inc(v_toBind_442_);
lean_dec_ref(v_inst_439_);
v_modifyTraceState_443_ = lean_ctor_get(v_inst_440_, 0);
lean_inc(v_modifyTraceState_443_);
v_getTraceState_444_ = lean_ctor_get(v_inst_440_, 1);
lean_inc(v_getTraceState_444_);
lean_dec_ref(v_inst_440_);
v_toPure_445_ = lean_ctor_get(v_toApplicative_441_, 1);
lean_inc(v_toPure_445_);
lean_dec_ref(v_toApplicative_441_);
v___f_446_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0));
lean_inc(v_toBind_442_);
lean_inc(v_toPure_445_);
v___f_447_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_447_, 0, v_toPure_445_);
lean_closure_set(v___f_447_, 1, v_modifyTraceState_443_);
lean_closure_set(v___f_447_, 2, v___f_446_);
lean_closure_set(v___f_447_, 3, v_toBind_442_);
v___f_448_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_448_, 0, v_toPure_445_);
lean_inc(v_toBind_442_);
v___x_449_ = lean_apply_4(v_toBind_442_, lean_box(0), lean_box(0), v_getTraceState_444_, v___f_448_);
v___x_450_ = lean_apply_4(v_toBind_442_, lean_box(0), lean_box(0), v___x_449_, v___f_447_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object* v_m_451_, lean_object* v_inst_452_, lean_object* v_inst_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_452_, v_inst_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object* v_ref_455_, lean_object* v_msg_456_, lean_object* v_s_457_){
_start:
{
uint64_t v_tid_458_; lean_object* v_traces_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_468_; 
v_tid_458_ = lean_ctor_get_uint64(v_s_457_, sizeof(void*)*1);
v_traces_459_ = lean_ctor_get(v_s_457_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_s_457_);
if (v_isSharedCheck_468_ == 0)
{
v___x_461_ = v_s_457_;
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_traces_459_);
lean_dec(v_s_457_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_ref_455_);
lean_ctor_set(v___x_463_, 1, v_msg_456_);
v___x_464_ = l_Lean_PersistentArray_push___redArg(v_traces_459_, v___x_463_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_464_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
lean_ctor_set_uint64(v_reuseFailAlloc_467_, sizeof(void*)*1, v_tid_458_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object* v_inst_469_, lean_object* v_ref_470_, lean_object* v_msg_471_){
_start:
{
lean_object* v_modifyTraceState_472_; lean_object* v___f_473_; lean_object* v___x_474_; 
v_modifyTraceState_472_ = lean_ctor_get(v_inst_469_, 0);
lean_inc(v_modifyTraceState_472_);
lean_dec_ref(v_inst_469_);
v___f_473_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__0), 3, 2);
lean_closure_set(v___f_473_, 0, v_ref_470_);
lean_closure_set(v___f_473_, 1, v_msg_471_);
v___x_474_ = lean_apply_1(v_modifyTraceState_472_, v___f_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_msg_477_, lean_object* v_toBind_478_, lean_object* v_ref_479_){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___f_480_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__1), 3, 2);
lean_closure_set(v___f_480_, 0, v_inst_475_);
lean_closure_set(v___f_480_, 1, v_ref_479_);
v___x_481_ = lean_apply_1(v_inst_476_, v_msg_477_);
v___x_482_ = lean_apply_4(v_toBind_478_, lean_box(0), lean_box(0), v___x_481_, v___f_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_msg_487_){
_start:
{
lean_object* v_toBind_488_; lean_object* v_getRef_489_; lean_object* v___f_490_; lean_object* v___x_491_; 
v_toBind_488_ = lean_ctor_get(v_inst_483_, 1);
lean_inc(v_toBind_488_);
lean_dec_ref(v_inst_483_);
v_getRef_489_ = lean_ctor_get(v_inst_485_, 0);
lean_inc(v_getRef_489_);
lean_dec_ref(v_inst_485_);
lean_inc(v_toBind_488_);
v___f_490_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__2), 5, 4);
lean_closure_set(v___f_490_, 0, v_inst_484_);
lean_closure_set(v___f_490_, 1, v_inst_486_);
lean_closure_set(v___f_490_, 2, v_msg_487_);
lean_closure_set(v___f_490_, 3, v_toBind_488_);
v___x_491_ = lean_apply_4(v_toBind_488_, lean_box(0), lean_box(0), v_getRef_489_, v___f_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object* v_m_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_msg_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_addRawTrace___redArg(v_inst_493_, v_inst_494_, v_inst_495_, v_inst_496_, v_msg_497_);
return v___x_498_;
}
}
static double _init_l_Lean_addTrace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_499_; double v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_float_of_nat(v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object* v_cls_504_, lean_object* v_msg_505_, lean_object* v_ref_506_, lean_object* v_s_507_){
_start:
{
uint64_t v_tid_508_; lean_object* v_traces_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_525_; 
v_tid_508_ = lean_ctor_get_uint64(v_s_507_, sizeof(void*)*1);
v_traces_509_ = lean_ctor_get(v_s_507_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v_s_507_);
if (v_isSharedCheck_525_ == 0)
{
v___x_511_ = v_s_507_;
v_isShared_512_ = v_isSharedCheck_525_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_traces_509_);
lean_dec(v_s_507_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_525_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; double v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_513_ = lean_box(0);
v___x_514_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
v___x_515_ = 0;
v___x_516_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_517_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_517_, 0, v_cls_504_);
lean_ctor_set(v___x_517_, 1, v___x_513_);
lean_ctor_set(v___x_517_, 2, v___x_516_);
lean_ctor_set_float(v___x_517_, sizeof(void*)*3, v___x_514_);
lean_ctor_set_float(v___x_517_, sizeof(void*)*3 + 8, v___x_514_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*3 + 16, v___x_515_);
v___x_518_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
v___x_519_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v_msg_505_);
lean_ctor_set(v___x_519_, 2, v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v_ref_506_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = l_Lean_PersistentArray_push___redArg(v_traces_509_, v___x_520_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_521_);
v___x_523_ = v___x_511_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
lean_ctor_set_uint64(v_reuseFailAlloc_524_, sizeof(void*)*1, v_tid_508_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object* v_inst_526_, lean_object* v_cls_527_, lean_object* v_ref_528_, lean_object* v_msg_529_){
_start:
{
lean_object* v_modifyTraceState_530_; lean_object* v___f_531_; lean_object* v___x_532_; 
v_modifyTraceState_530_ = lean_ctor_get(v_inst_526_, 0);
lean_inc(v_modifyTraceState_530_);
lean_dec_ref(v_inst_526_);
v___f_531_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_531_, 0, v_cls_527_);
lean_closure_set(v___f_531_, 1, v_msg_529_);
lean_closure_set(v___f_531_, 2, v_ref_528_);
v___x_532_ = lean_apply_1(v_modifyTraceState_530_, v___f_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object* v_inst_533_, lean_object* v_cls_534_, lean_object* v_inst_535_, lean_object* v_msg_536_, lean_object* v_toBind_537_, lean_object* v_ref_538_){
_start:
{
lean_object* v___f_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___f_539_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__1), 4, 3);
lean_closure_set(v___f_539_, 0, v_inst_533_);
lean_closure_set(v___f_539_, 1, v_cls_534_);
lean_closure_set(v___f_539_, 2, v_ref_538_);
v___x_540_ = lean_apply_1(v_inst_535_, v_msg_536_);
v___x_541_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_540_, v___f_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_cls_546_, lean_object* v_msg_547_){
_start:
{
lean_object* v_toBind_548_; lean_object* v_getRef_549_; lean_object* v___f_550_; lean_object* v___x_551_; 
v_toBind_548_ = lean_ctor_get(v_inst_542_, 1);
lean_inc(v_toBind_548_);
lean_dec_ref(v_inst_542_);
v_getRef_549_ = lean_ctor_get(v_inst_544_, 0);
lean_inc(v_getRef_549_);
lean_dec_ref(v_inst_544_);
lean_inc(v_toBind_548_);
v___f_550_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__2), 6, 5);
lean_closure_set(v___f_550_, 0, v_inst_543_);
lean_closure_set(v___f_550_, 1, v_cls_546_);
lean_closure_set(v___f_550_, 2, v_inst_545_);
lean_closure_set(v___f_550_, 3, v_msg_547_);
lean_closure_set(v___f_550_, 4, v_toBind_548_);
v___x_551_ = lean_apply_4(v_toBind_548_, lean_box(0), lean_box(0), v_getRef_549_, v___f_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object* v_m_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_cls_557_, lean_object* v_msg_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_addTrace___redArg(v_inst_553_, v_inst_554_, v_inst_555_, v_inst_556_, v_cls_557_, v_msg_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0(lean_object* v_toApplicative_560_, lean_object* v_msg_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_cls_566_, uint8_t v_____do__lift_567_){
_start:
{
if (v_____do__lift_567_ == 0)
{
lean_object* v_toPure_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_cls_566_);
lean_dec(v_inst_565_);
lean_dec_ref(v_inst_564_);
lean_dec_ref(v_inst_563_);
lean_dec_ref(v_inst_562_);
lean_dec_ref(v_msg_561_);
v_toPure_568_ = lean_ctor_get(v_toApplicative_560_, 1);
lean_inc(v_toPure_568_);
lean_dec_ref(v_toApplicative_560_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_apply_2(v_toPure_568_, lean_box(0), v___x_569_);
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec_ref(v_toApplicative_560_);
v___x_571_ = lean_box(0);
v___x_572_ = lean_apply_1(v_msg_561_, v___x_571_);
v___x_573_ = l_Lean_addTrace___redArg(v_inst_562_, v_inst_563_, v_inst_564_, v_inst_565_, v_cls_566_, v___x_572_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object* v_toApplicative_574_, lean_object* v_msg_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_cls_580_, lean_object* v_____do__lift_581_){
_start:
{
uint8_t v_____do__lift_92__boxed_582_; lean_object* v_res_583_; 
v_____do__lift_92__boxed_582_ = lean_unbox(v_____do__lift_581_);
v_res_583_ = l_Lean_trace___redArg___lam__0(v_toApplicative_574_, v_msg_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_inst_579_, v_cls_580_, v_____do__lift_92__boxed_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_cls_589_, lean_object* v_msg_590_){
_start:
{
lean_object* v_toApplicative_591_; lean_object* v_toBind_592_; lean_object* v___f_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_toApplicative_591_ = lean_ctor_get(v_inst_584_, 0);
v_toBind_592_ = lean_ctor_get(v_inst_584_, 1);
lean_inc(v_toBind_592_);
lean_inc(v_cls_589_);
lean_inc_ref(v_inst_585_);
lean_inc_ref(v_inst_584_);
lean_inc_ref(v_toApplicative_591_);
v___f_593_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_593_, 0, v_toApplicative_591_);
lean_closure_set(v___f_593_, 1, v_msg_590_);
lean_closure_set(v___f_593_, 2, v_inst_584_);
lean_closure_set(v___f_593_, 3, v_inst_585_);
lean_closure_set(v___f_593_, 4, v_inst_586_);
lean_closure_set(v___f_593_, 5, v_inst_587_);
lean_closure_set(v___f_593_, 6, v_cls_589_);
v___x_594_ = l_Lean_isTracingEnabledFor___redArg(v_inst_584_, v_inst_585_, v_inst_588_, v_cls_589_);
v___x_595_ = lean_apply_4(v_toBind_592_, lean_box(0), lean_box(0), v___x_594_, v___f_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace(lean_object* v_m_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_cls_602_, lean_object* v_msg_603_){
_start:
{
lean_object* v_toApplicative_604_; lean_object* v_toBind_605_; lean_object* v___f_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_toApplicative_604_ = lean_ctor_get(v_inst_597_, 0);
v_toBind_605_ = lean_ctor_get(v_inst_597_, 1);
lean_inc(v_toBind_605_);
lean_inc(v_cls_602_);
lean_inc_ref(v_inst_598_);
lean_inc_ref(v_inst_597_);
lean_inc_ref(v_toApplicative_604_);
v___f_606_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_606_, 0, v_toApplicative_604_);
lean_closure_set(v___f_606_, 1, v_msg_603_);
lean_closure_set(v___f_606_, 2, v_inst_597_);
lean_closure_set(v___f_606_, 3, v_inst_598_);
lean_closure_set(v___f_606_, 4, v_inst_599_);
lean_closure_set(v___f_606_, 5, v_inst_600_);
lean_closure_set(v___f_606_, 6, v_cls_602_);
v___x_607_ = l_Lean_isTracingEnabledFor___redArg(v_inst_597_, v_inst_598_, v_inst_601_, v_cls_602_);
v___x_608_ = lean_apply_4(v_toBind_605_, lean_box(0), lean_box(0), v___x_607_, v___f_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_cls_613_, lean_object* v_msg_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_addTrace___redArg(v_inst_609_, v_inst_610_, v_inst_611_, v_inst_612_, v_cls_613_, v_msg_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1(lean_object* v_toApplicative_616_, lean_object* v_toBind_617_, lean_object* v_mkMsg_618_, lean_object* v___f_619_, uint8_t v_____do__lift_620_){
_start:
{
if (v_____do__lift_620_ == 0)
{
lean_object* v_toPure_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec(v___f_619_);
lean_dec(v_mkMsg_618_);
lean_dec(v_toBind_617_);
v_toPure_621_ = lean_ctor_get(v_toApplicative_616_, 1);
lean_inc(v_toPure_621_);
lean_dec_ref(v_toApplicative_616_);
v___x_622_ = lean_box(0);
v___x_623_ = lean_apply_2(v_toPure_621_, lean_box(0), v___x_622_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; 
lean_dec_ref(v_toApplicative_616_);
v___x_624_ = lean_apply_4(v_toBind_617_, lean_box(0), lean_box(0), v_mkMsg_618_, v___f_619_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object* v_toApplicative_625_, lean_object* v_toBind_626_, lean_object* v_mkMsg_627_, lean_object* v___f_628_, lean_object* v_____do__lift_629_){
_start:
{
uint8_t v_____do__lift_98__boxed_630_; lean_object* v_res_631_; 
v_____do__lift_98__boxed_630_ = lean_unbox(v_____do__lift_629_);
v_res_631_ = l_Lean_traceM___redArg___lam__1(v_toApplicative_625_, v_toBind_626_, v_mkMsg_627_, v___f_628_, v_____do__lift_98__boxed_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_cls_637_, lean_object* v_mkMsg_638_){
_start:
{
lean_object* v_toApplicative_639_; lean_object* v_toBind_640_; lean_object* v___f_641_; lean_object* v___f_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_toApplicative_639_ = lean_ctor_get(v_inst_632_, 0);
v_toBind_640_ = lean_ctor_get(v_inst_632_, 1);
lean_inc(v_toBind_640_);
lean_inc(v_cls_637_);
lean_inc_ref(v_inst_633_);
lean_inc_ref(v_inst_632_);
v___f_641_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_641_, 0, v_inst_632_);
lean_closure_set(v___f_641_, 1, v_inst_633_);
lean_closure_set(v___f_641_, 2, v_inst_634_);
lean_closure_set(v___f_641_, 3, v_inst_635_);
lean_closure_set(v___f_641_, 4, v_cls_637_);
lean_inc(v_toBind_640_);
lean_inc_ref(v_toApplicative_639_);
v___f_642_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_642_, 0, v_toApplicative_639_);
lean_closure_set(v___f_642_, 1, v_toBind_640_);
lean_closure_set(v___f_642_, 2, v_mkMsg_638_);
lean_closure_set(v___f_642_, 3, v___f_641_);
v___x_643_ = l_Lean_isTracingEnabledFor___redArg(v_inst_632_, v_inst_633_, v_inst_636_, v_cls_637_);
v___x_644_ = lean_apply_4(v_toBind_640_, lean_box(0), lean_box(0), v___x_643_, v___f_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object* v_m_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_cls_651_, lean_object* v_mkMsg_652_){
_start:
{
lean_object* v_toApplicative_653_; lean_object* v_toBind_654_; lean_object* v___f_655_; lean_object* v___f_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_toApplicative_653_ = lean_ctor_get(v_inst_646_, 0);
v_toBind_654_ = lean_ctor_get(v_inst_646_, 1);
lean_inc(v_toBind_654_);
lean_inc(v_cls_651_);
lean_inc_ref(v_inst_647_);
lean_inc_ref(v_inst_646_);
v___f_655_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_655_, 0, v_inst_646_);
lean_closure_set(v___f_655_, 1, v_inst_647_);
lean_closure_set(v___f_655_, 2, v_inst_648_);
lean_closure_set(v___f_655_, 3, v_inst_649_);
lean_closure_set(v___f_655_, 4, v_cls_651_);
lean_inc(v_toBind_654_);
lean_inc_ref(v_toApplicative_653_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_656_, 0, v_toApplicative_653_);
lean_closure_set(v___f_656_, 1, v_toBind_654_);
lean_closure_set(v___f_656_, 2, v_mkMsg_652_);
lean_closure_set(v___f_656_, 3, v___f_655_);
v___x_657_ = l_Lean_isTracingEnabledFor___redArg(v_inst_646_, v_inst_647_, v_inst_650_, v_cls_651_);
v___x_658_ = lean_apply_4(v_toBind_654_, lean_box(0), lean_box(0), v___x_657_, v___f_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object* v_x_659_){
_start:
{
lean_object* v_msg_660_; 
v_msg_660_ = lean_ctor_get(v_x_659_, 1);
lean_inc_ref(v_msg_660_);
return v_msg_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object* v_x_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_661_);
lean_dec_ref(v_x_661_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object* v_ref_663_, lean_object* v_msg_664_, lean_object* v_oldTraces_665_, lean_object* v_s_666_){
_start:
{
uint64_t v_tid_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_676_; 
v_tid_667_ = lean_ctor_get_uint64(v_s_666_, sizeof(void*)*1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_s_666_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v_s_666_, 0);
lean_dec(v_unused_677_);
v___x_669_ = v_s_666_;
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_s_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_676_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_ref_663_);
lean_ctor_set(v___x_671_, 1, v_msg_664_);
v___x_672_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_665_, v___x_671_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_672_);
v___x_674_ = v___x_669_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
lean_ctor_set_uint64(v_reuseFailAlloc_675_, sizeof(void*)*1, v_tid_667_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object* v_ref_678_, lean_object* v_oldTraces_679_, lean_object* v_modifyTraceState_680_, lean_object* v_msg_681_){
_start:
{
lean_object* v___f_682_; lean_object* v___x_683_; 
v___f_682_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0), 4, 3);
lean_closure_set(v___f_682_, 0, v_ref_678_);
lean_closure_set(v___f_682_, 1, v_msg_681_);
lean_closure_set(v___f_682_, 2, v_oldTraces_679_);
v___x_683_ = lean_apply_1(v_modifyTraceState_680_, v___f_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object* v___f_703_, lean_object* v_data_704_, lean_object* v_msg_705_, lean_object* v_inst_706_, lean_object* v_toBind_707_, lean_object* v___f_708_, lean_object* v_____do__lift_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; size_t v_sz_712_; size_t v___x_713_; lean_object* v___x_714_; lean_object* v_msg_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_710_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_709_);
v___x_711_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v_sz_712_ = lean_array_size(v___x_710_);
v___x_713_ = ((size_t)0ULL);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_711_, v___f_703_, v_sz_712_, v___x_713_, v___x_710_);
v_msg_715_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_715_, 0, v_data_704_);
lean_ctor_set(v_msg_715_, 1, v_msg_705_);
lean_ctor_set(v_msg_715_, 2, v___x_714_);
v___x_716_ = lean_apply_1(v_inst_706_, v_msg_715_);
v___x_717_ = lean_apply_4(v_toBind_707_, lean_box(0), lean_box(0), v___x_716_, v___f_708_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object* v___f_718_, lean_object* v_data_719_, lean_object* v_msg_720_, lean_object* v_inst_721_, lean_object* v_toBind_722_, lean_object* v___f_723_, lean_object* v_____do__lift_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(v___f_718_, v_data_719_, v_msg_720_, v_inst_721_, v_toBind_722_, v___f_723_, v_____do__lift_724_);
lean_dec_ref(v_____do__lift_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object* v_ref_726_, lean_object* v_withRef_727_, lean_object* v___x_728_, lean_object* v_oldRef_729_){
_start:
{
lean_object* v_ref_730_; lean_object* v___x_731_; 
v_ref_730_ = l_Lean_replaceRef(v_ref_726_, v_oldRef_729_);
v___x_731_ = lean_apply_3(v_withRef_727_, lean_box(0), v_ref_730_, v___x_728_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object* v_ref_732_, lean_object* v_withRef_733_, lean_object* v___x_734_, lean_object* v_oldRef_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(v_ref_732_, v_withRef_733_, v___x_734_, v_oldRef_735_);
lean_dec(v_oldRef_735_);
lean_dec(v_ref_732_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_oldTraces_742_, lean_object* v_data_743_, lean_object* v_ref_744_, lean_object* v_msg_745_){
_start:
{
lean_object* v_toApplicative_746_; lean_object* v_toBind_747_; lean_object* v_modifyTraceState_748_; lean_object* v_getTraceState_749_; lean_object* v_toPure_750_; lean_object* v_getRef_751_; lean_object* v_withRef_752_; lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___f_757_; lean_object* v___x_758_; lean_object* v___f_759_; lean_object* v___x_760_; 
v_toApplicative_746_ = lean_ctor_get(v_inst_738_, 0);
lean_inc_ref(v_toApplicative_746_);
v_toBind_747_ = lean_ctor_get(v_inst_738_, 1);
lean_inc(v_toBind_747_);
lean_dec_ref(v_inst_738_);
v_modifyTraceState_748_ = lean_ctor_get(v_inst_739_, 0);
lean_inc(v_modifyTraceState_748_);
v_getTraceState_749_ = lean_ctor_get(v_inst_739_, 1);
lean_inc(v_getTraceState_749_);
lean_dec_ref(v_inst_739_);
v_toPure_750_ = lean_ctor_get(v_toApplicative_746_, 1);
lean_inc(v_toPure_750_);
lean_dec_ref(v_toApplicative_746_);
v_getRef_751_ = lean_ctor_get(v_inst_740_, 0);
lean_inc(v_getRef_751_);
v_withRef_752_ = lean_ctor_get(v_inst_740_, 1);
lean_inc(v_withRef_752_);
lean_dec_ref(v_inst_740_);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_753_, 0, v_toPure_750_);
lean_inc(v_toBind_747_);
v___x_754_ = lean_apply_4(v_toBind_747_, lean_box(0), lean_box(0), v_getTraceState_749_, v___f_753_);
v___f_755_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0));
lean_inc(v_ref_744_);
v___f_756_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2), 4, 3);
lean_closure_set(v___f_756_, 0, v_ref_744_);
lean_closure_set(v___f_756_, 1, v_oldTraces_742_);
lean_closure_set(v___f_756_, 2, v_modifyTraceState_748_);
lean_inc(v_toBind_747_);
v___f_757_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_757_, 0, v___f_755_);
lean_closure_set(v___f_757_, 1, v_data_743_);
lean_closure_set(v___f_757_, 2, v_msg_745_);
lean_closure_set(v___f_757_, 3, v_inst_741_);
lean_closure_set(v___f_757_, 4, v_toBind_747_);
lean_closure_set(v___f_757_, 5, v___f_756_);
lean_inc(v_toBind_747_);
v___x_758_ = lean_apply_4(v_toBind_747_, lean_box(0), lean_box(0), v___x_754_, v___f_757_);
v___f_759_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_759_, 0, v_ref_744_);
lean_closure_set(v___f_759_, 1, v_withRef_752_);
lean_closure_set(v___f_759_, 2, v___x_758_);
v___x_760_ = lean_apply_4(v_toBind_747_, lean_box(0), lean_box(0), v_getRef_751_, v___f_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object* v_m_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_oldTraces_766_, lean_object* v_data_767_, lean_object* v_ref_768_, lean_object* v_msg_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_762_, v_inst_763_, v_inst_764_, v_inst_765_, v_oldTraces_766_, v_data_767_, v_ref_768_, v_msg_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object* v_name_771_, lean_object* v_decl_772_, lean_object* v_ref_773_){
_start:
{
lean_object* v_defValue_775_; lean_object* v_descr_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_803_; 
v_defValue_775_ = lean_ctor_get(v_decl_772_, 0);
v_descr_776_ = lean_ctor_get(v_decl_772_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_decl_772_);
if (v_isSharedCheck_803_ == 0)
{
v___x_778_ = v_decl_772_;
v_isShared_779_ = v_isSharedCheck_803_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_descr_776_);
lean_inc(v_defValue_775_);
lean_dec(v_decl_772_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_803_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = lean_alloc_ctor(1, 0, 1);
v___x_781_ = lean_unbox(v_defValue_775_);
lean_ctor_set_uint8(v___x_780_, 0, v___x_781_);
lean_inc(v_name_771_);
v___x_782_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_782_, 0, v_name_771_);
lean_ctor_set(v___x_782_, 1, v_ref_773_);
lean_ctor_set(v___x_782_, 2, v___x_780_);
lean_ctor_set(v___x_782_, 3, v_descr_776_);
lean_inc(v_name_771_);
v___x_783_ = lean_register_option(v_name_771_, v___x_782_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_793_; 
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v___x_783_, 0);
lean_dec(v_unused_794_);
v___x_785_ = v___x_783_;
v_isShared_786_ = v_isSharedCheck_793_;
goto v_resetjp_784_;
}
else
{
lean_dec(v___x_783_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_793_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_defValue_775_);
lean_ctor_set(v___x_778_, 0, v_name_771_);
v___x_788_ = v___x_778_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_name_771_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_defValue_775_);
v___x_788_ = v_reuseFailAlloc_792_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_788_);
v___x_790_ = v___x_785_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_del_object(v___x_778_);
lean_dec(v_defValue_775_);
lean_dec(v_name_771_);
v_a_795_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_783_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_783_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_804_, lean_object* v_decl_805_, lean_object* v_ref_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_804_, v_decl_805_, v_ref_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_823_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_824_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_825_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_826_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_823_, v___x_824_, v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object* v_name_829_, lean_object* v_decl_830_, lean_object* v_ref_831_){
_start:
{
lean_object* v_defValue_833_; lean_object* v_descr_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_860_; 
v_defValue_833_ = lean_ctor_get(v_decl_830_, 0);
v_descr_834_ = lean_ctor_get(v_decl_830_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_decl_830_);
if (v_isSharedCheck_860_ == 0)
{
v___x_836_ = v_decl_830_;
v_isShared_837_ = v_isSharedCheck_860_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_descr_834_);
lean_inc(v_defValue_833_);
lean_dec(v_decl_830_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_860_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_inc(v_defValue_833_);
v___x_838_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_838_, 0, v_defValue_833_);
lean_inc(v_name_829_);
v___x_839_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_839_, 0, v_name_829_);
lean_ctor_set(v___x_839_, 1, v_ref_831_);
lean_ctor_set(v___x_839_, 2, v___x_838_);
lean_ctor_set(v___x_839_, 3, v_descr_834_);
lean_inc(v_name_829_);
v___x_840_ = lean_register_option(v_name_829_, v___x_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_850_; 
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v___x_840_, 0);
lean_dec(v_unused_851_);
v___x_842_ = v___x_840_;
v_isShared_843_ = v_isSharedCheck_850_;
goto v_resetjp_841_;
}
else
{
lean_dec(v___x_840_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_850_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_defValue_833_);
lean_ctor_set(v___x_836_, 0, v_name_829_);
v___x_845_ = v___x_836_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_name_829_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_defValue_833_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_845_);
v___x_847_ = v___x_842_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_del_object(v___x_836_);
lean_dec(v_defValue_833_);
lean_dec(v_name_829_);
v_a_852_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_840_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_840_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_861_, lean_object* v_decl_862_, lean_object* v_ref_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_861_, v_decl_862_, v_ref_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_881_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_882_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_883_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_884_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_881_, v___x_882_, v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_903_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_904_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_905_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_906_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_903_, v___x_904_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object* v_name_909_, lean_object* v_decl_910_, lean_object* v_ref_911_){
_start:
{
lean_object* v_defValue_913_; lean_object* v_descr_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_940_; 
v_defValue_913_ = lean_ctor_get(v_decl_910_, 0);
v_descr_914_ = lean_ctor_get(v_decl_910_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_decl_910_);
if (v_isSharedCheck_940_ == 0)
{
v___x_916_ = v_decl_910_;
v_isShared_917_ = v_isSharedCheck_940_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_descr_914_);
lean_inc(v_defValue_913_);
lean_dec(v_decl_910_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_940_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_inc(v_defValue_913_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v_defValue_913_);
lean_inc(v_name_909_);
v___x_919_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_919_, 0, v_name_909_);
lean_ctor_set(v___x_919_, 1, v_ref_911_);
lean_ctor_set(v___x_919_, 2, v___x_918_);
lean_ctor_set(v___x_919_, 3, v_descr_914_);
lean_inc(v_name_909_);
v___x_920_ = lean_register_option(v_name_909_, v___x_919_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_930_; 
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v___x_920_, 0);
lean_dec(v_unused_931_);
v___x_922_ = v___x_920_;
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
else
{
lean_dec(v___x_920_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v_defValue_913_);
lean_ctor_set(v___x_916_, 0, v_name_909_);
v___x_925_ = v___x_916_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_name_909_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_defValue_913_);
v___x_925_ = v_reuseFailAlloc_929_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_927_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_925_);
v___x_927_ = v___x_922_;
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
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_del_object(v___x_916_);
lean_dec(v_defValue_913_);
lean_dec(v_name_909_);
v_a_932_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_920_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_920_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_941_, lean_object* v_decl_942_, lean_object* v_ref_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_941_, v_decl_942_, v_ref_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_961_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_962_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_963_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_964_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_961_, v___x_962_, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_985_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_986_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_987_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_988_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_985_, v___x_986_, v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
return v_res_990_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_991_; double v___x_992_; 
v___x_991_ = lean_unsigned_to_nat(1000000000u);
v___x_992_ = lean_float_of_nat(v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object* v_toApplicative_993_, lean_object* v_start_994_, lean_object* v_a_995_, lean_object* v_stop_996_){
_start:
{
lean_object* v_toPure_997_; double v___x_998_; double v___x_999_; double v___x_1000_; double v___x_1001_; double v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_toPure_997_ = lean_ctor_get(v_toApplicative_993_, 1);
lean_inc(v_toPure_997_);
lean_dec_ref(v_toApplicative_993_);
v___x_998_ = lean_float_of_nat(v_start_994_);
v___x_999_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1000_ = lean_float_div(v___x_998_, v___x_999_);
v___x_1001_ = lean_float_of_nat(v_stop_996_);
v___x_1002_ = lean_float_div(v___x_1001_, v___x_999_);
v___x_1003_ = lean_box_float(v___x_1000_);
v___x_1004_ = lean_box_float(v___x_1002_);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v_a_995_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = lean_apply_2(v_toPure_997_, lean_box(0), v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object* v_toApplicative_1008_, lean_object* v_start_1009_, lean_object* v_toBind_1010_, lean_object* v___x_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v___f_1013_; lean_object* v___x_1014_; 
v___f_1013_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1013_, 0, v_toApplicative_1008_);
lean_closure_set(v___f_1013_, 1, v_start_1009_);
lean_closure_set(v___f_1013_, 2, v_a_1012_);
v___x_1014_ = lean_apply_4(v_toBind_1010_, lean_box(0), lean_box(0), v___x_1011_, v___f_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object* v_toApplicative_1015_, lean_object* v_toBind_1016_, lean_object* v___x_1017_, lean_object* v_act_1018_, lean_object* v_start_1019_){
_start:
{
lean_object* v___f_1020_; lean_object* v___x_1021_; 
lean_inc(v_toBind_1016_);
v___f_1020_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1020_, 0, v_toApplicative_1015_);
lean_closure_set(v___f_1020_, 1, v_start_1019_);
lean_closure_set(v___f_1020_, 2, v_toBind_1016_);
lean_closure_set(v___f_1020_, 3, v___x_1017_);
v___x_1021_ = lean_apply_4(v_toBind_1016_, lean_box(0), lean_box(0), v_act_1018_, v___f_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object* v_toApplicative_1022_, lean_object* v_start_1023_, lean_object* v_a_1024_, lean_object* v_stop_1025_){
_start:
{
lean_object* v_toPure_1026_; double v___x_1027_; double v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_toPure_1026_ = lean_ctor_get(v_toApplicative_1022_, 1);
lean_inc(v_toPure_1026_);
lean_dec_ref(v_toApplicative_1022_);
v___x_1027_ = lean_float_of_nat(v_start_1023_);
v___x_1028_ = lean_float_of_nat(v_stop_1025_);
v___x_1029_ = lean_box_float(v___x_1027_);
v___x_1030_ = lean_box_float(v___x_1028_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v_a_1024_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_apply_2(v_toPure_1026_, lean_box(0), v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object* v_toApplicative_1034_, lean_object* v_start_1035_, lean_object* v_toBind_1036_, lean_object* v___x_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___f_1039_; lean_object* v___x_1040_; 
v___f_1039_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1039_, 0, v_toApplicative_1034_);
lean_closure_set(v___f_1039_, 1, v_start_1035_);
lean_closure_set(v___f_1039_, 2, v_a_1038_);
v___x_1040_ = lean_apply_4(v_toBind_1036_, lean_box(0), lean_box(0), v___x_1037_, v___f_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object* v_toApplicative_1041_, lean_object* v_toBind_1042_, lean_object* v___x_1043_, lean_object* v_act_1044_, lean_object* v_start_1045_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; 
lean_inc(v_toBind_1042_);
v___f_1046_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1046_, 0, v_toApplicative_1041_);
lean_closure_set(v___f_1046_, 1, v_start_1045_);
lean_closure_set(v___f_1046_, 2, v_toBind_1042_);
lean_closure_set(v___f_1046_, 3, v___x_1043_);
v___x_1047_ = lean_apply_4(v_toBind_1042_, lean_box(0), lean_box(0), v_act_1044_, v___f_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_opts_1052_, lean_object* v_act_1053_){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1054_ = l_Lean_KVMap_instValueBool;
v___x_1055_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1056_ = l_Lean_Option_get___redArg(v___x_1054_, v_opts_1052_, v___x_1055_);
v___x_1057_ = lean_unbox(v___x_1056_);
lean_dec(v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v_toApplicative_1058_; lean_object* v_toBind_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; 
v_toApplicative_1058_ = lean_ctor_get(v_inst_1050_, 0);
lean_inc_ref(v_toApplicative_1058_);
v_toBind_1059_ = lean_ctor_get(v_inst_1050_, 1);
lean_inc(v_toBind_1059_);
lean_dec_ref(v_inst_1050_);
v___x_1060_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1061_ = lean_apply_2(v_inst_1051_, lean_box(0), v___x_1060_);
lean_inc(v___x_1061_);
lean_inc(v_toBind_1059_);
v___f_1062_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1062_, 0, v_toApplicative_1058_);
lean_closure_set(v___f_1062_, 1, v_toBind_1059_);
lean_closure_set(v___f_1062_, 2, v___x_1061_);
lean_closure_set(v___f_1062_, 3, v_act_1053_);
v___x_1063_ = lean_apply_4(v_toBind_1059_, lean_box(0), lean_box(0), v___x_1061_, v___f_1062_);
return v___x_1063_;
}
else
{
lean_object* v_toApplicative_1064_; lean_object* v_toBind_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; 
v_toApplicative_1064_ = lean_ctor_get(v_inst_1050_, 0);
lean_inc_ref(v_toApplicative_1064_);
v_toBind_1065_ = lean_ctor_get(v_inst_1050_, 1);
lean_inc(v_toBind_1065_);
lean_dec_ref(v_inst_1050_);
v___x_1066_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1067_ = lean_apply_2(v_inst_1051_, lean_box(0), v___x_1066_);
lean_inc(v___x_1067_);
lean_inc(v_toBind_1065_);
v___f_1068_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1068_, 0, v_toApplicative_1064_);
lean_closure_set(v___f_1068_, 1, v_toBind_1065_);
lean_closure_set(v___f_1068_, 2, v___x_1067_);
lean_closure_set(v___f_1068_, 3, v_act_1053_);
v___x_1069_ = lean_apply_4(v_toBind_1065_, lean_box(0), lean_box(0), v___x_1067_, v___f_1068_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_opts_1072_, lean_object* v_act_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(v_inst_1070_, v_inst_1071_, v_opts_1072_, v_act_1073_);
lean_dec_ref(v_opts_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object* v_00_u03b1_1075_, lean_object* v_m_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_opts_1079_, lean_object* v_act_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1081_ = l_Lean_KVMap_instValueBool;
v___x_1082_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1083_ = l_Lean_Option_get___redArg(v___x_1081_, v_opts_1079_, v___x_1082_);
v___x_1084_ = lean_unbox(v___x_1083_);
lean_dec(v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v_toApplicative_1085_; lean_object* v_toBind_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___f_1089_; lean_object* v___x_1090_; 
v_toApplicative_1085_ = lean_ctor_get(v_inst_1077_, 0);
lean_inc_ref(v_toApplicative_1085_);
v_toBind_1086_ = lean_ctor_get(v_inst_1077_, 1);
lean_inc(v_toBind_1086_);
lean_dec_ref(v_inst_1077_);
v___x_1087_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1088_ = lean_apply_2(v_inst_1078_, lean_box(0), v___x_1087_);
lean_inc(v___x_1088_);
lean_inc(v_toBind_1086_);
v___f_1089_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1089_, 0, v_toApplicative_1085_);
lean_closure_set(v___f_1089_, 1, v_toBind_1086_);
lean_closure_set(v___f_1089_, 2, v___x_1088_);
lean_closure_set(v___f_1089_, 3, v_act_1080_);
v___x_1090_ = lean_apply_4(v_toBind_1086_, lean_box(0), lean_box(0), v___x_1088_, v___f_1089_);
return v___x_1090_;
}
else
{
lean_object* v_toApplicative_1091_; lean_object* v_toBind_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___f_1095_; lean_object* v___x_1096_; 
v_toApplicative_1091_ = lean_ctor_get(v_inst_1077_, 0);
lean_inc_ref(v_toApplicative_1091_);
v_toBind_1092_ = lean_ctor_get(v_inst_1077_, 1);
lean_inc(v_toBind_1092_);
lean_dec_ref(v_inst_1077_);
v___x_1093_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1094_ = lean_apply_2(v_inst_1078_, lean_box(0), v___x_1093_);
lean_inc(v___x_1094_);
lean_inc(v_toBind_1092_);
v___f_1095_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1095_, 0, v_toApplicative_1091_);
lean_closure_set(v___f_1095_, 1, v_toBind_1092_);
lean_closure_set(v___f_1095_, 2, v___x_1094_);
lean_closure_set(v___f_1095_, 3, v_act_1080_);
v___x_1096_ = lean_apply_4(v_toBind_1092_, lean_box(0), lean_box(0), v___x_1094_, v___f_1095_);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object* v_00_u03b1_1097_, lean_object* v_m_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_opts_1101_, lean_object* v_act_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(v_00_u03b1_1097_, v_m_1098_, v_inst_1099_, v_inst_1100_, v_opts_1101_, v_act_1102_);
lean_dec_ref(v_opts_1101_);
return v_res_1103_;
}
}
static double _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0(void){
_start:
{
lean_object* v___x_1104_; double v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(1000u);
v___x_1105_ = lean_float_of_nat(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object* v_o_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1107_ = l_Lean_KVMap_instValueBool;
v___x_1108_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1109_ = l_Lean_Option_get___redArg(v___x_1107_, v_o_1106_, v___x_1108_);
v___x_1110_ = lean_unbox(v___x_1109_);
lean_dec(v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; double v___x_1114_; double v___x_1115_; double v___x_1116_; 
v___x_1111_ = l_Lean_KVMap_instValueNat;
v___x_1112_ = l_Lean_trace_profiler_threshold;
v___x_1113_ = l_Lean_Option_get___redArg(v___x_1111_, v_o_1106_, v___x_1112_);
v___x_1114_ = lean_float_of_nat(v___x_1113_);
v___x_1115_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1116_ = lean_float_div(v___x_1114_, v___x_1115_);
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; double v___x_1120_; 
v___x_1117_ = l_Lean_KVMap_instValueNat;
v___x_1118_ = l_Lean_trace_profiler_threshold;
v___x_1119_ = l_Lean_Option_get___redArg(v___x_1117_, v_o_1106_, v___x_1118_);
v___x_1120_ = lean_float_of_nat(v___x_1119_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object* v_o_1121_){
_start:
{
double v_res_1122_; lean_object* v_r_1123_; 
v_res_1122_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1121_);
lean_dec_ref(v_o_1121_);
v_r_1123_ = lean_box_float(v_res_1122_);
return v_r_1123_;
}
}
static lean_object* _init_l_Lean_instMonadAlwaysExceptEIO___closed__0(void){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_instMonadExceptOfEST(lean_box(0), lean_box(0));
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object* v_00_u03b5_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___closed__0, &l_Lean_instMonadAlwaysExceptEIO___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___closed__0);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object* v_inst_1127_, lean_object* v_always_1128_){
_start:
{
lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; 
lean_inc_ref(v_always_1128_);
v___f_1129_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1129_, 0, v_always_1128_);
lean_closure_set(v___f_1129_, 1, v_inst_1127_);
v___f_1130_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_1130_, 0, v_always_1128_);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___f_1129_);
lean_ctor_set(v___x_1131_, 1, v___f_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object* v_m_1132_, lean_object* v_inst_1133_, lean_object* v_00_u03b5_1134_, lean_object* v_00_u03c3_1135_, lean_object* v_always_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_1133_, v_always_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object* v_always_1138_){
_start:
{
lean_object* v___f_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; 
lean_inc_ref(v_always_1138_);
v___f_1139_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1139_, 0, v_always_1138_);
v___f_1140_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1140_, 0, v_always_1138_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___f_1139_);
lean_ctor_set(v___x_1141_, 1, v___f_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object* v_m_1142_, lean_object* v_00_u03b5_1143_, lean_object* v_00_u03c9_1144_, lean_object* v_00_u03c3_1145_, lean_object* v_always_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object* v_always_1148_){
_start:
{
lean_object* v___f_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; 
lean_inc_ref(v_always_1148_);
v___f_1149_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1149_, 0, v_always_1148_);
v___f_1150_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1150_, 0, v_always_1148_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___f_1149_);
lean_ctor_set(v___x_1151_, 1, v___f_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object* v_m_1152_, lean_object* v_00_u03b5_1153_, lean_object* v_00_u03c1_1154_, lean_object* v_always_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object* v_always_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_always_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object* v_00_u03b1_1159_, lean_object* v_m_1160_, lean_object* v_00_u03b5_1161_, lean_object* v_00_u03c9_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_always_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_always_1164_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_m_1170_, lean_object* v_00_u03b5_1171_, lean_object* v_00_u03c9_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_always_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_instMonadAlwaysExceptMonadCacheT(v_00_u03b1_1169_, v_m_1170_, v_00_u03b5_1171_, v_00_u03c9_1172_, v_00_u03b2_1173_, v_always_1174_, v_inst_1175_, v_inst_1176_, v_inst_1177_);
lean_dec_ref(v_inst_1177_);
lean_dec_ref(v_inst_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t v_x_1185_){
_start:
{
switch(v_x_1185_)
{
case 0:
{
lean_object* v___x_1186_; 
v___x_1186_ = ((lean_object*)(l_Lean_checkEmoji___closed__0));
return v___x_1186_;
}
case 1:
{
lean_object* v___x_1187_; 
v___x_1187_ = ((lean_object*)(l_Lean_crossEmoji___closed__0));
return v___x_1187_;
}
default: 
{
lean_object* v___x_1188_; 
v___x_1188_ = ((lean_object*)(l_Lean_bombEmoji___closed__0));
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object* v_x_1189_){
_start:
{
uint8_t v_x_31__boxed_1190_; lean_object* v_res_1191_; 
v_x_31__boxed_1190_ = lean_unbox(v_x_1189_);
v_res_1191_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___lam__0(lean_object* v_x_1192_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
uint8_t v___x_1193_; 
v___x_1193_ = 2;
return v___x_1193_;
}
else
{
lean_object* v_a_1194_; uint8_t v___x_1195_; 
v_a_1194_ = lean_ctor_get(v_x_1192_, 0);
v___x_1195_ = lean_unbox(v_a_1194_);
if (v___x_1195_ == 0)
{
uint8_t v___x_1196_; 
v___x_1196_ = 1;
return v___x_1196_;
}
else
{
uint8_t v___x_1197_; 
v___x_1197_ = 0;
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object* v_x_1198_){
_start:
{
uint8_t v_res_1199_; lean_object* v_r_1200_; 
v_res_1199_ = l_Lean_instExceptToTraceResultBool___lam__0(v_x_1198_);
lean_dec_ref(v_x_1198_);
v_r_1200_ = lean_box(v_res_1199_);
return v_r_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object* v_00_u03b5_1202_){
_start:
{
lean_object* v___f_1203_; 
v___f_1203_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___closed__0));
return v___f_1203_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___lam__0(lean_object* v_x_1204_){
_start:
{
if (lean_obj_tag(v_x_1204_) == 0)
{
uint8_t v___x_1205_; 
v___x_1205_ = 2;
return v___x_1205_;
}
else
{
lean_object* v_a_1206_; 
v_a_1206_ = lean_ctor_get(v_x_1204_, 0);
if (lean_obj_tag(v_a_1206_) == 0)
{
uint8_t v___x_1207_; 
v___x_1207_ = 1;
return v___x_1207_;
}
else
{
uint8_t v___x_1208_; 
v___x_1208_ = 0;
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object* v_x_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_Lean_instExceptToTraceResultOption___lam__0(v_x_1209_);
lean_dec_ref(v_x_1209_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object* v_00_u03b1_1213_, lean_object* v_00_u03b5_1214_){
_start:
{
lean_object* v___f_1215_; 
v___f_1215_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___closed__0));
return v___f_1215_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object* v_x_1216_){
_start:
{
if (lean_obj_tag(v_x_1216_) == 0)
{
uint8_t v___x_1217_; 
v___x_1217_ = 2;
return v___x_1217_;
}
else
{
uint8_t v___x_1218_; 
v___x_1218_ = 0;
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object* v_x_1219_){
_start:
{
uint8_t v_res_1220_; lean_object* v_r_1221_; 
v_res_1220_ = l_Lean_instExceptToTraceResult___lam__0(v_x_1219_);
lean_dec_ref(v_x_1219_);
v_r_1221_ = lean_box(v_res_1220_);
return v_r_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object* v_00_u03b1_1223_, lean_object* v_00_u03b5_1224_){
_start:
{
lean_object* v___f_1225_; 
v___f_1225_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
return v___f_1225_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___redArg(lean_object* v_inst_1226_, lean_object* v_e_1227_){
_start:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1228_ = lean_apply_1(v_inst_1226_, v_e_1227_);
v___x_1229_ = lean_unbox(v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___redArg___boxed(lean_object* v_inst_1230_, lean_object* v_e_1231_){
_start:
{
uint8_t v_res_1232_; lean_object* v_r_1233_; 
v_res_1232_ = l_Except_toTraceResult___redArg(v_inst_1230_, v_e_1231_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult(lean_object* v_00_u03b1_1234_, lean_object* v_00_u03b5_1235_, lean_object* v_inst_1236_, lean_object* v_e_1237_){
_start:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = lean_apply_1(v_inst_1236_, v_e_1237_);
v___x_1239_ = lean_unbox(v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___boxed(lean_object* v_00_u03b1_1240_, lean_object* v_00_u03b5_1241_, lean_object* v_inst_1242_, lean_object* v_e_1243_){
_start:
{
uint8_t v_res_1244_; lean_object* v_r_1245_; 
v_res_1244_ = l_Except_toTraceResult(v_00_u03b1_1240_, v_00_u03b5_1241_, v_inst_1242_, v_e_1243_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0));
v___x_1248_ = l_Lean_stringToMessageData(v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object* v_inst_1249_, lean_object* v_x_1250_){
_start:
{
lean_object* v_toApplicative_1251_; lean_object* v_toPure_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_toApplicative_1251_ = lean_ctor_get(v_inst_1249_, 0);
lean_inc_ref(v_toApplicative_1251_);
lean_dec_ref(v_inst_1249_);
v_toPure_1252_ = lean_ctor_get(v_toApplicative_1251_, 1);
lean_inc(v_toPure_1252_);
lean_dec_ref(v_toApplicative_1251_);
v___x_1253_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1);
v___x_1254_ = lean_apply_2(v_toPure_1252_, lean_box(0), v___x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(lean_object* v_inst_1255_, lean_object* v_x_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(v_inst_1255_, v_x_1256_);
lean_dec(v_x_1256_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object* v_oldTraces_1258_, lean_object* v_s_1259_){
_start:
{
uint64_t v_tid_1260_; lean_object* v_traces_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1269_; 
v_tid_1260_ = lean_ctor_get_uint64(v_s_1259_, sizeof(void*)*1);
v_traces_1261_ = lean_ctor_get(v_s_1259_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_s_1259_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1263_ = v_s_1259_;
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_traces_1261_);
lean_dec(v_s_1259_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1258_, v_traces_1261_);
lean_dec_ref(v_traces_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1265_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
lean_ctor_set_uint64(v_reuseFailAlloc_1268_, sizeof(void*)*1, v_tid_1260_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object* v_always_1270_, lean_object* v_inst_1271_, lean_object* v_fst_1272_, lean_object* v_____r_1273_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1270_);
v___x_1275_ = l_MonadExcept_ofExcept___redArg(v_inst_1271_, v___x_1274_, v_fst_1272_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object* v_inst_1276_, lean_object* v___x_1277_, lean_object* v_fst_1278_, lean_object* v_____r_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_MonadExcept_ofExcept___redArg(v_inst_1276_, v___x_1277_, v_fst_1278_);
return v___x_1280_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0));
v___x_1283_ = l_Lean_stringToMessageData(v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object* v_inst_1284_, lean_object* v_fst_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_oldTraces_1290_, lean_object* v_ref_1291_, lean_object* v_toBind_1292_, lean_object* v___f_1293_, lean_object* v_cls_1294_, uint8_t v_collapsed_1295_, lean_object* v_tag_1296_, uint8_t v___x_1297_, double v_fst_1298_, double v_snd_1299_, lean_object* v_m_1300_){
_start:
{
lean_object* v_result_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_m_1307_; lean_object* v_data_1309_; lean_object* v___x_1312_; double v___x_1313_; lean_object* v_data_1314_; 
v_result_1301_ = lean_apply_1(v_inst_1284_, v_fst_1285_);
v___x_1302_ = lean_unbox(v_result_1301_);
v___x_1303_ = l_Lean_TraceResult_toEmoji(v___x_1302_);
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
v___x_1305_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v_m_1307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_m_1307_, 0, v___x_1306_);
lean_ctor_set(v_m_1307_, 1, v_m_1300_);
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_result_1301_);
v___x_1313_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_1296_);
lean_inc_ref(v___x_1312_);
lean_inc(v_cls_1294_);
v_data_1314_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1314_, 0, v_cls_1294_);
lean_ctor_set(v_data_1314_, 1, v___x_1312_);
lean_ctor_set(v_data_1314_, 2, v_tag_1296_);
lean_ctor_set_float(v_data_1314_, sizeof(void*)*3, v___x_1313_);
lean_ctor_set_float(v_data_1314_, sizeof(void*)*3 + 8, v___x_1313_);
lean_ctor_set_uint8(v_data_1314_, sizeof(void*)*3 + 16, v_collapsed_1295_);
if (v___x_1297_ == 0)
{
lean_dec_ref(v___x_1312_);
lean_dec_ref(v_tag_1296_);
lean_dec(v_cls_1294_);
v_data_1309_ = v_data_1314_;
goto v___jp_1308_;
}
else
{
lean_object* v_data_1315_; 
lean_dec_ref(v_data_1314_);
v_data_1315_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1315_, 0, v_cls_1294_);
lean_ctor_set(v_data_1315_, 1, v___x_1312_);
lean_ctor_set(v_data_1315_, 2, v_tag_1296_);
lean_ctor_set_float(v_data_1315_, sizeof(void*)*3, v_fst_1298_);
lean_ctor_set_float(v_data_1315_, sizeof(void*)*3 + 8, v_snd_1299_);
lean_ctor_set_uint8(v_data_1315_, sizeof(void*)*3 + 16, v_collapsed_1295_);
v_data_1309_ = v_data_1315_;
goto v___jp_1308_;
}
v___jp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_1286_, v_inst_1287_, v_inst_1288_, v_inst_1289_, v_oldTraces_1290_, v_data_1309_, v_ref_1291_, v_m_1307_);
v___x_1311_ = lean_apply_4(v_toBind_1292_, lean_box(0), lean_box(0), v___x_1310_, v___f_1293_);
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_1316_ = _args[0];
lean_object* v_fst_1317_ = _args[1];
lean_object* v_inst_1318_ = _args[2];
lean_object* v_inst_1319_ = _args[3];
lean_object* v_inst_1320_ = _args[4];
lean_object* v_inst_1321_ = _args[5];
lean_object* v_oldTraces_1322_ = _args[6];
lean_object* v_ref_1323_ = _args[7];
lean_object* v_toBind_1324_ = _args[8];
lean_object* v___f_1325_ = _args[9];
lean_object* v_cls_1326_ = _args[10];
lean_object* v_collapsed_1327_ = _args[11];
lean_object* v_tag_1328_ = _args[12];
lean_object* v___x_1329_ = _args[13];
lean_object* v_fst_1330_ = _args[14];
lean_object* v_snd_1331_ = _args[15];
lean_object* v_m_1332_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1333_; uint8_t v___x_676__boxed_1334_; double v_fst_677__boxed_1335_; double v_snd_678__boxed_1336_; lean_object* v_res_1337_; 
v_collapsed_boxed_1333_ = lean_unbox(v_collapsed_1327_);
v___x_676__boxed_1334_ = lean_unbox(v___x_1329_);
v_fst_677__boxed_1335_ = lean_unbox_float(v_fst_1330_);
lean_dec_ref(v_fst_1330_);
v_snd_678__boxed_1336_ = lean_unbox_float(v_snd_1331_);
lean_dec_ref(v_snd_1331_);
v_res_1337_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1316_, v_fst_1317_, v_inst_1318_, v_inst_1319_, v_inst_1320_, v_inst_1321_, v_oldTraces_1322_, v_ref_1323_, v_toBind_1324_, v___f_1325_, v_cls_1326_, v_collapsed_boxed_1333_, v_tag_1328_, v___x_676__boxed_1334_, v_fst_677__boxed_1335_, v_snd_678__boxed_1336_, v_m_1332_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(lean_object* v_always_1338_, lean_object* v_inst_1339_, lean_object* v_fst_1340_, lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_oldTraces_1345_, lean_object* v_toBind_1346_, lean_object* v_cls_1347_, uint8_t v_collapsed_1348_, lean_object* v_tag_1349_, uint8_t v___x_1350_, double v_fst_1351_, double v_snd_1352_, lean_object* v_msg_1353_, lean_object* v___f_1354_, lean_object* v_ref_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v_tryCatch_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_inc_ref(v_always_1338_);
v___x_1356_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1338_);
v_tryCatch_1357_ = lean_ctor_get(v_always_1338_, 1);
lean_inc(v_tryCatch_1357_);
lean_dec_ref(v_always_1338_);
lean_inc_ref(v_fst_1340_);
lean_inc_ref(v_inst_1339_);
v___f_1358_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1358_, 0, v_inst_1339_);
lean_closure_set(v___f_1358_, 1, v___x_1356_);
lean_closure_set(v___f_1358_, 2, v_fst_1340_);
v___x_1359_ = lean_box(v_collapsed_1348_);
v___x_1360_ = lean_box(v___x_1350_);
v___x_1361_ = lean_box_float(v_fst_1351_);
v___x_1362_ = lean_box_float(v_snd_1352_);
lean_inc(v_toBind_1346_);
lean_inc_ref(v_fst_1340_);
v___f_1363_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1363_, 0, v_inst_1341_);
lean_closure_set(v___f_1363_, 1, v_fst_1340_);
lean_closure_set(v___f_1363_, 2, v_inst_1339_);
lean_closure_set(v___f_1363_, 3, v_inst_1342_);
lean_closure_set(v___f_1363_, 4, v_inst_1343_);
lean_closure_set(v___f_1363_, 5, v_inst_1344_);
lean_closure_set(v___f_1363_, 6, v_oldTraces_1345_);
lean_closure_set(v___f_1363_, 7, v_ref_1355_);
lean_closure_set(v___f_1363_, 8, v_toBind_1346_);
lean_closure_set(v___f_1363_, 9, v___f_1358_);
lean_closure_set(v___f_1363_, 10, v_cls_1347_);
lean_closure_set(v___f_1363_, 11, v___x_1359_);
lean_closure_set(v___f_1363_, 12, v_tag_1349_);
lean_closure_set(v___f_1363_, 13, v___x_1360_);
lean_closure_set(v___f_1363_, 14, v___x_1361_);
lean_closure_set(v___f_1363_, 15, v___x_1362_);
v___x_1364_ = lean_apply_1(v_msg_1353_, v_fst_1340_);
v___x_1365_ = lean_apply_3(v_tryCatch_1357_, lean_box(0), v___x_1364_, v___f_1354_);
v___x_1366_ = lean_apply_4(v_toBind_1346_, lean_box(0), lean_box(0), v___x_1365_, v___f_1363_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_always_1367_ = _args[0];
lean_object* v_inst_1368_ = _args[1];
lean_object* v_fst_1369_ = _args[2];
lean_object* v_inst_1370_ = _args[3];
lean_object* v_inst_1371_ = _args[4];
lean_object* v_inst_1372_ = _args[5];
lean_object* v_inst_1373_ = _args[6];
lean_object* v_oldTraces_1374_ = _args[7];
lean_object* v_toBind_1375_ = _args[8];
lean_object* v_cls_1376_ = _args[9];
lean_object* v_collapsed_1377_ = _args[10];
lean_object* v_tag_1378_ = _args[11];
lean_object* v___x_1379_ = _args[12];
lean_object* v_fst_1380_ = _args[13];
lean_object* v_snd_1381_ = _args[14];
lean_object* v_msg_1382_ = _args[15];
lean_object* v___f_1383_ = _args[16];
lean_object* v_ref_1384_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_1385_; uint8_t v___x_728__boxed_1386_; double v_fst_729__boxed_1387_; double v_snd_730__boxed_1388_; lean_object* v_res_1389_; 
v_collapsed_boxed_1385_ = lean_unbox(v_collapsed_1377_);
v___x_728__boxed_1386_ = lean_unbox(v___x_1379_);
v_fst_729__boxed_1387_ = lean_unbox_float(v_fst_1380_);
lean_dec_ref(v_fst_1380_);
v_snd_730__boxed_1388_ = lean_unbox_float(v_snd_1381_);
lean_dec_ref(v_snd_1381_);
v_res_1389_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(v_always_1367_, v_inst_1368_, v_fst_1369_, v_inst_1370_, v_inst_1371_, v_inst_1372_, v_inst_1373_, v_oldTraces_1374_, v_toBind_1375_, v_cls_1376_, v_collapsed_boxed_1385_, v_tag_1378_, v___x_728__boxed_1386_, v_fst_729__boxed_1387_, v_snd_730__boxed_1388_, v_msg_1382_, v___f_1383_, v_ref_1384_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object* v_inst_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_always_1394_, lean_object* v_inst_1395_, lean_object* v_cls_1396_, uint8_t v_collapsed_1397_, lean_object* v_tag_1398_, lean_object* v_opts_1399_, uint8_t v_clsEnabled_1400_, lean_object* v_oldTraces_1401_, lean_object* v_msg_1402_, lean_object* v_resStartStop_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v_snd_1405_; lean_object* v_fst_1406_; lean_object* v_fst_1407_; lean_object* v_snd_1408_; lean_object* v___f_1409_; lean_object* v___f_1410_; lean_object* v___f_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___y_1421_; double v___y_1427_; uint8_t v___x_1432_; 
v___x_1404_ = l_Lean_KVMap_instValueBool;
v_snd_1405_ = lean_ctor_get(v_resStartStop_1403_, 1);
lean_inc(v_snd_1405_);
v_fst_1406_ = lean_ctor_get(v_resStartStop_1403_, 0);
lean_inc(v_fst_1406_);
lean_dec_ref(v_resStartStop_1403_);
v_fst_1407_ = lean_ctor_get(v_snd_1405_, 0);
lean_inc(v_fst_1407_);
v_snd_1408_ = lean_ctor_get(v_snd_1405_, 1);
lean_inc(v_snd_1408_);
lean_dec(v_snd_1405_);
lean_inc_ref(v_inst_1390_);
v___f_1409_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1409_, 0, v_inst_1390_);
lean_inc_ref(v_oldTraces_1401_);
v___f_1410_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1410_, 0, v_oldTraces_1401_);
lean_inc(v_fst_1406_);
lean_inc_ref(v_inst_1390_);
lean_inc_ref(v_always_1394_);
v___f_1411_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1411_, 0, v_always_1394_);
lean_closure_set(v___f_1411_, 1, v_inst_1390_);
lean_closure_set(v___f_1411_, 2, v_fst_1406_);
v___x_1412_ = l_Lean_trace_profiler;
v___x_1413_ = l_Lean_Option_get___redArg(v___x_1404_, v_opts_1399_, v___x_1412_);
v___x_1432_ = lean_unbox(v___x_1413_);
if (v___x_1432_ == 0)
{
uint8_t v___x_1433_; 
v___x_1433_ = lean_unbox(v___x_1413_);
v___y_1421_ = v___x_1433_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1435_ = l_Lean_Option_get___redArg(v___x_1404_, v_opts_1399_, v___x_1434_);
v___x_1436_ = lean_unbox(v___x_1435_);
lean_dec(v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; double v___x_1440_; double v___x_1441_; double v___x_1442_; 
v___x_1437_ = l_Lean_KVMap_instValueNat;
v___x_1438_ = l_Lean_trace_profiler_threshold;
v___x_1439_ = l_Lean_Option_get___redArg(v___x_1437_, v_opts_1399_, v___x_1438_);
v___x_1440_ = lean_float_of_nat(v___x_1439_);
v___x_1441_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1442_ = lean_float_div(v___x_1440_, v___x_1441_);
v___y_1427_ = v___x_1442_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; double v___x_1446_; 
v___x_1443_ = l_Lean_KVMap_instValueNat;
v___x_1444_ = l_Lean_trace_profiler_threshold;
v___x_1445_ = l_Lean_Option_get___redArg(v___x_1443_, v_opts_1399_, v___x_1444_);
v___x_1446_ = lean_float_of_nat(v___x_1445_);
v___y_1427_ = v___x_1446_;
goto v___jp_1426_;
}
}
v___jp_1414_:
{
lean_object* v_toBind_1415_; lean_object* v_getRef_1416_; lean_object* v___x_1417_; lean_object* v___f_1418_; lean_object* v___x_1419_; 
v_toBind_1415_ = lean_ctor_get(v_inst_1390_, 1);
lean_inc(v_toBind_1415_);
v_getRef_1416_ = lean_ctor_get(v_inst_1392_, 0);
lean_inc(v_getRef_1416_);
v___x_1417_ = lean_box(v_collapsed_1397_);
lean_inc(v_toBind_1415_);
v___f_1418_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed), 18, 17);
lean_closure_set(v___f_1418_, 0, v_always_1394_);
lean_closure_set(v___f_1418_, 1, v_inst_1390_);
lean_closure_set(v___f_1418_, 2, v_fst_1406_);
lean_closure_set(v___f_1418_, 3, v_inst_1395_);
lean_closure_set(v___f_1418_, 4, v_inst_1391_);
lean_closure_set(v___f_1418_, 5, v_inst_1392_);
lean_closure_set(v___f_1418_, 6, v_inst_1393_);
lean_closure_set(v___f_1418_, 7, v_oldTraces_1401_);
lean_closure_set(v___f_1418_, 8, v_toBind_1415_);
lean_closure_set(v___f_1418_, 9, v_cls_1396_);
lean_closure_set(v___f_1418_, 10, v___x_1417_);
lean_closure_set(v___f_1418_, 11, v_tag_1398_);
lean_closure_set(v___f_1418_, 12, v___x_1413_);
lean_closure_set(v___f_1418_, 13, v_fst_1407_);
lean_closure_set(v___f_1418_, 14, v_snd_1408_);
lean_closure_set(v___f_1418_, 15, v_msg_1402_);
lean_closure_set(v___f_1418_, 16, v___f_1409_);
v___x_1419_ = lean_apply_4(v_toBind_1415_, lean_box(0), lean_box(0), v_getRef_1416_, v___f_1418_);
return v___x_1419_;
}
v___jp_1420_:
{
if (v_clsEnabled_1400_ == 0)
{
if (v___y_1421_ == 0)
{
lean_object* v_toBind_1422_; lean_object* v_modifyTraceState_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v___x_1413_);
lean_dec_ref(v___f_1409_);
lean_dec(v_snd_1408_);
lean_dec(v_fst_1407_);
lean_dec(v_fst_1406_);
lean_dec(v_msg_1402_);
lean_dec_ref(v_oldTraces_1401_);
lean_dec_ref(v_tag_1398_);
lean_dec(v_cls_1396_);
lean_dec_ref(v_inst_1395_);
lean_dec_ref(v_always_1394_);
lean_dec(v_inst_1393_);
lean_dec_ref(v_inst_1392_);
v_toBind_1422_ = lean_ctor_get(v_inst_1390_, 1);
lean_inc(v_toBind_1422_);
lean_dec_ref(v_inst_1390_);
v_modifyTraceState_1423_ = lean_ctor_get(v_inst_1391_, 0);
lean_inc(v_modifyTraceState_1423_);
lean_dec_ref(v_inst_1391_);
v___x_1424_ = lean_apply_1(v_modifyTraceState_1423_, v___f_1410_);
v___x_1425_ = lean_apply_4(v_toBind_1422_, lean_box(0), lean_box(0), v___x_1424_, v___f_1411_);
return v___x_1425_;
}
else
{
lean_dec_ref(v___f_1411_);
lean_dec_ref(v___f_1410_);
goto v___jp_1414_;
}
}
else
{
lean_dec_ref(v___f_1411_);
lean_dec_ref(v___f_1410_);
goto v___jp_1414_;
}
}
v___jp_1426_:
{
double v___x_1428_; double v___x_1429_; double v___x_1430_; uint8_t v___x_1431_; 
v___x_1428_ = lean_unbox_float(v_snd_1408_);
v___x_1429_ = lean_unbox_float(v_fst_1407_);
v___x_1430_ = lean_float_sub(v___x_1428_, v___x_1429_);
v___x_1431_ = lean_float_decLt(v___y_1427_, v___x_1430_);
v___y_1421_ = v___x_1431_;
goto v___jp_1420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_inst_1449_, lean_object* v_inst_1450_, lean_object* v_always_1451_, lean_object* v_inst_1452_, lean_object* v_cls_1453_, lean_object* v_collapsed_1454_, lean_object* v_tag_1455_, lean_object* v_opts_1456_, lean_object* v_clsEnabled_1457_, lean_object* v_oldTraces_1458_, lean_object* v_msg_1459_, lean_object* v_resStartStop_1460_){
_start:
{
uint8_t v_collapsed_boxed_1461_; uint8_t v_clsEnabled_boxed_1462_; lean_object* v_res_1463_; 
v_collapsed_boxed_1461_ = lean_unbox(v_collapsed_1454_);
v_clsEnabled_boxed_1462_ = lean_unbox(v_clsEnabled_1457_);
v_res_1463_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1447_, v_inst_1448_, v_inst_1449_, v_inst_1450_, v_always_1451_, v_inst_1452_, v_cls_1453_, v_collapsed_boxed_1461_, v_tag_1455_, v_opts_1456_, v_clsEnabled_boxed_1462_, v_oldTraces_1458_, v_msg_1459_, v_resStartStop_1460_);
lean_dec_ref(v_opts_1456_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object* v_00_u03b1_1464_, lean_object* v_m_1465_, lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_00_u03b5_1470_, lean_object* v_always_1471_, lean_object* v_inst_1472_, lean_object* v_cls_1473_, uint8_t v_collapsed_1474_, lean_object* v_tag_1475_, lean_object* v_opts_1476_, uint8_t v_clsEnabled_1477_, lean_object* v_oldTraces_1478_, lean_object* v_msg_1479_, lean_object* v_resStartStop_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1466_, v_inst_1467_, v_inst_1468_, v_inst_1469_, v_always_1471_, v_inst_1472_, v_cls_1473_, v_collapsed_1474_, v_tag_1475_, v_opts_1476_, v_clsEnabled_1477_, v_oldTraces_1478_, v_msg_1479_, v_resStartStop_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_1482_ = _args[0];
lean_object* v_m_1483_ = _args[1];
lean_object* v_inst_1484_ = _args[2];
lean_object* v_inst_1485_ = _args[3];
lean_object* v_inst_1486_ = _args[4];
lean_object* v_inst_1487_ = _args[5];
lean_object* v_00_u03b5_1488_ = _args[6];
lean_object* v_always_1489_ = _args[7];
lean_object* v_inst_1490_ = _args[8];
lean_object* v_cls_1491_ = _args[9];
lean_object* v_collapsed_1492_ = _args[10];
lean_object* v_tag_1493_ = _args[11];
lean_object* v_opts_1494_ = _args[12];
lean_object* v_clsEnabled_1495_ = _args[13];
lean_object* v_oldTraces_1496_ = _args[14];
lean_object* v_msg_1497_ = _args[15];
lean_object* v_resStartStop_1498_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1499_; uint8_t v_clsEnabled_boxed_1500_; lean_object* v_res_1501_; 
v_collapsed_boxed_1499_ = lean_unbox(v_collapsed_1492_);
v_clsEnabled_boxed_1500_ = lean_unbox(v_clsEnabled_1495_);
v_res_1501_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(v_00_u03b1_1482_, v_m_1483_, v_inst_1484_, v_inst_1485_, v_inst_1486_, v_inst_1487_, v_00_u03b5_1488_, v_always_1489_, v_inst_1490_, v_cls_1491_, v_collapsed_boxed_1499_, v_tag_1493_, v_opts_1494_, v_clsEnabled_boxed_1500_, v_oldTraces_1496_, v_msg_1497_, v_resStartStop_1498_);
lean_dec_ref(v_opts_1494_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_always_1506_, lean_object* v_inst_1507_, lean_object* v_cls_1508_, uint8_t v_collapsed_1509_, lean_object* v_tag_1510_, lean_object* v_opts_1511_, uint8_t v_clsEnabled_1512_, lean_object* v_oldTraces_1513_, lean_object* v_msg_1514_, lean_object* v_resStartStop_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1502_, v_inst_1503_, v_inst_1504_, v_inst_1505_, v_always_1506_, v_inst_1507_, v_cls_1508_, v_collapsed_1509_, v_tag_1510_, v_opts_1511_, v_clsEnabled_1512_, v_oldTraces_1513_, v_msg_1514_, v_resStartStop_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_always_1521_, lean_object* v_inst_1522_, lean_object* v_cls_1523_, lean_object* v_collapsed_1524_, lean_object* v_tag_1525_, lean_object* v_opts_1526_, lean_object* v_clsEnabled_1527_, lean_object* v_oldTraces_1528_, lean_object* v_msg_1529_, lean_object* v_resStartStop_1530_){
_start:
{
uint8_t v_collapsed_boxed_1531_; uint8_t v_clsEnabled_boxed_1532_; lean_object* v_res_1533_; 
v_collapsed_boxed_1531_ = lean_unbox(v_collapsed_1524_);
v_clsEnabled_boxed_1532_ = lean_unbox(v_clsEnabled_1527_);
v_res_1533_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1517_, v_inst_1518_, v_inst_1519_, v_inst_1520_, v_always_1521_, v_inst_1522_, v_cls_1523_, v_collapsed_boxed_1531_, v_tag_1525_, v_opts_1526_, v_clsEnabled_boxed_1532_, v_oldTraces_1528_, v_msg_1529_, v_resStartStop_1530_);
lean_dec_ref(v_opts_1526_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object* v_toPure_1534_, lean_object* v_ex_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v_ex_1535_);
v___x_1537_ = lean_apply_2(v_toPure_1534_, lean_box(0), v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object* v_toPure_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_a_1539_);
v___x_1541_ = lean_apply_2(v_toPure_1538_, lean_box(0), v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object* v_start_1542_, lean_object* v_a_1543_, lean_object* v_toPure_1544_, lean_object* v_stop_1545_){
_start:
{
double v___x_1546_; double v___x_1547_; double v___x_1548_; double v___x_1549_; double v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1546_ = lean_float_of_nat(v_start_1542_);
v___x_1547_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1548_ = lean_float_div(v___x_1546_, v___x_1547_);
v___x_1549_ = lean_float_of_nat(v_stop_1545_);
v___x_1550_ = lean_float_div(v___x_1549_, v___x_1547_);
v___x_1551_ = lean_box_float(v___x_1548_);
v___x_1552_ = lean_box_float(v___x_1550_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_a_1543_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_apply_2(v_toPure_1544_, lean_box(0), v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object* v_start_1556_, lean_object* v_toPure_1557_, lean_object* v_toBind_1558_, lean_object* v___x_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v___f_1561_; lean_object* v___x_1562_; 
v___f_1561_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1561_, 0, v_start_1556_);
lean_closure_set(v___f_1561_, 1, v_a_1560_);
lean_closure_set(v___f_1561_, 2, v_toPure_1557_);
v___x_1562_ = lean_apply_4(v_toBind_1558_, lean_box(0), lean_box(0), v___x_1559_, v___f_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object* v_toPure_1563_, lean_object* v_toBind_1564_, lean_object* v___x_1565_, lean_object* v___x_1566_, lean_object* v_start_1567_){
_start:
{
lean_object* v___f_1568_; lean_object* v___x_1569_; 
lean_inc(v_toBind_1564_);
v___f_1568_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1568_, 0, v_start_1567_);
lean_closure_set(v___f_1568_, 1, v_toPure_1563_);
lean_closure_set(v___f_1568_, 2, v_toBind_1564_);
lean_closure_set(v___f_1568_, 3, v___x_1565_);
v___x_1569_ = lean_apply_4(v_toBind_1564_, lean_box(0), lean_box(0), v___x_1566_, v___f_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object* v_start_1570_, lean_object* v_a_1571_, lean_object* v_toPure_1572_, lean_object* v_stop_1573_){
_start:
{
double v___x_1574_; double v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1574_ = lean_float_of_nat(v_start_1570_);
v___x_1575_ = lean_float_of_nat(v_stop_1573_);
v___x_1576_ = lean_box_float(v___x_1574_);
v___x_1577_ = lean_box_float(v___x_1575_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_a_1571_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_apply_2(v_toPure_1572_, lean_box(0), v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object* v_start_1581_, lean_object* v_toPure_1582_, lean_object* v_toBind_1583_, lean_object* v___x_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___f_1586_; lean_object* v___x_1587_; 
v___f_1586_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__6), 4, 3);
lean_closure_set(v___f_1586_, 0, v_start_1581_);
lean_closure_set(v___f_1586_, 1, v_a_1585_);
lean_closure_set(v___f_1586_, 2, v_toPure_1582_);
v___x_1587_ = lean_apply_4(v_toBind_1583_, lean_box(0), lean_box(0), v___x_1584_, v___f_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object* v_toPure_1588_, lean_object* v_toBind_1589_, lean_object* v___x_1590_, lean_object* v___x_1591_, lean_object* v_start_1592_){
_start:
{
lean_object* v___f_1593_; lean_object* v___x_1594_; 
lean_inc(v_toBind_1589_);
v___f_1593_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1593_, 0, v_start_1592_);
lean_closure_set(v___f_1593_, 1, v_toPure_1588_);
lean_closure_set(v___f_1593_, 2, v_toBind_1589_);
lean_closure_set(v___f_1593_, 3, v___x_1590_);
v___x_1594_ = lean_apply_4(v_toBind_1589_, lean_box(0), lean_box(0), v___x_1591_, v___f_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object* v_toApplicative_1595_, lean_object* v_always_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_cls_1602_, uint8_t v_collapsed_1603_, lean_object* v_tag_1604_, lean_object* v_opts_1605_, uint8_t v_clsEnabled_1606_, lean_object* v_msg_1607_, lean_object* v_toBind_1608_, lean_object* v_k_1609_, lean_object* v_inst_1610_, lean_object* v_oldTraces_1611_){
_start:
{
lean_object* v_toPure_1612_; lean_object* v_tryCatch_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___f_1616_; lean_object* v___f_1617_; lean_object* v___f_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v_toPure_1612_ = lean_ctor_get(v_toApplicative_1595_, 1);
lean_inc(v_toPure_1612_);
lean_dec_ref(v_toApplicative_1595_);
v_tryCatch_1613_ = lean_ctor_get(v_always_1596_, 1);
lean_inc(v_tryCatch_1613_);
v___x_1614_ = lean_box(v_collapsed_1603_);
v___x_1615_ = lean_box(v_clsEnabled_1606_);
lean_inc_ref(v_opts_1605_);
v___f_1616_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1616_, 0, v_inst_1597_);
lean_closure_set(v___f_1616_, 1, v_inst_1598_);
lean_closure_set(v___f_1616_, 2, v_inst_1599_);
lean_closure_set(v___f_1616_, 3, v_inst_1600_);
lean_closure_set(v___f_1616_, 4, v_always_1596_);
lean_closure_set(v___f_1616_, 5, v_inst_1601_);
lean_closure_set(v___f_1616_, 6, v_cls_1602_);
lean_closure_set(v___f_1616_, 7, v___x_1614_);
lean_closure_set(v___f_1616_, 8, v_tag_1604_);
lean_closure_set(v___f_1616_, 9, v_opts_1605_);
lean_closure_set(v___f_1616_, 10, v___x_1615_);
lean_closure_set(v___f_1616_, 11, v_oldTraces_1611_);
lean_closure_set(v___f_1616_, 12, v_msg_1607_);
lean_inc(v_toPure_1612_);
v___f_1617_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1617_, 0, v_toPure_1612_);
lean_inc(v_toPure_1612_);
v___f_1618_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1618_, 0, v_toPure_1612_);
lean_inc(v_toBind_1608_);
v___x_1619_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v_k_1609_, v___f_1618_);
v___x_1620_ = lean_apply_3(v_tryCatch_1613_, lean_box(0), v___x_1619_, v___f_1617_);
v___x_1621_ = l_Lean_KVMap_instValueBool;
v___x_1622_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1623_ = l_Lean_Option_get___redArg(v___x_1621_, v_opts_1605_, v___x_1622_);
lean_dec_ref(v_opts_1605_);
v___x_1624_ = lean_unbox(v___x_1623_);
lean_dec(v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___f_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1626_ = lean_apply_2(v_inst_1610_, lean_box(0), v___x_1625_);
lean_inc(v___x_1626_);
lean_inc(v_toBind_1608_);
v___f_1627_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1627_, 0, v_toPure_1612_);
lean_closure_set(v___f_1627_, 1, v_toBind_1608_);
lean_closure_set(v___f_1627_, 2, v___x_1626_);
lean_closure_set(v___f_1627_, 3, v___x_1620_);
lean_inc(v_toBind_1608_);
v___x_1628_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v___x_1626_, v___f_1627_);
v___x_1629_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v___x_1628_, v___f_1616_);
return v___x_1629_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___f_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1630_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1631_ = lean_apply_2(v_inst_1610_, lean_box(0), v___x_1630_);
lean_inc(v___x_1631_);
lean_inc(v_toBind_1608_);
v___f_1632_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_1632_, 0, v_toPure_1612_);
lean_closure_set(v___f_1632_, 1, v_toBind_1608_);
lean_closure_set(v___f_1632_, 2, v___x_1631_);
lean_closure_set(v___f_1632_, 3, v___x_1620_);
lean_inc(v_toBind_1608_);
v___x_1633_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v___x_1631_, v___f_1632_);
v___x_1634_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v___x_1633_, v___f_1616_);
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_toApplicative_1635_ = _args[0];
lean_object* v_always_1636_ = _args[1];
lean_object* v_inst_1637_ = _args[2];
lean_object* v_inst_1638_ = _args[3];
lean_object* v_inst_1639_ = _args[4];
lean_object* v_inst_1640_ = _args[5];
lean_object* v_inst_1641_ = _args[6];
lean_object* v_cls_1642_ = _args[7];
lean_object* v_collapsed_1643_ = _args[8];
lean_object* v_tag_1644_ = _args[9];
lean_object* v_opts_1645_ = _args[10];
lean_object* v_clsEnabled_1646_ = _args[11];
lean_object* v_msg_1647_ = _args[12];
lean_object* v_toBind_1648_ = _args[13];
lean_object* v_k_1649_ = _args[14];
lean_object* v_inst_1650_ = _args[15];
lean_object* v_oldTraces_1651_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1652_; uint8_t v_clsEnabled_boxed_1653_; lean_object* v_res_1654_; 
v_collapsed_boxed_1652_ = lean_unbox(v_collapsed_1643_);
v_clsEnabled_boxed_1653_ = lean_unbox(v_clsEnabled_1646_);
v_res_1654_ = l_Lean_withTraceNode___redArg___lam__9(v_toApplicative_1635_, v_always_1636_, v_inst_1637_, v_inst_1638_, v_inst_1639_, v_inst_1640_, v_inst_1641_, v_cls_1642_, v_collapsed_boxed_1652_, v_tag_1644_, v_opts_1645_, v_clsEnabled_boxed_1653_, v_msg_1647_, v_toBind_1648_, v_k_1649_, v_inst_1650_, v_oldTraces_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object* v_toApplicative_1655_, lean_object* v_always_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_inst_1661_, lean_object* v_cls_1662_, uint8_t v_collapsed_1663_, lean_object* v_tag_1664_, lean_object* v_opts_1665_, lean_object* v_msg_1666_, lean_object* v_toBind_1667_, lean_object* v_k_1668_, lean_object* v_inst_1669_, uint8_t v_clsEnabled_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___f_1673_; 
v___x_1671_ = lean_box(v_collapsed_1663_);
v___x_1672_ = lean_box(v_clsEnabled_1670_);
lean_inc(v_k_1668_);
lean_inc(v_toBind_1667_);
lean_inc_ref(v_opts_1665_);
lean_inc_ref(v_inst_1658_);
lean_inc_ref(v_inst_1657_);
v___f_1673_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_1673_, 0, v_toApplicative_1655_);
lean_closure_set(v___f_1673_, 1, v_always_1656_);
lean_closure_set(v___f_1673_, 2, v_inst_1657_);
lean_closure_set(v___f_1673_, 3, v_inst_1658_);
lean_closure_set(v___f_1673_, 4, v_inst_1659_);
lean_closure_set(v___f_1673_, 5, v_inst_1660_);
lean_closure_set(v___f_1673_, 6, v_inst_1661_);
lean_closure_set(v___f_1673_, 7, v_cls_1662_);
lean_closure_set(v___f_1673_, 8, v___x_1671_);
lean_closure_set(v___f_1673_, 9, v_tag_1664_);
lean_closure_set(v___f_1673_, 10, v_opts_1665_);
lean_closure_set(v___f_1673_, 11, v___x_1672_);
lean_closure_set(v___f_1673_, 12, v_msg_1666_);
lean_closure_set(v___f_1673_, 13, v_toBind_1667_);
lean_closure_set(v___f_1673_, 14, v_k_1668_);
lean_closure_set(v___f_1673_, 15, v_inst_1669_);
if (v_clsEnabled_1670_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1677_ = l_Lean_KVMap_instValueBool;
v___x_1678_ = l_Lean_trace_profiler;
v___x_1679_ = l_Lean_Option_get___redArg(v___x_1677_, v_opts_1665_, v___x_1678_);
lean_dec_ref(v_opts_1665_);
v___x_1680_ = lean_unbox(v___x_1679_);
lean_dec(v___x_1679_);
if (v___x_1680_ == 0)
{
lean_dec_ref(v___f_1673_);
lean_dec(v_toBind_1667_);
lean_dec_ref(v_inst_1658_);
lean_dec_ref(v_inst_1657_);
return v_k_1668_;
}
else
{
lean_dec(v_k_1668_);
goto v___jp_1674_;
}
}
else
{
lean_dec(v_k_1668_);
lean_dec_ref(v_opts_1665_);
goto v___jp_1674_;
}
v___jp_1674_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1657_, v_inst_1658_);
v___x_1676_ = lean_apply_4(v_toBind_1667_, lean_box(0), lean_box(0), v___x_1675_, v___f_1673_);
return v___x_1676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object* v_toApplicative_1681_, lean_object* v_always_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v_cls_1688_, lean_object* v_collapsed_1689_, lean_object* v_tag_1690_, lean_object* v_opts_1691_, lean_object* v_msg_1692_, lean_object* v_toBind_1693_, lean_object* v_k_1694_, lean_object* v_inst_1695_, lean_object* v_clsEnabled_1696_){
_start:
{
uint8_t v_collapsed_boxed_1697_; uint8_t v_clsEnabled_boxed_1698_; lean_object* v_res_1699_; 
v_collapsed_boxed_1697_ = lean_unbox(v_collapsed_1689_);
v_clsEnabled_boxed_1698_ = lean_unbox(v_clsEnabled_1696_);
v_res_1699_ = l_Lean_withTraceNode___redArg___lam__10(v_toApplicative_1681_, v_always_1682_, v_inst_1683_, v_inst_1684_, v_inst_1685_, v_inst_1686_, v_inst_1687_, v_cls_1688_, v_collapsed_boxed_1697_, v_tag_1690_, v_opts_1691_, v_msg_1692_, v_toBind_1693_, v_k_1694_, v_inst_1695_, v_clsEnabled_boxed_1698_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__11(lean_object* v_k_1700_, lean_object* v_toApplicative_1701_, lean_object* v_always_1702_, lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_cls_1708_, uint8_t v_collapsed_1709_, lean_object* v_tag_1710_, lean_object* v_msg_1711_, lean_object* v_toBind_1712_, lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_opts_1715_){
_start:
{
uint8_t v_hasTrace_1716_; 
v_hasTrace_1716_ = lean_ctor_get_uint8(v_opts_1715_, sizeof(void*)*1);
if (v_hasTrace_1716_ == 0)
{
lean_dec_ref(v_opts_1715_);
lean_dec(v_inst_1714_);
lean_dec(v_inst_1713_);
lean_dec(v_toBind_1712_);
lean_dec(v_msg_1711_);
lean_dec_ref(v_tag_1710_);
lean_dec(v_cls_1708_);
lean_dec_ref(v_inst_1707_);
lean_dec(v_inst_1706_);
lean_dec_ref(v_inst_1705_);
lean_dec_ref(v_inst_1704_);
lean_dec_ref(v_inst_1703_);
lean_dec_ref(v_always_1702_);
lean_dec_ref(v_toApplicative_1701_);
return v_k_1700_;
}
else
{
lean_object* v___x_1717_; lean_object* v___f_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1717_ = lean_box(v_collapsed_1709_);
lean_inc(v_toBind_1712_);
lean_inc(v_cls_1708_);
lean_inc_ref(v_inst_1704_);
lean_inc_ref(v_inst_1703_);
v___f_1718_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_1718_, 0, v_toApplicative_1701_);
lean_closure_set(v___f_1718_, 1, v_always_1702_);
lean_closure_set(v___f_1718_, 2, v_inst_1703_);
lean_closure_set(v___f_1718_, 3, v_inst_1704_);
lean_closure_set(v___f_1718_, 4, v_inst_1705_);
lean_closure_set(v___f_1718_, 5, v_inst_1706_);
lean_closure_set(v___f_1718_, 6, v_inst_1707_);
lean_closure_set(v___f_1718_, 7, v_cls_1708_);
lean_closure_set(v___f_1718_, 8, v___x_1717_);
lean_closure_set(v___f_1718_, 9, v_tag_1710_);
lean_closure_set(v___f_1718_, 10, v_opts_1715_);
lean_closure_set(v___f_1718_, 11, v_msg_1711_);
lean_closure_set(v___f_1718_, 12, v_toBind_1712_);
lean_closure_set(v___f_1718_, 13, v_k_1700_);
lean_closure_set(v___f_1718_, 14, v_inst_1713_);
v___x_1719_ = l_Lean_isTracingEnabledFor___redArg(v_inst_1703_, v_inst_1704_, v_inst_1714_, v_cls_1708_);
v___x_1720_ = lean_apply_4(v_toBind_1712_, lean_box(0), lean_box(0), v___x_1719_, v___f_1718_);
return v___x_1720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__11___boxed(lean_object* v_k_1721_, lean_object* v_toApplicative_1722_, lean_object* v_always_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_cls_1729_, lean_object* v_collapsed_1730_, lean_object* v_tag_1731_, lean_object* v_msg_1732_, lean_object* v_toBind_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_opts_1736_){
_start:
{
uint8_t v_collapsed_boxed_1737_; lean_object* v_res_1738_; 
v_collapsed_boxed_1737_ = lean_unbox(v_collapsed_1730_);
v_res_1738_ = l_Lean_withTraceNode___redArg___lam__11(v_k_1721_, v_toApplicative_1722_, v_always_1723_, v_inst_1724_, v_inst_1725_, v_inst_1726_, v_inst_1727_, v_inst_1728_, v_cls_1729_, v_collapsed_boxed_1737_, v_tag_1731_, v_msg_1732_, v_toBind_1733_, v_inst_1734_, v_inst_1735_, v_opts_1736_);
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
lean_inc(v_toBind_1753_);
v___x_1754_ = lean_box(v_collapsed_1750_);
lean_inc(v_inst_1743_);
lean_inc(v_toBind_1753_);
v___f_1755_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_1755_, 0, v_k_1749_);
lean_closure_set(v___f_1755_, 1, v_toApplicative_1752_);
lean_closure_set(v___f_1755_, 2, v_always_1744_);
lean_closure_set(v___f_1755_, 3, v_inst_1739_);
lean_closure_set(v___f_1755_, 4, v_inst_1740_);
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
lean_inc(v_toBind_1789_);
v___x_1790_ = lean_box(v_collapsed_1786_);
lean_inc(v_inst_1778_);
lean_inc(v_toBind_1789_);
v___f_1791_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__11___boxed), 16, 15);
lean_closure_set(v___f_1791_, 0, v_k_1785_);
lean_closure_set(v___f_1791_, 1, v_toApplicative_1788_);
lean_closure_set(v___f_1791_, 2, v_always_1780_);
lean_closure_set(v___f_1791_, 3, v_inst_1774_);
lean_closure_set(v___f_1791_, 4, v_inst_1775_);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object* v_toPure_1823_, lean_object* v_ex_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_ex_1824_);
v___x_1826_ = lean_apply_2(v_toPure_1823_, lean_box(0), v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object* v_toPure_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1829_, 0, v_a_1828_);
v___x_1830_ = lean_apply_2(v_toPure_1827_, lean_box(0), v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v___f_1836_, lean_object* v_cls_1837_, uint8_t v_collapsed_1838_, lean_object* v_tag_1839_, lean_object* v_opts_1840_, uint8_t v_clsEnabled_1841_, lean_object* v_oldTraces_1842_, lean_object* v_msg_1843_, lean_object* v_resStartStop_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1831_, v_inst_1832_, v_inst_1833_, v_inst_1834_, v_inst_1835_, v___f_1836_, v_cls_1837_, v_collapsed_1838_, v_tag_1839_, v_opts_1840_, v_clsEnabled_1841_, v_oldTraces_1842_, v_msg_1843_, v_resStartStop_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4___boxed(lean_object* v_inst_1846_, lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v___f_1851_, lean_object* v_cls_1852_, lean_object* v_collapsed_1853_, lean_object* v_tag_1854_, lean_object* v_opts_1855_, lean_object* v_clsEnabled_1856_, lean_object* v_oldTraces_1857_, lean_object* v_msg_1858_, lean_object* v_resStartStop_1859_){
_start:
{
uint8_t v_collapsed_boxed_1860_; uint8_t v_clsEnabled_boxed_1861_; lean_object* v_res_1862_; 
v_collapsed_boxed_1860_ = lean_unbox(v_collapsed_1853_);
v_clsEnabled_boxed_1861_ = lean_unbox(v_clsEnabled_1856_);
v_res_1862_ = l_Lean_withTraceNode_x27___redArg___lam__4(v_inst_1846_, v_inst_1847_, v_inst_1848_, v_inst_1849_, v_inst_1850_, v___f_1851_, v_cls_1852_, v_collapsed_boxed_1860_, v_tag_1854_, v_opts_1855_, v_clsEnabled_boxed_1861_, v_oldTraces_1857_, v_msg_1858_, v_resStartStop_1859_);
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
v___f_1938_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4___boxed), 14, 13);
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
lean_inc(v_toBind_1928_);
v___f_1947_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1947_, 0, v_toPure_1933_);
lean_closure_set(v___f_1947_, 1, v_toBind_1928_);
lean_closure_set(v___f_1947_, 2, v___x_1946_);
lean_closure_set(v___f_1947_, 3, v___x_1940_);
lean_inc(v_toBind_1928_);
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
lean_inc(v_toBind_1928_);
v___f_1952_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__10), 5, 4);
lean_closure_set(v___f_1952_, 0, v_toPure_1933_);
lean_closure_set(v___f_1952_, 1, v_toBind_1928_);
lean_closure_set(v___f_1952_, 2, v___x_1951_);
lean_closure_set(v___f_1952_, 3, v___x_1940_);
lean_inc(v_toBind_1928_);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object* v_k_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_inst_2031_, lean_object* v___f_2032_, lean_object* v_cls_2033_, uint8_t v_collapsed_2034_, lean_object* v_tag_2035_, lean_object* v_msg_2036_, lean_object* v_toBind_2037_, lean_object* v___f_2038_, lean_object* v___f_2039_, lean_object* v_inst_2040_, lean_object* v_toPure_2041_, lean_object* v_inst_2042_, lean_object* v_opts_2043_){
_start:
{
uint8_t v_hasTrace_2044_; 
v_hasTrace_2044_ = lean_ctor_get_uint8(v_opts_2043_, sizeof(void*)*1);
if (v_hasTrace_2044_ == 0)
{
lean_dec_ref(v_opts_2043_);
lean_dec(v_inst_2042_);
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
lean_object* v___x_2045_; lean_object* v___f_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2045_ = lean_box(v_collapsed_2034_);
lean_inc(v_toBind_2037_);
lean_inc(v_cls_2033_);
lean_inc_ref(v_inst_2029_);
lean_inc_ref(v_inst_2028_);
v___f_2046_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_2046_, 0, v_inst_2027_);
lean_closure_set(v___f_2046_, 1, v_inst_2028_);
lean_closure_set(v___f_2046_, 2, v_inst_2029_);
lean_closure_set(v___f_2046_, 3, v_inst_2030_);
lean_closure_set(v___f_2046_, 4, v_inst_2031_);
lean_closure_set(v___f_2046_, 5, v___f_2032_);
lean_closure_set(v___f_2046_, 6, v_cls_2033_);
lean_closure_set(v___f_2046_, 7, v___x_2045_);
lean_closure_set(v___f_2046_, 8, v_tag_2035_);
lean_closure_set(v___f_2046_, 9, v_opts_2043_);
lean_closure_set(v___f_2046_, 10, v_msg_2036_);
lean_closure_set(v___f_2046_, 11, v_toBind_2037_);
lean_closure_set(v___f_2046_, 12, v_k_2026_);
lean_closure_set(v___f_2046_, 13, v___f_2038_);
lean_closure_set(v___f_2046_, 14, v___f_2039_);
lean_closure_set(v___f_2046_, 15, v_inst_2040_);
lean_closure_set(v___f_2046_, 16, v_toPure_2041_);
v___x_2047_ = l_Lean_isTracingEnabledFor___redArg(v_inst_2028_, v_inst_2029_, v_inst_2042_, v_cls_2033_);
v___x_2048_ = lean_apply_4(v_toBind_2037_, lean_box(0), lean_box(0), v___x_2047_, v___f_2046_);
return v___x_2048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_k_2049_ = _args[0];
lean_object* v_inst_2050_ = _args[1];
lean_object* v_inst_2051_ = _args[2];
lean_object* v_inst_2052_ = _args[3];
lean_object* v_inst_2053_ = _args[4];
lean_object* v_inst_2054_ = _args[5];
lean_object* v___f_2055_ = _args[6];
lean_object* v_cls_2056_ = _args[7];
lean_object* v_collapsed_2057_ = _args[8];
lean_object* v_tag_2058_ = _args[9];
lean_object* v_msg_2059_ = _args[10];
lean_object* v_toBind_2060_ = _args[11];
lean_object* v___f_2061_ = _args[12];
lean_object* v___f_2062_ = _args[13];
lean_object* v_inst_2063_ = _args[14];
lean_object* v_toPure_2064_ = _args[15];
lean_object* v_inst_2065_ = _args[16];
lean_object* v_opts_2066_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2067_; lean_object* v_res_2068_; 
v_collapsed_boxed_2067_ = lean_unbox(v_collapsed_2057_);
v_res_2068_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_k_2049_, v_inst_2050_, v_inst_2051_, v_inst_2052_, v_inst_2053_, v_inst_2054_, v___f_2055_, v_cls_2056_, v_collapsed_boxed_2067_, v_tag_2058_, v_msg_2059_, v_toBind_2060_, v___f_2061_, v___f_2062_, v_inst_2063_, v_toPure_2064_, v_inst_2065_, v_opts_2066_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_inst_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_cls_2077_, lean_object* v_k_2078_, uint8_t v_collapsed_2079_, lean_object* v_tag_2080_){
_start:
{
lean_object* v_toApplicative_2081_; lean_object* v_toFunctor_2082_; lean_object* v_toBind_2083_; lean_object* v_toPure_2084_; lean_object* v_map_2085_; lean_object* v___f_2086_; lean_object* v_msg_2087_; lean_object* v___f_2088_; lean_object* v___f_2089_; lean_object* v___f_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_toApplicative_2081_ = lean_ctor_get(v_inst_2070_, 0);
v_toFunctor_2082_ = lean_ctor_get(v_toApplicative_2081_, 0);
v_toBind_2083_ = lean_ctor_get(v_inst_2070_, 1);
lean_inc(v_toBind_2083_);
v_toPure_2084_ = lean_ctor_get(v_toApplicative_2081_, 1);
lean_inc(v_toPure_2084_);
v_map_2085_ = lean_ctor_get(v_toFunctor_2082_, 0);
lean_inc(v_map_2085_);
v___f_2086_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
lean_inc(v_toPure_2084_);
v_msg_2087_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2087_, 0, v_toPure_2084_);
lean_inc(v_toPure_2084_);
v___f_2088_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2088_, 0, v_toPure_2084_);
lean_inc(v_toPure_2084_);
v___f_2089_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2089_, 0, v_toPure_2084_);
v___f_2090_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2091_ = lean_box(v_collapsed_2079_);
lean_inc(v_inst_2074_);
lean_inc(v_toBind_2083_);
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2092_, 0, v_k_2078_);
lean_closure_set(v___f_2092_, 1, v_inst_2075_);
lean_closure_set(v___f_2092_, 2, v_inst_2070_);
lean_closure_set(v___f_2092_, 3, v_inst_2071_);
lean_closure_set(v___f_2092_, 4, v_inst_2072_);
lean_closure_set(v___f_2092_, 5, v_inst_2073_);
lean_closure_set(v___f_2092_, 6, v___f_2090_);
lean_closure_set(v___f_2092_, 7, v_cls_2077_);
lean_closure_set(v___f_2092_, 8, v___x_2091_);
lean_closure_set(v___f_2092_, 9, v_tag_2080_);
lean_closure_set(v___f_2092_, 10, v_msg_2087_);
lean_closure_set(v___f_2092_, 11, v_toBind_2083_);
lean_closure_set(v___f_2092_, 12, v___f_2089_);
lean_closure_set(v___f_2092_, 13, v___f_2088_);
lean_closure_set(v___f_2092_, 14, v_inst_2076_);
lean_closure_set(v___f_2092_, 15, v_toPure_2084_);
lean_closure_set(v___f_2092_, 16, v_inst_2074_);
v___x_2093_ = lean_apply_4(v_toBind_2083_, lean_box(0), lean_box(0), v_inst_2074_, v___f_2092_);
v___x_2094_ = lean_apply_4(v_map_2085_, lean_box(0), lean_box(0), v___f_2086_, v___x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object* v_inst_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_cls_2102_, lean_object* v_k_2103_, lean_object* v_collapsed_2104_, lean_object* v_tag_2105_){
_start:
{
uint8_t v_collapsed_boxed_2106_; lean_object* v_res_2107_; 
v_collapsed_boxed_2106_ = lean_unbox(v_collapsed_2104_);
v_res_2107_ = l_Lean_withTraceNode_x27___redArg(v_inst_2095_, v_inst_2096_, v_inst_2097_, v_inst_2098_, v_inst_2099_, v_inst_2100_, v_inst_2101_, v_cls_2102_, v_k_2103_, v_collapsed_boxed_2106_, v_tag_2105_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object* v_00_u03b1_2108_, lean_object* v_m_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_cls_2117_, lean_object* v_k_2118_, uint8_t v_collapsed_2119_, lean_object* v_tag_2120_){
_start:
{
lean_object* v_toApplicative_2121_; lean_object* v_toFunctor_2122_; lean_object* v_toBind_2123_; lean_object* v_toPure_2124_; lean_object* v_map_2125_; lean_object* v___f_2126_; lean_object* v_msg_2127_; lean_object* v___f_2128_; lean_object* v___f_2129_; lean_object* v___f_2130_; lean_object* v___x_2131_; lean_object* v___f_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_toApplicative_2121_ = lean_ctor_get(v_inst_2110_, 0);
v_toFunctor_2122_ = lean_ctor_get(v_toApplicative_2121_, 0);
v_toBind_2123_ = lean_ctor_get(v_inst_2110_, 1);
lean_inc(v_toBind_2123_);
v_toPure_2124_ = lean_ctor_get(v_toApplicative_2121_, 1);
lean_inc(v_toPure_2124_);
v_map_2125_ = lean_ctor_get(v_toFunctor_2122_, 0);
lean_inc(v_map_2125_);
v___f_2126_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
lean_inc(v_toPure_2124_);
v_msg_2127_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2127_, 0, v_toPure_2124_);
lean_inc(v_toPure_2124_);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2128_, 0, v_toPure_2124_);
lean_inc(v_toPure_2124_);
v___f_2129_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2129_, 0, v_toPure_2124_);
v___f_2130_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2131_ = lean_box(v_collapsed_2119_);
lean_inc(v_inst_2114_);
lean_inc(v_toBind_2123_);
v___f_2132_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2132_, 0, v_k_2118_);
lean_closure_set(v___f_2132_, 1, v_inst_2115_);
lean_closure_set(v___f_2132_, 2, v_inst_2110_);
lean_closure_set(v___f_2132_, 3, v_inst_2111_);
lean_closure_set(v___f_2132_, 4, v_inst_2112_);
lean_closure_set(v___f_2132_, 5, v_inst_2113_);
lean_closure_set(v___f_2132_, 6, v___f_2130_);
lean_closure_set(v___f_2132_, 7, v_cls_2117_);
lean_closure_set(v___f_2132_, 8, v___x_2131_);
lean_closure_set(v___f_2132_, 9, v_tag_2120_);
lean_closure_set(v___f_2132_, 10, v_msg_2127_);
lean_closure_set(v___f_2132_, 11, v_toBind_2123_);
lean_closure_set(v___f_2132_, 12, v___f_2129_);
lean_closure_set(v___f_2132_, 13, v___f_2128_);
lean_closure_set(v___f_2132_, 14, v_inst_2116_);
lean_closure_set(v___f_2132_, 15, v_toPure_2124_);
lean_closure_set(v___f_2132_, 16, v_inst_2114_);
v___x_2133_ = lean_apply_4(v_toBind_2123_, lean_box(0), lean_box(0), v_inst_2114_, v___f_2132_);
v___x_2134_ = lean_apply_4(v_map_2125_, lean_box(0), lean_box(0), v___f_2126_, v___x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_m_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_inst_2143_, lean_object* v_cls_2144_, lean_object* v_k_2145_, lean_object* v_collapsed_2146_, lean_object* v_tag_2147_){
_start:
{
uint8_t v_collapsed_boxed_2148_; lean_object* v_res_2149_; 
v_collapsed_boxed_2148_ = lean_unbox(v_collapsed_2146_);
v_res_2149_ = l_Lean_withTraceNode_x27(v_00_u03b1_2135_, v_m_2136_, v_inst_2137_, v_inst_2138_, v_inst_2139_, v_inst_2140_, v_inst_2141_, v_inst_2142_, v_inst_2143_, v_cls_2144_, v_k_2145_, v_collapsed_boxed_2148_, v_tag_2147_);
return v_res_2149_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__4(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__3));
v___x_2159_ = l_Lean_mkAtom(v___x_2158_);
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__5(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__4, &l_Lean_registerTraceClass___auto__1___closed__4_once, _init_l_Lean_registerTraceClass___auto__1___closed__4);
v___x_2161_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2162_ = lean_array_push(v___x_2161_, v___x_2160_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__6(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2163_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__5, &l_Lean_registerTraceClass___auto__1___closed__5_once, _init_l_Lean_registerTraceClass___auto__1___closed__5);
v___x_2164_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__2));
v___x_2165_ = lean_box(2);
v___x_2166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___x_2164_);
lean_ctor_set(v___x_2166_, 2, v___x_2163_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__7(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__6, &l_Lean_registerTraceClass___auto__1___closed__6_once, _init_l_Lean_registerTraceClass___auto__1___closed__6);
v___x_2168_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_2169_ = lean_array_push(v___x_2168_, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__7, &l_Lean_registerTraceClass___auto__1___closed__7_once, _init_l_Lean_registerTraceClass___auto__1___closed__7);
v___x_2171_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_2172_ = lean_box(2);
v___x_2173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
lean_ctor_set(v___x_2173_, 1, v___x_2171_);
lean_ctor_set(v___x_2173_, 2, v___x_2170_);
return v___x_2173_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__8, &l_Lean_registerTraceClass___auto__1___closed__8_once, _init_l_Lean_registerTraceClass___auto__1___closed__8);
v___x_2175_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2176_ = lean_array_push(v___x_2175_, v___x_2174_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2177_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__9, &l_Lean_registerTraceClass___auto__1___closed__9_once, _init_l_Lean_registerTraceClass___auto__1___closed__9);
v___x_2178_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2179_ = lean_box(2);
v___x_2180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v___x_2178_);
lean_ctor_set(v___x_2180_, 2, v___x_2177_);
return v___x_2180_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__11(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__10, &l_Lean_registerTraceClass___auto__1___closed__10_once, _init_l_Lean_registerTraceClass___auto__1___closed__10);
v___x_2182_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2183_ = lean_array_push(v___x_2182_, v___x_2181_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2184_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__11, &l_Lean_registerTraceClass___auto__1___closed__11_once, _init_l_Lean_registerTraceClass___auto__1___closed__11);
v___x_2185_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_2186_ = lean_box(2);
v___x_2187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v___x_2185_);
lean_ctor_set(v___x_2187_, 2, v___x_2184_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__12, &l_Lean_registerTraceClass___auto__1___closed__12_once, _init_l_Lean_registerTraceClass___auto__1___closed__12);
v___x_2189_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2190_ = lean_array_push(v___x_2189_, v___x_2188_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2191_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__13, &l_Lean_registerTraceClass___auto__1___closed__13_once, _init_l_Lean_registerTraceClass___auto__1___closed__13);
v___x_2192_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_2193_ = lean_box(2);
v___x_2194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v___x_2192_);
lean_ctor_set(v___x_2194_, 2, v___x_2191_);
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1(void){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__14, &l_Lean_registerTraceClass___auto__1___closed__14_once, _init_l_Lean_registerTraceClass___auto__1___closed__14);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2196_, lean_object* v_x_2197_){
_start:
{
if (lean_obj_tag(v_x_2197_) == 0)
{
return v_x_2196_;
}
else
{
lean_object* v_key_2198_; lean_object* v_value_2199_; lean_object* v_tail_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2226_; 
v_key_2198_ = lean_ctor_get(v_x_2197_, 0);
v_value_2199_ = lean_ctor_get(v_x_2197_, 1);
v_tail_2200_ = lean_ctor_get(v_x_2197_, 2);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_x_2197_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2202_ = v_x_2197_;
v_isShared_2203_ = v_isSharedCheck_2226_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_tail_2200_);
lean_inc(v_value_2199_);
lean_inc(v_key_2198_);
lean_dec(v_x_2197_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2226_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; uint64_t v___y_2206_; 
v___x_2204_ = lean_array_get_size(v_x_2196_);
if (lean_obj_tag(v_key_2198_) == 0)
{
uint64_t v___x_2224_; 
v___x_2224_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2206_ = v___x_2224_;
goto v___jp_2205_;
}
else
{
uint64_t v_hash_2225_; 
v_hash_2225_ = lean_ctor_get_uint64(v_key_2198_, sizeof(void*)*2);
v___y_2206_ = v_hash_2225_;
goto v___jp_2205_;
}
v___jp_2205_:
{
uint64_t v___x_2207_; uint64_t v___x_2208_; uint64_t v_fold_2209_; uint64_t v___x_2210_; uint64_t v___x_2211_; uint64_t v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; size_t v___x_2216_; size_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2207_ = 32ULL;
v___x_2208_ = lean_uint64_shift_right(v___y_2206_, v___x_2207_);
v_fold_2209_ = lean_uint64_xor(v___y_2206_, v___x_2208_);
v___x_2210_ = 16ULL;
v___x_2211_ = lean_uint64_shift_right(v_fold_2209_, v___x_2210_);
v___x_2212_ = lean_uint64_xor(v_fold_2209_, v___x_2211_);
v___x_2213_ = lean_uint64_to_usize(v___x_2212_);
v___x_2214_ = lean_usize_of_nat(v___x_2204_);
v___x_2215_ = ((size_t)1ULL);
v___x_2216_ = lean_usize_sub(v___x_2214_, v___x_2215_);
v___x_2217_ = lean_usize_land(v___x_2213_, v___x_2216_);
v___x_2218_ = lean_array_uget_borrowed(v_x_2196_, v___x_2217_);
lean_inc(v___x_2218_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 2, v___x_2218_);
v___x_2220_ = v___x_2202_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_key_2198_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_value_2199_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_array_uset(v_x_2196_, v___x_2217_, v___x_2220_);
v_x_2196_ = v___x_2221_;
v_x_2197_ = v_tail_2200_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object* v_i_2227_, lean_object* v_source_2228_, lean_object* v_target_2229_){
_start:
{
lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2230_ = lean_array_get_size(v_source_2228_);
v___x_2231_ = lean_nat_dec_lt(v_i_2227_, v___x_2230_);
if (v___x_2231_ == 0)
{
lean_dec_ref(v_source_2228_);
lean_dec(v_i_2227_);
return v_target_2229_;
}
else
{
lean_object* v_es_2232_; lean_object* v___x_2233_; lean_object* v_source_2234_; lean_object* v_target_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v_es_2232_ = lean_array_fget(v_source_2228_, v_i_2227_);
v___x_2233_ = lean_box(0);
v_source_2234_ = lean_array_fset(v_source_2228_, v_i_2227_, v___x_2233_);
v_target_2235_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_2229_, v_es_2232_);
v___x_2236_ = lean_unsigned_to_nat(1u);
v___x_2237_ = lean_nat_add(v_i_2227_, v___x_2236_);
lean_dec(v_i_2227_);
v_i_2227_ = v___x_2237_;
v_source_2228_ = v_source_2234_;
v_target_2229_ = v_target_2235_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object* v_data_2239_){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v_nbuckets_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2240_ = lean_array_get_size(v_data_2239_);
v___x_2241_ = lean_unsigned_to_nat(2u);
v_nbuckets_2242_ = lean_nat_mul(v___x_2240_, v___x_2241_);
v___x_2243_ = lean_unsigned_to_nat(0u);
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_mk_array(v_nbuckets_2242_, v___x_2244_);
v___x_2246_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_2243_, v_data_2239_, v___x_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object* v_m_2247_, lean_object* v_a_2248_, lean_object* v_b_2249_){
_start:
{
lean_object* v_size_2250_; lean_object* v_buckets_2251_; lean_object* v___x_2252_; uint64_t v___y_2254_; 
v_size_2250_ = lean_ctor_get(v_m_2247_, 0);
v_buckets_2251_ = lean_ctor_get(v_m_2247_, 1);
v___x_2252_ = lean_array_get_size(v_buckets_2251_);
if (lean_obj_tag(v_a_2248_) == 0)
{
uint64_t v___x_2291_; 
v___x_2291_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2254_ = v___x_2291_;
goto v___jp_2253_;
}
else
{
uint64_t v_hash_2292_; 
v_hash_2292_ = lean_ctor_get_uint64(v_a_2248_, sizeof(void*)*2);
v___y_2254_ = v_hash_2292_;
goto v___jp_2253_;
}
v___jp_2253_:
{
uint64_t v___x_2255_; uint64_t v___x_2256_; uint64_t v_fold_2257_; uint64_t v___x_2258_; uint64_t v___x_2259_; uint64_t v___x_2260_; size_t v___x_2261_; size_t v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; size_t v___x_2265_; lean_object* v_bkt_2266_; uint8_t v___x_2267_; 
v___x_2255_ = 32ULL;
v___x_2256_ = lean_uint64_shift_right(v___y_2254_, v___x_2255_);
v_fold_2257_ = lean_uint64_xor(v___y_2254_, v___x_2256_);
v___x_2258_ = 16ULL;
v___x_2259_ = lean_uint64_shift_right(v_fold_2257_, v___x_2258_);
v___x_2260_ = lean_uint64_xor(v_fold_2257_, v___x_2259_);
v___x_2261_ = lean_uint64_to_usize(v___x_2260_);
v___x_2262_ = lean_usize_of_nat(v___x_2252_);
v___x_2263_ = ((size_t)1ULL);
v___x_2264_ = lean_usize_sub(v___x_2262_, v___x_2263_);
v___x_2265_ = lean_usize_land(v___x_2261_, v___x_2264_);
v_bkt_2266_ = lean_array_uget_borrowed(v_buckets_2251_, v___x_2265_);
v___x_2267_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_2248_, v_bkt_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2288_; 
lean_inc_ref(v_buckets_2251_);
lean_inc(v_size_2250_);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_m_2247_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; lean_object* v_unused_2290_; 
v_unused_2289_ = lean_ctor_get(v_m_2247_, 1);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v_m_2247_, 0);
lean_dec(v_unused_2290_);
v___x_2269_ = v_m_2247_;
v_isShared_2270_ = v_isSharedCheck_2288_;
goto v_resetjp_2268_;
}
else
{
lean_dec(v_m_2247_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2288_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; lean_object* v_size_x27_2272_; lean_object* v___x_2273_; lean_object* v_buckets_x27_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2271_ = lean_unsigned_to_nat(1u);
v_size_x27_2272_ = lean_nat_add(v_size_2250_, v___x_2271_);
lean_dec(v_size_2250_);
lean_inc(v_bkt_2266_);
v___x_2273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2273_, 0, v_a_2248_);
lean_ctor_set(v___x_2273_, 1, v_b_2249_);
lean_ctor_set(v___x_2273_, 2, v_bkt_2266_);
v_buckets_x27_2274_ = lean_array_uset(v_buckets_2251_, v___x_2265_, v___x_2273_);
v___x_2275_ = lean_unsigned_to_nat(4u);
v___x_2276_ = lean_nat_mul(v_size_x27_2272_, v___x_2275_);
v___x_2277_ = lean_unsigned_to_nat(3u);
v___x_2278_ = lean_nat_div(v___x_2276_, v___x_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_array_get_size(v_buckets_x27_2274_);
v___x_2280_ = lean_nat_dec_le(v___x_2278_, v___x_2279_);
lean_dec(v___x_2278_);
if (v___x_2280_ == 0)
{
lean_object* v_val_2281_; lean_object* v___x_2283_; 
v_val_2281_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_2274_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 1, v_val_2281_);
lean_ctor_set(v___x_2269_, 0, v_size_x27_2272_);
v___x_2283_ = v___x_2269_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_size_x27_2272_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_val_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
else
{
lean_object* v___x_2286_; 
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 1, v_buckets_x27_2274_);
lean_ctor_set(v___x_2269_, 0, v_size_x27_2272_);
v___x_2286_ = v___x_2269_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_size_x27_2272_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_buckets_x27_2274_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_dec(v_b_2249_);
lean_dec(v_a_2248_);
return v_m_2247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object* v_traceClassName_2296_, uint8_t v_inherited_2297_, lean_object* v_ref_2298_){
_start:
{
lean_object* v___x_2300_; lean_object* v_optionName_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2300_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v_optionName_2301_ = l_Lean_Name_append(v___x_2300_, v_traceClassName_2296_);
v___x_2302_ = ((lean_object*)(l_Lean_registerTraceClass___closed__0));
v___x_2303_ = ((lean_object*)(l_Lean_registerTraceClass___closed__1));
lean_inc(v_optionName_2301_);
v___x_2304_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2304_, 0, v_optionName_2301_);
lean_ctor_set(v___x_2304_, 1, v_ref_2298_);
lean_ctor_set(v___x_2304_, 2, v___x_2302_);
lean_ctor_set(v___x_2304_, 3, v___x_2303_);
lean_inc(v_optionName_2301_);
v___x_2305_ = lean_register_option(v_optionName_2301_, v___x_2304_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2321_; 
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v___x_2305_, 0);
lean_dec(v_unused_2322_);
v___x_2307_ = v___x_2305_;
v_isShared_2308_ = v_isSharedCheck_2321_;
goto v_resetjp_2306_;
}
else
{
lean_dec(v___x_2305_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2321_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
if (v_inherited_2297_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
lean_dec(v_optionName_2301_);
v___x_2309_ = lean_box(0);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2309_);
v___x_2311_ = v___x_2307_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2313_ = l_Lean_inheritedTraceOptions;
v___x_2314_ = lean_st_ref_take(v___x_2313_);
v___x_2315_ = lean_box(0);
v___x_2316_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2314_, v_optionName_2301_, v___x_2315_);
v___x_2317_ = lean_st_ref_set(v___x_2313_, v___x_2316_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2317_);
v___x_2319_ = v___x_2307_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_dec(v_optionName_2301_);
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object* v_traceClassName_2323_, lean_object* v_inherited_2324_, lean_object* v_ref_2325_, lean_object* v_a_2326_){
_start:
{
uint8_t v_inherited_boxed_2327_; lean_object* v_res_2328_; 
v_inherited_boxed_2327_ = lean_unbox(v_inherited_2324_);
v_res_2328_ = l_Lean_registerTraceClass(v_traceClassName_2323_, v_inherited_boxed_2327_, v_ref_2325_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(lean_object* v_00_u03b2_2329_, lean_object* v_m_2330_, lean_object* v_a_2331_, lean_object* v_b_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v_m_2330_, v_a_2331_, v_b_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object* v_00_u03b2_2334_, lean_object* v_data_2335_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_data_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2337_, lean_object* v_i_2338_, lean_object* v_source_2339_, lean_object* v_target_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_i_2338_, v_source_2339_, v_target_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2343_, v_x_2344_);
return v___x_2345_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10(void){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Array_mkArray0(lean_box(0));
return v___x_2372_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17));
v___x_2393_ = l_String_toRawSubstring_x27(v___x_2392_);
return v___x_2393_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_2427_ = l_String_toRawSubstring_x27(v___x_2426_);
return v___x_2427_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42));
v___x_2450_ = l_String_toRawSubstring_x27(v___x_2449_);
return v___x_2450_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52));
v___x_2471_ = l_String_toRawSubstring_x27(v___x_2470_);
return v___x_2471_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__63));
v___x_2494_ = l_String_toRawSubstring_x27(v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object* v_id_2516_, lean_object* v_s_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_msg_2521_; lean_object* v_quotContext_2522_; lean_object* v_currMacroScope_2523_; lean_object* v_ref_2524_; lean_object* v___y_2525_; lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
lean_inc(v_s_2517_);
v___x_2609_ = l_Lean_Syntax_getKind(v_s_2517_);
v___x_2610_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59));
v___x_2611_ = lean_name_eq(v___x_2609_, v___x_2610_);
lean_dec(v___x_2609_);
if (v___x_2611_ == 0)
{
lean_object* v_quotContext_2612_; lean_object* v_currMacroScope_2613_; lean_object* v_ref_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v_quotContext_2612_ = lean_ctor_get(v_a_2518_, 1);
lean_inc(v_quotContext_2612_);
v_currMacroScope_2613_ = lean_ctor_get(v_a_2518_, 2);
lean_inc(v_currMacroScope_2613_);
v_ref_2614_ = lean_ctor_get(v_a_2518_, 5);
lean_inc(v_ref_2614_);
lean_dec_ref(v_a_2518_);
v___x_2615_ = l_Lean_SourceInfo_fromRef(v_ref_2614_, v___x_2611_);
v___x_2616_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__61));
v___x_2617_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2618_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
lean_inc(v___x_2615_);
v___x_2619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2615_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32));
v___x_2621_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33);
v___x_2622_ = lean_box(0);
lean_inc(v_currMacroScope_2613_);
lean_inc(v_quotContext_2612_);
v___x_2623_ = l_Lean_addMacroScope(v_quotContext_2612_, v___x_2622_, v_currMacroScope_2613_);
v___x_2624_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36));
lean_inc(v___x_2615_);
v___x_2625_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2615_);
lean_ctor_set(v___x_2625_, 1, v___x_2621_);
lean_ctor_set(v___x_2625_, 2, v___x_2623_);
lean_ctor_set(v___x_2625_, 3, v___x_2624_);
lean_inc(v___x_2615_);
v___x_2626_ = l_Lean_Syntax_node1(v___x_2615_, v___x_2620_, v___x_2625_);
lean_inc(v___x_2615_);
v___x_2627_ = l_Lean_Syntax_node2(v___x_2615_, v___x_2617_, v___x_2619_, v___x_2626_);
v___x_2628_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__62));
lean_inc(v___x_2615_);
v___x_2629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2615_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2631_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64);
v___x_2632_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__65));
lean_inc(v_currMacroScope_2613_);
lean_inc(v_quotContext_2612_);
v___x_2633_ = l_Lean_addMacroScope(v_quotContext_2612_, v___x_2632_, v_currMacroScope_2613_);
v___x_2634_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__70));
lean_inc(v___x_2615_);
v___x_2635_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2615_);
lean_ctor_set(v___x_2635_, 1, v___x_2631_);
lean_ctor_set(v___x_2635_, 2, v___x_2633_);
lean_ctor_set(v___x_2635_, 3, v___x_2634_);
lean_inc(v___x_2615_);
v___x_2636_ = l_Lean_Syntax_node1(v___x_2615_, v___x_2630_, v___x_2635_);
v___x_2637_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48));
lean_inc(v___x_2615_);
v___x_2638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2615_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = l_Lean_Syntax_node5(v___x_2615_, v___x_2616_, v___x_2627_, v_s_2517_, v___x_2629_, v___x_2636_, v___x_2638_);
v_msg_2521_ = v___x_2639_;
v_quotContext_2522_ = v_quotContext_2612_;
v_currMacroScope_2523_ = v_currMacroScope_2613_;
v_ref_2524_ = v_ref_2614_;
v___y_2525_ = v_a_2519_;
goto v___jp_2520_;
}
else
{
lean_object* v_quotContext_2640_; lean_object* v_currMacroScope_2641_; lean_object* v_ref_2642_; uint8_t v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_quotContext_2640_ = lean_ctor_get(v_a_2518_, 1);
lean_inc(v_quotContext_2640_);
v_currMacroScope_2641_ = lean_ctor_get(v_a_2518_, 2);
lean_inc(v_currMacroScope_2641_);
v_ref_2642_ = lean_ctor_get(v_a_2518_, 5);
lean_inc(v_ref_2642_);
lean_dec_ref(v_a_2518_);
v___x_2643_ = 0;
v___x_2644_ = l_Lean_SourceInfo_fromRef(v_ref_2642_, v___x_2643_);
v___x_2645_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__72));
v___x_2646_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__73));
lean_inc(v___x_2644_);
v___x_2647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2644_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = l_Lean_Syntax_node2(v___x_2644_, v___x_2645_, v___x_2647_, v_s_2517_);
v_msg_2521_ = v___x_2648_;
v_quotContext_2522_ = v_quotContext_2640_;
v_currMacroScope_2523_ = v_currMacroScope_2641_;
v_ref_2524_ = v_ref_2642_;
v___y_2525_ = v_a_2519_;
goto v___jp_2520_;
}
v___jp_2520_:
{
uint8_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2526_ = 0;
v___x_2527_ = l_Lean_SourceInfo_fromRef(v_ref_2524_, v___x_2526_);
lean_dec(v_ref_2524_);
v___x_2528_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1));
v___x_2529_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2));
lean_inc(v___x_2527_);
v___x_2530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2527_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4));
v___x_2532_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2533_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__6));
v___x_2534_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8));
v___x_2535_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9));
lean_inc(v___x_2527_);
v___x_2536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2527_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10);
lean_inc(v___x_2527_);
v___x_2538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2527_);
lean_ctor_set(v___x_2538_, 1, v___x_2532_);
lean_ctor_set(v___x_2538_, 2, v___x_2537_);
v___x_2539_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12));
v___x_2540_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14));
v___x_2541_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2542_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18);
v___x_2543_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19));
lean_inc(v_currMacroScope_2523_);
lean_inc(v_quotContext_2522_);
v___x_2544_ = l_Lean_addMacroScope(v_quotContext_2522_, v___x_2543_, v_currMacroScope_2523_);
v___x_2545_ = lean_box(0);
lean_inc(v___x_2527_);
v___x_2546_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2527_);
lean_ctor_set(v___x_2546_, 1, v___x_2542_);
lean_ctor_set(v___x_2546_, 2, v___x_2544_);
lean_ctor_set(v___x_2546_, 3, v___x_2545_);
lean_inc_ref(v___x_2546_);
lean_inc(v___x_2527_);
v___x_2547_ = l_Lean_Syntax_node1(v___x_2527_, v___x_2541_, v___x_2546_);
v___x_2548_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20));
lean_inc(v___x_2527_);
v___x_2549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2527_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = l_Lean_Syntax_getId(v_id_2516_);
v___x_2551_ = lean_erase_macro_scopes(v___x_2550_);
v___x_2552_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_2551_);
lean_inc_ref_n(v___x_2538_, 2);
lean_inc(v___x_2527_);
v___x_2553_ = l_Lean_Syntax_node5(v___x_2527_, v___x_2540_, v___x_2547_, v___x_2538_, v___x_2538_, v___x_2549_, v___x_2552_);
lean_inc(v___x_2527_);
v___x_2554_ = l_Lean_Syntax_node1(v___x_2527_, v___x_2539_, v___x_2553_);
lean_inc_ref(v___x_2538_);
lean_inc(v___x_2527_);
v___x_2555_ = l_Lean_Syntax_node3(v___x_2527_, v___x_2534_, v___x_2536_, v___x_2538_, v___x_2554_);
lean_inc_ref(v___x_2538_);
lean_inc(v___x_2527_);
v___x_2556_ = l_Lean_Syntax_node2(v___x_2527_, v___x_2533_, v___x_2555_, v___x_2538_);
v___x_2557_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22));
v___x_2558_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23));
lean_inc(v___x_2527_);
v___x_2559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2527_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25));
v___x_2561_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27));
v___x_2562_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2563_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
lean_inc(v___x_2527_);
v___x_2564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2527_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__32));
v___x_2566_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33);
v___x_2567_ = lean_box(0);
lean_inc(v_currMacroScope_2523_);
lean_inc(v_quotContext_2522_);
v___x_2568_ = l_Lean_addMacroScope(v_quotContext_2522_, v___x_2567_, v_currMacroScope_2523_);
v___x_2569_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__36));
lean_inc(v___x_2527_);
v___x_2570_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2527_);
lean_ctor_set(v___x_2570_, 1, v___x_2566_);
lean_ctor_set(v___x_2570_, 2, v___x_2568_);
lean_ctor_set(v___x_2570_, 3, v___x_2569_);
lean_inc(v___x_2527_);
v___x_2571_ = l_Lean_Syntax_node1(v___x_2527_, v___x_2565_, v___x_2570_);
lean_inc(v___x_2527_);
v___x_2572_ = l_Lean_Syntax_node2(v___x_2527_, v___x_2562_, v___x_2564_, v___x_2571_);
v___x_2573_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__38));
v___x_2574_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39));
lean_inc(v___x_2527_);
v___x_2575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2527_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41));
v___x_2577_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43);
v___x_2578_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45));
lean_inc(v_currMacroScope_2523_);
lean_inc(v_quotContext_2522_);
v___x_2579_ = l_Lean_addMacroScope(v_quotContext_2522_, v___x_2578_, v_currMacroScope_2523_);
v___x_2580_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47));
lean_inc(v___x_2527_);
v___x_2581_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2527_);
lean_ctor_set(v___x_2581_, 1, v___x_2577_);
lean_ctor_set(v___x_2581_, 2, v___x_2579_);
lean_ctor_set(v___x_2581_, 3, v___x_2580_);
lean_inc_ref(v___x_2546_);
lean_inc(v___x_2527_);
v___x_2582_ = l_Lean_Syntax_node1(v___x_2527_, v___x_2532_, v___x_2546_);
lean_inc(v___x_2527_);
v___x_2583_ = l_Lean_Syntax_node2(v___x_2527_, v___x_2576_, v___x_2581_, v___x_2582_);
lean_inc(v___x_2527_);
v___x_2584_ = l_Lean_Syntax_node2(v___x_2527_, v___x_2573_, v___x_2575_, v___x_2583_);
v___x_2585_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__48));
lean_inc(v___x_2527_);
v___x_2586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2527_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
lean_inc(v___x_2527_);
v___x_2587_ = l_Lean_Syntax_node3(v___x_2527_, v___x_2561_, v___x_2572_, v___x_2584_, v___x_2586_);
lean_inc_ref(v___x_2538_);
lean_inc(v___x_2527_);
v___x_2588_ = l_Lean_Syntax_node2(v___x_2527_, v___x_2560_, v___x_2538_, v___x_2587_);
v___x_2589_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49));
lean_inc(v___x_2527_);
v___x_2590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2527_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51));
v___x_2592_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__53);
v___x_2593_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55));
v___x_2594_ = l_Lean_addMacroScope(v_quotContext_2522_, v___x_2593_, v_currMacroScope_2523_);
v___x_2595_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57));
lean_inc(v___x_2527_);
v___x_2596_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2527_);
lean_ctor_set(v___x_2596_, 1, v___x_2592_);
lean_ctor_set(v___x_2596_, 2, v___x_2594_);
lean_ctor_set(v___x_2596_, 3, v___x_2595_);
lean_inc(v___x_2527_);
v___x_2597_ = l_Lean_Syntax_node2(v___x_2527_, v___x_2532_, v___x_2546_, v_msg_2521_);
lean_inc(v___x_2527_);
v___x_2598_ = l_Lean_Syntax_node2(v___x_2527_, v___x_2576_, v___x_2596_, v___x_2597_);
lean_inc(v___x_2527_);
v___x_2599_ = l_Lean_Syntax_node1(v___x_2527_, v___x_2591_, v___x_2598_);
lean_inc_ref(v___x_2538_);
lean_inc(v___x_2527_);
v___x_2600_ = l_Lean_Syntax_node2(v___x_2527_, v___x_2533_, v___x_2599_, v___x_2538_);
lean_inc(v___x_2527_);
v___x_2601_ = l_Lean_Syntax_node1(v___x_2527_, v___x_2532_, v___x_2600_);
lean_inc(v___x_2527_);
v___x_2602_ = l_Lean_Syntax_node1(v___x_2527_, v___x_2531_, v___x_2601_);
lean_inc_ref_n(v___x_2538_, 2);
lean_inc(v___x_2527_);
v___x_2603_ = l_Lean_Syntax_node6(v___x_2527_, v___x_2557_, v___x_2559_, v___x_2588_, v___x_2590_, v___x_2602_, v___x_2538_, v___x_2538_);
lean_inc(v___x_2527_);
v___x_2604_ = l_Lean_Syntax_node2(v___x_2527_, v___x_2533_, v___x_2603_, v___x_2538_);
lean_inc(v___x_2527_);
v___x_2605_ = l_Lean_Syntax_node2(v___x_2527_, v___x_2532_, v___x_2556_, v___x_2604_);
lean_inc(v___x_2527_);
v___x_2606_ = l_Lean_Syntax_node1(v___x_2527_, v___x_2531_, v___x_2605_);
v___x_2607_ = l_Lean_Syntax_node2(v___x_2527_, v___x_2528_, v___x_2530_, v___x_2606_);
v___x_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v___y_2525_);
return v___x_2608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object* v_id_2649_, lean_object* v_s_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v_id_2649_, v_s_2650_, v_a_2651_, v_a_2652_);
lean_dec(v_id_2649_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object* v_x_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v___x_2711_; uint8_t v___x_2712_; 
v___x_2711_ = ((lean_object*)(l_Lean_doElemTrace_x5b___x5d_____00__closed__1));
lean_inc(v_x_2708_);
v___x_2712_ = l_Lean_Syntax_isOfKind(v_x_2708_, v___x_2711_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec_ref(v_a_2709_);
lean_dec(v_x_2708_);
v___x_2713_ = lean_box(1);
v___x_2714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v_a_2710_);
return v___x_2714_;
}
else
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v_a_2720_; lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
v___x_2715_ = lean_unsigned_to_nat(1u);
v___x_2716_ = l_Lean_Syntax_getArg(v_x_2708_, v___x_2715_);
v___x_2717_ = lean_unsigned_to_nat(3u);
v___x_2718_ = l_Lean_Syntax_getArg(v_x_2708_, v___x_2717_);
lean_dec(v_x_2708_);
v___x_2719_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v___x_2716_, v___x_2718_, v_a_2709_, v_a_2710_);
lean_dec(v___x_2716_);
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
v_a_2721_ = lean_ctor_get(v___x_2719_, 1);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2719_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_inc(v_a_2720_);
lean_dec(v___x_2719_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2720_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object* v_inst_2729_, lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_always_2733_, lean_object* v_inst_2734_, lean_object* v_cls_2735_, uint8_t v_collapsed_2736_, lean_object* v_tag_2737_, lean_object* v_opts_2738_, uint8_t v_clsEnabled_2739_, lean_object* v_oldTraces_2740_, lean_object* v_ref_2741_, lean_object* v_msg_2742_, lean_object* v_resStartStop_2743_){
_start:
{
lean_object* v___x_2744_; lean_object* v_snd_2745_; lean_object* v_fst_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2812_; 
v___x_2744_ = l_Lean_KVMap_instValueBool;
v_snd_2745_ = lean_ctor_get(v_resStartStop_2743_, 1);
v_fst_2746_ = lean_ctor_get(v_resStartStop_2743_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_resStartStop_2743_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2748_ = v_resStartStop_2743_;
v_isShared_2749_ = v_isSharedCheck_2812_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_snd_2745_);
lean_inc(v_fst_2746_);
lean_dec(v_resStartStop_2743_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2812_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v_fst_2750_; lean_object* v_snd_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2811_; 
v_fst_2750_ = lean_ctor_get(v_snd_2745_, 0);
v_snd_2751_ = lean_ctor_get(v_snd_2745_, 1);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_snd_2745_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2753_ = v_snd_2745_;
v_isShared_2754_ = v_isSharedCheck_2811_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_snd_2751_);
lean_inc(v_fst_2750_);
lean_dec(v_snd_2745_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2811_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___f_2755_; lean_object* v___f_2756_; lean_object* v___y_2758_; lean_object* v_data_2759_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___y_2785_; double v___y_2791_; uint8_t v___x_2796_; 
lean_inc_ref(v_oldTraces_2740_);
v___f_2755_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2755_, 0, v_oldTraces_2740_);
lean_inc(v_fst_2746_);
lean_inc_ref(v_inst_2729_);
v___f_2756_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2756_, 0, v_always_2733_);
lean_closure_set(v___f_2756_, 1, v_inst_2729_);
lean_closure_set(v___f_2756_, 2, v_fst_2746_);
v___x_2763_ = l_Lean_trace_profiler;
v___x_2764_ = l_Lean_Option_get___redArg(v___x_2744_, v_opts_2738_, v___x_2763_);
v___x_2796_ = lean_unbox(v___x_2764_);
if (v___x_2796_ == 0)
{
uint8_t v___x_2797_; 
v___x_2797_ = lean_unbox(v___x_2764_);
v___y_2785_ = v___x_2797_;
goto v___jp_2784_;
}
else
{
lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2798_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2799_ = l_Lean_Option_get___redArg(v___x_2744_, v_opts_2738_, v___x_2798_);
v___x_2800_ = lean_unbox(v___x_2799_);
lean_dec(v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; double v___x_2804_; double v___x_2805_; double v___x_2806_; 
v___x_2801_ = l_Lean_KVMap_instValueNat;
v___x_2802_ = l_Lean_trace_profiler_threshold;
v___x_2803_ = l_Lean_Option_get___redArg(v___x_2801_, v_opts_2738_, v___x_2802_);
v___x_2804_ = lean_float_of_nat(v___x_2803_);
v___x_2805_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_2806_ = lean_float_div(v___x_2804_, v___x_2805_);
v___y_2791_ = v___x_2806_;
goto v___jp_2790_;
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; double v___x_2810_; 
v___x_2807_ = l_Lean_KVMap_instValueNat;
v___x_2808_ = l_Lean_trace_profiler_threshold;
v___x_2809_ = l_Lean_Option_get___redArg(v___x_2807_, v_opts_2738_, v___x_2808_);
v___x_2810_ = lean_float_of_nat(v___x_2809_);
v___y_2791_ = v___x_2810_;
goto v___jp_2790_;
}
}
v___jp_2757_:
{
lean_object* v_toBind_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_toBind_2760_ = lean_ctor_get(v_inst_2729_, 1);
lean_inc(v_toBind_2760_);
v___x_2761_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_2729_, v_inst_2730_, v_inst_2731_, v_inst_2732_, v_oldTraces_2740_, v_data_2759_, v_ref_2741_, v___y_2758_);
v___x_2762_ = lean_apply_4(v_toBind_2760_, lean_box(0), lean_box(0), v___x_2761_, v___f_2756_);
return v___x_2762_;
}
v___jp_2765_:
{
lean_object* v_result_2766_; uint8_t v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v_result_2766_ = lean_apply_1(v_inst_2734_, v_fst_2746_);
v___x_2767_ = lean_unbox(v_result_2766_);
v___x_2768_ = l_Lean_TraceResult_toEmoji(v___x_2767_);
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
v___x_2770_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 7);
lean_ctor_set(v___x_2753_, 1, v___x_2770_);
lean_ctor_set(v___x_2753_, 0, v___x_2769_);
v___x_2772_ = v___x_2753_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v_msg_2774_; 
if (v_isShared_2749_ == 0)
{
lean_ctor_set_tag(v___x_2748_, 7);
lean_ctor_set(v___x_2748_, 1, v_msg_2742_);
lean_ctor_set(v___x_2748_, 0, v___x_2772_);
v_msg_2774_ = v___x_2748_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_msg_2742_);
v_msg_2774_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; double v___x_2776_; lean_object* v_data_2777_; uint8_t v___x_2778_; 
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v_result_2766_);
v___x_2776_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_2737_);
lean_inc_ref(v___x_2775_);
lean_inc(v_cls_2735_);
v_data_2777_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2777_, 0, v_cls_2735_);
lean_ctor_set(v_data_2777_, 1, v___x_2775_);
lean_ctor_set(v_data_2777_, 2, v_tag_2737_);
lean_ctor_set_float(v_data_2777_, sizeof(void*)*3, v___x_2776_);
lean_ctor_set_float(v_data_2777_, sizeof(void*)*3 + 8, v___x_2776_);
lean_ctor_set_uint8(v_data_2777_, sizeof(void*)*3 + 16, v_collapsed_2736_);
v___x_2778_ = lean_unbox(v___x_2764_);
lean_dec(v___x_2764_);
if (v___x_2778_ == 0)
{
lean_dec_ref(v___x_2775_);
lean_dec(v_snd_2751_);
lean_dec(v_fst_2750_);
lean_dec_ref(v_tag_2737_);
lean_dec(v_cls_2735_);
v___y_2758_ = v_msg_2774_;
v_data_2759_ = v_data_2777_;
goto v___jp_2757_;
}
else
{
lean_object* v_data_2779_; double v___x_2780_; double v___x_2781_; 
lean_dec_ref(v_data_2777_);
v_data_2779_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2779_, 0, v_cls_2735_);
lean_ctor_set(v_data_2779_, 1, v___x_2775_);
lean_ctor_set(v_data_2779_, 2, v_tag_2737_);
v___x_2780_ = lean_unbox_float(v_fst_2750_);
lean_dec(v_fst_2750_);
lean_ctor_set_float(v_data_2779_, sizeof(void*)*3, v___x_2780_);
v___x_2781_ = lean_unbox_float(v_snd_2751_);
lean_dec(v_snd_2751_);
lean_ctor_set_float(v_data_2779_, sizeof(void*)*3 + 8, v___x_2781_);
lean_ctor_set_uint8(v_data_2779_, sizeof(void*)*3 + 16, v_collapsed_2736_);
v___y_2758_ = v_msg_2774_;
v_data_2759_ = v_data_2779_;
goto v___jp_2757_;
}
}
}
}
v___jp_2784_:
{
if (v_clsEnabled_2739_ == 0)
{
if (v___y_2785_ == 0)
{
lean_object* v_toBind_2786_; lean_object* v_modifyTraceState_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_dec(v___x_2764_);
lean_del_object(v___x_2753_);
lean_dec(v_snd_2751_);
lean_dec(v_fst_2750_);
lean_del_object(v___x_2748_);
lean_dec(v_fst_2746_);
lean_dec_ref(v_msg_2742_);
lean_dec(v_ref_2741_);
lean_dec_ref(v_oldTraces_2740_);
lean_dec_ref(v_tag_2737_);
lean_dec(v_cls_2735_);
lean_dec_ref(v_inst_2734_);
lean_dec(v_inst_2732_);
lean_dec_ref(v_inst_2731_);
v_toBind_2786_ = lean_ctor_get(v_inst_2729_, 1);
lean_inc(v_toBind_2786_);
lean_dec_ref(v_inst_2729_);
v_modifyTraceState_2787_ = lean_ctor_get(v_inst_2730_, 0);
lean_inc(v_modifyTraceState_2787_);
lean_dec_ref(v_inst_2730_);
v___x_2788_ = lean_apply_1(v_modifyTraceState_2787_, v___f_2755_);
v___x_2789_ = lean_apply_4(v_toBind_2786_, lean_box(0), lean_box(0), v___x_2788_, v___f_2756_);
return v___x_2789_;
}
else
{
lean_dec_ref(v___f_2755_);
goto v___jp_2765_;
}
}
else
{
lean_dec_ref(v___f_2755_);
goto v___jp_2765_;
}
}
v___jp_2790_:
{
double v___x_2792_; double v___x_2793_; double v___x_2794_; uint8_t v___x_2795_; 
v___x_2792_ = lean_unbox_float(v_snd_2751_);
v___x_2793_ = lean_unbox_float(v_fst_2750_);
v___x_2794_ = lean_float_sub(v___x_2792_, v___x_2793_);
v___x_2795_ = lean_float_decLt(v___y_2791_, v___x_2794_);
v___y_2785_ = v___x_2795_;
goto v___jp_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object* v_inst_2813_, lean_object* v_inst_2814_, lean_object* v_inst_2815_, lean_object* v_inst_2816_, lean_object* v_always_2817_, lean_object* v_inst_2818_, lean_object* v_cls_2819_, lean_object* v_collapsed_2820_, lean_object* v_tag_2821_, lean_object* v_opts_2822_, lean_object* v_clsEnabled_2823_, lean_object* v_oldTraces_2824_, lean_object* v_ref_2825_, lean_object* v_msg_2826_, lean_object* v_resStartStop_2827_){
_start:
{
uint8_t v_collapsed_boxed_2828_; uint8_t v_clsEnabled_boxed_2829_; lean_object* v_res_2830_; 
v_collapsed_boxed_2828_ = lean_unbox(v_collapsed_2820_);
v_clsEnabled_boxed_2829_ = lean_unbox(v_clsEnabled_2823_);
v_res_2830_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2813_, v_inst_2814_, v_inst_2815_, v_inst_2816_, v_always_2817_, v_inst_2818_, v_cls_2819_, v_collapsed_boxed_2828_, v_tag_2821_, v_opts_2822_, v_clsEnabled_boxed_2829_, v_oldTraces_2824_, v_ref_2825_, v_msg_2826_, v_resStartStop_2827_);
lean_dec_ref(v_opts_2822_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object* v_00_u03b1_2831_, lean_object* v_m_2832_, lean_object* v_inst_2833_, lean_object* v_inst_2834_, lean_object* v_00_u03b5_2835_, lean_object* v_inst_2836_, lean_object* v_inst_2837_, lean_object* v_always_2838_, lean_object* v_inst_2839_, lean_object* v_cls_2840_, uint8_t v_collapsed_2841_, lean_object* v_tag_2842_, lean_object* v_opts_2843_, uint8_t v_clsEnabled_2844_, lean_object* v_oldTraces_2845_, lean_object* v_ref_2846_, lean_object* v_msg_2847_, lean_object* v_resStartStop_2848_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2833_, v_inst_2834_, v_inst_2836_, v_inst_2837_, v_always_2838_, v_inst_2839_, v_cls_2840_, v_collapsed_2841_, v_tag_2842_, v_opts_2843_, v_clsEnabled_2844_, v_oldTraces_2845_, v_ref_2846_, v_msg_2847_, v_resStartStop_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_2850_ = _args[0];
lean_object* v_m_2851_ = _args[1];
lean_object* v_inst_2852_ = _args[2];
lean_object* v_inst_2853_ = _args[3];
lean_object* v_00_u03b5_2854_ = _args[4];
lean_object* v_inst_2855_ = _args[5];
lean_object* v_inst_2856_ = _args[6];
lean_object* v_always_2857_ = _args[7];
lean_object* v_inst_2858_ = _args[8];
lean_object* v_cls_2859_ = _args[9];
lean_object* v_collapsed_2860_ = _args[10];
lean_object* v_tag_2861_ = _args[11];
lean_object* v_opts_2862_ = _args[12];
lean_object* v_clsEnabled_2863_ = _args[13];
lean_object* v_oldTraces_2864_ = _args[14];
lean_object* v_ref_2865_ = _args[15];
lean_object* v_msg_2866_ = _args[16];
lean_object* v_resStartStop_2867_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2868_; uint8_t v_clsEnabled_boxed_2869_; lean_object* v_res_2870_; 
v_collapsed_boxed_2868_ = lean_unbox(v_collapsed_2860_);
v_clsEnabled_boxed_2869_ = lean_unbox(v_clsEnabled_2863_);
v_res_2870_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(v_00_u03b1_2850_, v_m_2851_, v_inst_2852_, v_inst_2853_, v_00_u03b5_2854_, v_inst_2855_, v_inst_2856_, v_always_2857_, v_inst_2858_, v_cls_2859_, v_collapsed_boxed_2868_, v_tag_2861_, v_opts_2862_, v_clsEnabled_boxed_2869_, v_oldTraces_2864_, v_ref_2865_, v_msg_2866_, v_resStartStop_2867_);
lean_dec_ref(v_opts_2862_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object* v_inst_2871_, lean_object* v_____do__lift_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = lean_apply_1(v_inst_2871_, v_____do__lift_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_always_2878_, lean_object* v_inst_2879_, lean_object* v_cls_2880_, uint8_t v_collapsed_2881_, lean_object* v_tag_2882_, lean_object* v_opts_2883_, uint8_t v_clsEnabled_2884_, lean_object* v_oldTraces_2885_, lean_object* v_ref_2886_, lean_object* v_msg_2887_, lean_object* v_resStartStop_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2874_, v_inst_2875_, v_inst_2876_, v_inst_2877_, v_always_2878_, v_inst_2879_, v_cls_2880_, v_collapsed_2881_, v_tag_2882_, v_opts_2883_, v_clsEnabled_2884_, v_oldTraces_2885_, v_ref_2886_, v_msg_2887_, v_resStartStop_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_always_2894_, lean_object* v_inst_2895_, lean_object* v_cls_2896_, lean_object* v_collapsed_2897_, lean_object* v_tag_2898_, lean_object* v_opts_2899_, lean_object* v_clsEnabled_2900_, lean_object* v_oldTraces_2901_, lean_object* v_ref_2902_, lean_object* v_msg_2903_, lean_object* v_resStartStop_2904_){
_start:
{
uint8_t v_collapsed_boxed_2905_; uint8_t v_clsEnabled_boxed_2906_; lean_object* v_res_2907_; 
v_collapsed_boxed_2905_ = lean_unbox(v_collapsed_2897_);
v_clsEnabled_boxed_2906_ = lean_unbox(v_clsEnabled_2900_);
v_res_2907_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_2890_, v_inst_2891_, v_inst_2892_, v_inst_2893_, v_always_2894_, v_inst_2895_, v_cls_2896_, v_collapsed_boxed_2905_, v_tag_2898_, v_opts_2899_, v_clsEnabled_boxed_2906_, v_oldTraces_2901_, v_ref_2902_, v_msg_2903_, v_resStartStop_2904_);
lean_dec_ref(v_opts_2899_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object* v_toApplicative_2908_, lean_object* v_always_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_inst_2914_, lean_object* v_cls_2915_, uint8_t v_collapsed_2916_, lean_object* v_tag_2917_, lean_object* v_opts_2918_, uint8_t v_clsEnabled_2919_, lean_object* v_oldTraces_2920_, lean_object* v_ref_2921_, lean_object* v_toBind_2922_, lean_object* v_k_2923_, lean_object* v_inst_2924_, lean_object* v_msg_2925_){
_start:
{
lean_object* v_toPure_2926_; lean_object* v_tryCatch_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___f_2930_; lean_object* v___f_2931_; lean_object* v___f_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v_toPure_2926_ = lean_ctor_get(v_toApplicative_2908_, 1);
lean_inc(v_toPure_2926_);
lean_dec_ref(v_toApplicative_2908_);
v_tryCatch_2927_ = lean_ctor_get(v_always_2909_, 1);
lean_inc(v_tryCatch_2927_);
v___x_2928_ = lean_box(v_collapsed_2916_);
v___x_2929_ = lean_box(v_clsEnabled_2919_);
lean_inc_ref(v_opts_2918_);
v___f_2930_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__1___boxed), 15, 14);
lean_closure_set(v___f_2930_, 0, v_inst_2910_);
lean_closure_set(v___f_2930_, 1, v_inst_2911_);
lean_closure_set(v___f_2930_, 2, v_inst_2912_);
lean_closure_set(v___f_2930_, 3, v_inst_2913_);
lean_closure_set(v___f_2930_, 4, v_always_2909_);
lean_closure_set(v___f_2930_, 5, v_inst_2914_);
lean_closure_set(v___f_2930_, 6, v_cls_2915_);
lean_closure_set(v___f_2930_, 7, v___x_2928_);
lean_closure_set(v___f_2930_, 8, v_tag_2917_);
lean_closure_set(v___f_2930_, 9, v_opts_2918_);
lean_closure_set(v___f_2930_, 10, v___x_2929_);
lean_closure_set(v___f_2930_, 11, v_oldTraces_2920_);
lean_closure_set(v___f_2930_, 12, v_ref_2921_);
lean_closure_set(v___f_2930_, 13, v_msg_2925_);
lean_inc(v_toPure_2926_);
v___f_2931_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2931_, 0, v_toPure_2926_);
lean_inc(v_toPure_2926_);
v___f_2932_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2932_, 0, v_toPure_2926_);
lean_inc(v_toBind_2922_);
v___x_2933_ = lean_apply_4(v_toBind_2922_, lean_box(0), lean_box(0), v_k_2923_, v___f_2932_);
v___x_2934_ = lean_apply_3(v_tryCatch_2927_, lean_box(0), v___x_2933_, v___f_2931_);
v___x_2935_ = l_Lean_KVMap_instValueBool;
v___x_2936_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2937_ = l_Lean_Option_get___redArg(v___x_2935_, v_opts_2918_, v___x_2936_);
lean_dec_ref(v_opts_2918_);
v___x_2938_ = lean_unbox(v___x_2937_);
lean_dec(v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___f_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2939_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_2940_ = lean_apply_2(v_inst_2924_, lean_box(0), v___x_2939_);
lean_inc(v___x_2940_);
lean_inc(v_toBind_2922_);
v___f_2941_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_2941_, 0, v_toPure_2926_);
lean_closure_set(v___f_2941_, 1, v_toBind_2922_);
lean_closure_set(v___f_2941_, 2, v___x_2940_);
lean_closure_set(v___f_2941_, 3, v___x_2934_);
lean_inc(v_toBind_2922_);
v___x_2942_ = lean_apply_4(v_toBind_2922_, lean_box(0), lean_box(0), v___x_2940_, v___f_2941_);
v___x_2943_ = lean_apply_4(v_toBind_2922_, lean_box(0), lean_box(0), v___x_2942_, v___f_2930_);
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___f_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2944_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_2945_ = lean_apply_2(v_inst_2924_, lean_box(0), v___x_2944_);
lean_inc(v___x_2945_);
lean_inc(v_toBind_2922_);
v___f_2946_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_2946_, 0, v_toPure_2926_);
lean_closure_set(v___f_2946_, 1, v_toBind_2922_);
lean_closure_set(v___f_2946_, 2, v___x_2945_);
lean_closure_set(v___f_2946_, 3, v___x_2934_);
lean_inc(v_toBind_2922_);
v___x_2947_ = lean_apply_4(v_toBind_2922_, lean_box(0), lean_box(0), v___x_2945_, v___f_2946_);
v___x_2948_ = lean_apply_4(v_toBind_2922_, lean_box(0), lean_box(0), v___x_2947_, v___f_2930_);
return v___x_2948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_toApplicative_2949_ = _args[0];
lean_object* v_always_2950_ = _args[1];
lean_object* v_inst_2951_ = _args[2];
lean_object* v_inst_2952_ = _args[3];
lean_object* v_inst_2953_ = _args[4];
lean_object* v_inst_2954_ = _args[5];
lean_object* v_inst_2955_ = _args[6];
lean_object* v_cls_2956_ = _args[7];
lean_object* v_collapsed_2957_ = _args[8];
lean_object* v_tag_2958_ = _args[9];
lean_object* v_opts_2959_ = _args[10];
lean_object* v_clsEnabled_2960_ = _args[11];
lean_object* v_oldTraces_2961_ = _args[12];
lean_object* v_ref_2962_ = _args[13];
lean_object* v_toBind_2963_ = _args[14];
lean_object* v_k_2964_ = _args[15];
lean_object* v_inst_2965_ = _args[16];
lean_object* v_msg_2966_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2967_; uint8_t v_clsEnabled_boxed_2968_; lean_object* v_res_2969_; 
v_collapsed_boxed_2967_ = lean_unbox(v_collapsed_2957_);
v_clsEnabled_boxed_2968_ = lean_unbox(v_clsEnabled_2960_);
v_res_2969_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_toApplicative_2949_, v_always_2950_, v_inst_2951_, v_inst_2952_, v_inst_2953_, v_inst_2954_, v_inst_2955_, v_cls_2956_, v_collapsed_boxed_2967_, v_tag_2958_, v_opts_2959_, v_clsEnabled_boxed_2968_, v_oldTraces_2961_, v_ref_2962_, v_toBind_2963_, v_k_2964_, v_inst_2965_, v_msg_2966_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object* v_toApplicative_2970_, lean_object* v_always_2971_, lean_object* v_inst_2972_, lean_object* v_inst_2973_, lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_inst_2976_, lean_object* v_cls_2977_, uint8_t v_collapsed_2978_, lean_object* v_tag_2979_, lean_object* v_opts_2980_, uint8_t v_clsEnabled_2981_, lean_object* v_oldTraces_2982_, lean_object* v_toBind_2983_, lean_object* v_k_2984_, lean_object* v_inst_2985_, lean_object* v_msg_2986_, lean_object* v___f_2987_, lean_object* v_withRef_2988_, lean_object* v_getRef_2989_, lean_object* v_ref_2990_){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___f_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___f_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2991_ = lean_box(v_collapsed_2978_);
v___x_2992_ = lean_box(v_clsEnabled_2981_);
lean_inc(v_toBind_2983_);
lean_inc(v_ref_2990_);
v___f_2993_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__10___boxed), 18, 17);
lean_closure_set(v___f_2993_, 0, v_toApplicative_2970_);
lean_closure_set(v___f_2993_, 1, v_always_2971_);
lean_closure_set(v___f_2993_, 2, v_inst_2972_);
lean_closure_set(v___f_2993_, 3, v_inst_2973_);
lean_closure_set(v___f_2993_, 4, v_inst_2974_);
lean_closure_set(v___f_2993_, 5, v_inst_2975_);
lean_closure_set(v___f_2993_, 6, v_inst_2976_);
lean_closure_set(v___f_2993_, 7, v_cls_2977_);
lean_closure_set(v___f_2993_, 8, v___x_2991_);
lean_closure_set(v___f_2993_, 9, v_tag_2979_);
lean_closure_set(v___f_2993_, 10, v_opts_2980_);
lean_closure_set(v___f_2993_, 11, v___x_2992_);
lean_closure_set(v___f_2993_, 12, v_oldTraces_2982_);
lean_closure_set(v___f_2993_, 13, v_ref_2990_);
lean_closure_set(v___f_2993_, 14, v_toBind_2983_);
lean_closure_set(v___f_2993_, 15, v_k_2984_);
lean_closure_set(v___f_2993_, 16, v_inst_2985_);
v___x_2994_ = lean_box(0);
v___x_2995_ = lean_apply_1(v_msg_2986_, v___x_2994_);
lean_inc(v_toBind_2983_);
v___x_2996_ = lean_apply_4(v_toBind_2983_, lean_box(0), lean_box(0), v___x_2995_, v___f_2987_);
v___f_2997_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_2997_, 0, v_ref_2990_);
lean_closure_set(v___f_2997_, 1, v_withRef_2988_);
lean_closure_set(v___f_2997_, 2, v___x_2996_);
lean_inc(v_toBind_2983_);
v___x_2998_ = lean_apply_4(v_toBind_2983_, lean_box(0), lean_box(0), v_getRef_2989_, v___f_2997_);
v___x_2999_ = lean_apply_4(v_toBind_2983_, lean_box(0), lean_box(0), v___x_2998_, v___f_2993_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_toApplicative_3000_ = _args[0];
lean_object* v_always_3001_ = _args[1];
lean_object* v_inst_3002_ = _args[2];
lean_object* v_inst_3003_ = _args[3];
lean_object* v_inst_3004_ = _args[4];
lean_object* v_inst_3005_ = _args[5];
lean_object* v_inst_3006_ = _args[6];
lean_object* v_cls_3007_ = _args[7];
lean_object* v_collapsed_3008_ = _args[8];
lean_object* v_tag_3009_ = _args[9];
lean_object* v_opts_3010_ = _args[10];
lean_object* v_clsEnabled_3011_ = _args[11];
lean_object* v_oldTraces_3012_ = _args[12];
lean_object* v_toBind_3013_ = _args[13];
lean_object* v_k_3014_ = _args[14];
lean_object* v_inst_3015_ = _args[15];
lean_object* v_msg_3016_ = _args[16];
lean_object* v___f_3017_ = _args[17];
lean_object* v_withRef_3018_ = _args[18];
lean_object* v_getRef_3019_ = _args[19];
lean_object* v_ref_3020_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_3021_; uint8_t v_clsEnabled_boxed_3022_; lean_object* v_res_3023_; 
v_collapsed_boxed_3021_ = lean_unbox(v_collapsed_3008_);
v_clsEnabled_boxed_3022_ = lean_unbox(v_clsEnabled_3011_);
v_res_3023_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_toApplicative_3000_, v_always_3001_, v_inst_3002_, v_inst_3003_, v_inst_3004_, v_inst_3005_, v_inst_3006_, v_cls_3007_, v_collapsed_boxed_3021_, v_tag_3009_, v_opts_3010_, v_clsEnabled_boxed_3022_, v_oldTraces_3012_, v_toBind_3013_, v_k_3014_, v_inst_3015_, v_msg_3016_, v___f_3017_, v_withRef_3018_, v_getRef_3019_, v_ref_3020_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object* v_inst_3024_, lean_object* v_toApplicative_3025_, lean_object* v_always_3026_, lean_object* v_inst_3027_, lean_object* v_inst_3028_, lean_object* v_inst_3029_, lean_object* v_inst_3030_, lean_object* v_cls_3031_, uint8_t v_collapsed_3032_, lean_object* v_tag_3033_, lean_object* v_opts_3034_, uint8_t v_clsEnabled_3035_, lean_object* v_toBind_3036_, lean_object* v_k_3037_, lean_object* v_inst_3038_, lean_object* v_msg_3039_, lean_object* v___f_3040_, lean_object* v_oldTraces_3041_){
_start:
{
lean_object* v_getRef_3042_; lean_object* v_withRef_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___f_3046_; lean_object* v___x_3047_; 
v_getRef_3042_ = lean_ctor_get(v_inst_3024_, 0);
lean_inc(v_getRef_3042_);
v_withRef_3043_ = lean_ctor_get(v_inst_3024_, 1);
lean_inc(v_withRef_3043_);
v___x_3044_ = lean_box(v_collapsed_3032_);
v___x_3045_ = lean_box(v_clsEnabled_3035_);
lean_inc(v_getRef_3042_);
lean_inc(v_toBind_3036_);
v___f_3046_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__3___boxed), 21, 20);
lean_closure_set(v___f_3046_, 0, v_toApplicative_3025_);
lean_closure_set(v___f_3046_, 1, v_always_3026_);
lean_closure_set(v___f_3046_, 2, v_inst_3027_);
lean_closure_set(v___f_3046_, 3, v_inst_3028_);
lean_closure_set(v___f_3046_, 4, v_inst_3024_);
lean_closure_set(v___f_3046_, 5, v_inst_3029_);
lean_closure_set(v___f_3046_, 6, v_inst_3030_);
lean_closure_set(v___f_3046_, 7, v_cls_3031_);
lean_closure_set(v___f_3046_, 8, v___x_3044_);
lean_closure_set(v___f_3046_, 9, v_tag_3033_);
lean_closure_set(v___f_3046_, 10, v_opts_3034_);
lean_closure_set(v___f_3046_, 11, v___x_3045_);
lean_closure_set(v___f_3046_, 12, v_oldTraces_3041_);
lean_closure_set(v___f_3046_, 13, v_toBind_3036_);
lean_closure_set(v___f_3046_, 14, v_k_3037_);
lean_closure_set(v___f_3046_, 15, v_inst_3038_);
lean_closure_set(v___f_3046_, 16, v_msg_3039_);
lean_closure_set(v___f_3046_, 17, v___f_3040_);
lean_closure_set(v___f_3046_, 18, v_withRef_3043_);
lean_closure_set(v___f_3046_, 19, v_getRef_3042_);
v___x_3047_ = lean_apply_4(v_toBind_3036_, lean_box(0), lean_box(0), v_getRef_3042_, v___f_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_3048_ = _args[0];
lean_object* v_toApplicative_3049_ = _args[1];
lean_object* v_always_3050_ = _args[2];
lean_object* v_inst_3051_ = _args[3];
lean_object* v_inst_3052_ = _args[4];
lean_object* v_inst_3053_ = _args[5];
lean_object* v_inst_3054_ = _args[6];
lean_object* v_cls_3055_ = _args[7];
lean_object* v_collapsed_3056_ = _args[8];
lean_object* v_tag_3057_ = _args[9];
lean_object* v_opts_3058_ = _args[10];
lean_object* v_clsEnabled_3059_ = _args[11];
lean_object* v_toBind_3060_ = _args[12];
lean_object* v_k_3061_ = _args[13];
lean_object* v_inst_3062_ = _args[14];
lean_object* v_msg_3063_ = _args[15];
lean_object* v___f_3064_ = _args[16];
lean_object* v_oldTraces_3065_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3066_; uint8_t v_clsEnabled_boxed_3067_; lean_object* v_res_3068_; 
v_collapsed_boxed_3066_ = lean_unbox(v_collapsed_3056_);
v_clsEnabled_boxed_3067_ = lean_unbox(v_clsEnabled_3059_);
v_res_3068_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3048_, v_toApplicative_3049_, v_always_3050_, v_inst_3051_, v_inst_3052_, v_inst_3053_, v_inst_3054_, v_cls_3055_, v_collapsed_boxed_3066_, v_tag_3057_, v_opts_3058_, v_clsEnabled_boxed_3067_, v_toBind_3060_, v_k_3061_, v_inst_3062_, v_msg_3063_, v___f_3064_, v_oldTraces_3065_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object* v_inst_3069_, lean_object* v_toApplicative_3070_, lean_object* v_always_3071_, lean_object* v_inst_3072_, lean_object* v_inst_3073_, lean_object* v_inst_3074_, lean_object* v_inst_3075_, lean_object* v_cls_3076_, uint8_t v_collapsed_3077_, lean_object* v_tag_3078_, lean_object* v_opts_3079_, lean_object* v_toBind_3080_, lean_object* v_k_3081_, lean_object* v_inst_3082_, lean_object* v_msg_3083_, lean_object* v___f_3084_, uint8_t v_clsEnabled_3085_){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___f_3088_; 
v___x_3086_ = lean_box(v_collapsed_3077_);
v___x_3087_ = lean_box(v_clsEnabled_3085_);
lean_inc(v_k_3081_);
lean_inc(v_toBind_3080_);
lean_inc_ref(v_opts_3079_);
lean_inc_ref(v_inst_3073_);
lean_inc_ref(v_inst_3072_);
v___f_3088_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__2___boxed), 18, 17);
lean_closure_set(v___f_3088_, 0, v_inst_3069_);
lean_closure_set(v___f_3088_, 1, v_toApplicative_3070_);
lean_closure_set(v___f_3088_, 2, v_always_3071_);
lean_closure_set(v___f_3088_, 3, v_inst_3072_);
lean_closure_set(v___f_3088_, 4, v_inst_3073_);
lean_closure_set(v___f_3088_, 5, v_inst_3074_);
lean_closure_set(v___f_3088_, 6, v_inst_3075_);
lean_closure_set(v___f_3088_, 7, v_cls_3076_);
lean_closure_set(v___f_3088_, 8, v___x_3086_);
lean_closure_set(v___f_3088_, 9, v_tag_3078_);
lean_closure_set(v___f_3088_, 10, v_opts_3079_);
lean_closure_set(v___f_3088_, 11, v___x_3087_);
lean_closure_set(v___f_3088_, 12, v_toBind_3080_);
lean_closure_set(v___f_3088_, 13, v_k_3081_);
lean_closure_set(v___f_3088_, 14, v_inst_3082_);
lean_closure_set(v___f_3088_, 15, v_msg_3083_);
lean_closure_set(v___f_3088_, 16, v___f_3084_);
if (v_clsEnabled_3085_ == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3092_ = l_Lean_KVMap_instValueBool;
v___x_3093_ = l_Lean_trace_profiler;
v___x_3094_ = l_Lean_Option_get___redArg(v___x_3092_, v_opts_3079_, v___x_3093_);
lean_dec_ref(v_opts_3079_);
v___x_3095_ = lean_unbox(v___x_3094_);
lean_dec(v___x_3094_);
if (v___x_3095_ == 0)
{
lean_dec_ref(v___f_3088_);
lean_dec(v_toBind_3080_);
lean_dec_ref(v_inst_3073_);
lean_dec_ref(v_inst_3072_);
return v_k_3081_;
}
else
{
lean_dec(v_k_3081_);
goto v___jp_3089_;
}
}
else
{
lean_dec(v_k_3081_);
lean_dec_ref(v_opts_3079_);
goto v___jp_3089_;
}
v___jp_3089_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3072_, v_inst_3073_);
v___x_3091_ = lean_apply_4(v_toBind_3080_, lean_box(0), lean_box(0), v___x_3090_, v___f_3088_);
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_3096_ = _args[0];
lean_object* v_toApplicative_3097_ = _args[1];
lean_object* v_always_3098_ = _args[2];
lean_object* v_inst_3099_ = _args[3];
lean_object* v_inst_3100_ = _args[4];
lean_object* v_inst_3101_ = _args[5];
lean_object* v_inst_3102_ = _args[6];
lean_object* v_cls_3103_ = _args[7];
lean_object* v_collapsed_3104_ = _args[8];
lean_object* v_tag_3105_ = _args[9];
lean_object* v_opts_3106_ = _args[10];
lean_object* v_toBind_3107_ = _args[11];
lean_object* v_k_3108_ = _args[12];
lean_object* v_inst_3109_ = _args[13];
lean_object* v_msg_3110_ = _args[14];
lean_object* v___f_3111_ = _args[15];
lean_object* v_clsEnabled_3112_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3113_; uint8_t v_clsEnabled_boxed_3114_; lean_object* v_res_3115_; 
v_collapsed_boxed_3113_ = lean_unbox(v_collapsed_3104_);
v_clsEnabled_boxed_3114_ = lean_unbox(v_clsEnabled_3112_);
v_res_3115_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3096_, v_toApplicative_3097_, v_always_3098_, v_inst_3099_, v_inst_3100_, v_inst_3101_, v_inst_3102_, v_cls_3103_, v_collapsed_boxed_3113_, v_tag_3105_, v_opts_3106_, v_toBind_3107_, v_k_3108_, v_inst_3109_, v_msg_3110_, v___f_3111_, v_clsEnabled_boxed_3114_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__5(lean_object* v_k_3116_, lean_object* v_inst_3117_, lean_object* v_toApplicative_3118_, lean_object* v_always_3119_, lean_object* v_inst_3120_, lean_object* v_inst_3121_, lean_object* v_inst_3122_, lean_object* v_inst_3123_, lean_object* v_cls_3124_, uint8_t v_collapsed_3125_, lean_object* v_tag_3126_, lean_object* v_toBind_3127_, lean_object* v_inst_3128_, lean_object* v_msg_3129_, lean_object* v___f_3130_, lean_object* v_inst_3131_, lean_object* v_opts_3132_){
_start:
{
uint8_t v_hasTrace_3133_; 
v_hasTrace_3133_ = lean_ctor_get_uint8(v_opts_3132_, sizeof(void*)*1);
if (v_hasTrace_3133_ == 0)
{
lean_dec_ref(v_opts_3132_);
lean_dec(v_inst_3131_);
lean_dec(v___f_3130_);
lean_dec(v_msg_3129_);
lean_dec(v_inst_3128_);
lean_dec(v_toBind_3127_);
lean_dec_ref(v_tag_3126_);
lean_dec(v_cls_3124_);
lean_dec_ref(v_inst_3123_);
lean_dec(v_inst_3122_);
lean_dec_ref(v_inst_3121_);
lean_dec_ref(v_inst_3120_);
lean_dec_ref(v_always_3119_);
lean_dec_ref(v_toApplicative_3118_);
lean_dec_ref(v_inst_3117_);
return v_k_3116_;
}
else
{
lean_object* v___x_3134_; lean_object* v___f_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3134_ = lean_box(v_collapsed_3125_);
lean_inc(v_toBind_3127_);
lean_inc(v_cls_3124_);
lean_inc_ref(v_inst_3121_);
lean_inc_ref(v_inst_3120_);
v___f_3135_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_3135_, 0, v_inst_3117_);
lean_closure_set(v___f_3135_, 1, v_toApplicative_3118_);
lean_closure_set(v___f_3135_, 2, v_always_3119_);
lean_closure_set(v___f_3135_, 3, v_inst_3120_);
lean_closure_set(v___f_3135_, 4, v_inst_3121_);
lean_closure_set(v___f_3135_, 5, v_inst_3122_);
lean_closure_set(v___f_3135_, 6, v_inst_3123_);
lean_closure_set(v___f_3135_, 7, v_cls_3124_);
lean_closure_set(v___f_3135_, 8, v___x_3134_);
lean_closure_set(v___f_3135_, 9, v_tag_3126_);
lean_closure_set(v___f_3135_, 10, v_opts_3132_);
lean_closure_set(v___f_3135_, 11, v_toBind_3127_);
lean_closure_set(v___f_3135_, 12, v_k_3116_);
lean_closure_set(v___f_3135_, 13, v_inst_3128_);
lean_closure_set(v___f_3135_, 14, v_msg_3129_);
lean_closure_set(v___f_3135_, 15, v___f_3130_);
v___x_3136_ = l_Lean_isTracingEnabledFor___redArg(v_inst_3120_, v_inst_3121_, v_inst_3131_, v_cls_3124_);
v___x_3137_ = lean_apply_4(v_toBind_3127_, lean_box(0), lean_box(0), v___x_3136_, v___f_3135_);
return v___x_3137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_k_3138_ = _args[0];
lean_object* v_inst_3139_ = _args[1];
lean_object* v_toApplicative_3140_ = _args[2];
lean_object* v_always_3141_ = _args[3];
lean_object* v_inst_3142_ = _args[4];
lean_object* v_inst_3143_ = _args[5];
lean_object* v_inst_3144_ = _args[6];
lean_object* v_inst_3145_ = _args[7];
lean_object* v_cls_3146_ = _args[8];
lean_object* v_collapsed_3147_ = _args[9];
lean_object* v_tag_3148_ = _args[10];
lean_object* v_toBind_3149_ = _args[11];
lean_object* v_inst_3150_ = _args[12];
lean_object* v_msg_3151_ = _args[13];
lean_object* v___f_3152_ = _args[14];
lean_object* v_inst_3153_ = _args[15];
lean_object* v_opts_3154_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3155_; lean_object* v_res_3156_; 
v_collapsed_boxed_3155_ = lean_unbox(v_collapsed_3147_);
v_res_3156_ = l_Lean_withTraceNodeBefore___redArg___lam__5(v_k_3138_, v_inst_3139_, v_toApplicative_3140_, v_always_3141_, v_inst_3142_, v_inst_3143_, v_inst_3144_, v_inst_3145_, v_cls_3146_, v_collapsed_boxed_3155_, v_tag_3148_, v_toBind_3149_, v_inst_3150_, v_msg_3151_, v___f_3152_, v_inst_3153_, v_opts_3154_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object* v_inst_3157_, lean_object* v_inst_3158_, lean_object* v_inst_3159_, lean_object* v_inst_3160_, lean_object* v_inst_3161_, lean_object* v_always_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_cls_3165_, lean_object* v_msg_3166_, lean_object* v_k_3167_, uint8_t v_collapsed_3168_, lean_object* v_tag_3169_){
_start:
{
lean_object* v_toApplicative_3170_; lean_object* v_toBind_3171_; lean_object* v___f_3172_; lean_object* v___x_3173_; lean_object* v___f_3174_; lean_object* v___x_3175_; 
v_toApplicative_3170_ = lean_ctor_get(v_inst_3157_, 0);
lean_inc_ref(v_toApplicative_3170_);
v_toBind_3171_ = lean_ctor_get(v_inst_3157_, 1);
lean_inc(v_toBind_3171_);
lean_inc(v_inst_3160_);
v___f_3172_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3172_, 0, v_inst_3160_);
v___x_3173_ = lean_box(v_collapsed_3168_);
lean_inc(v_inst_3161_);
lean_inc(v_toBind_3171_);
v___f_3174_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_3174_, 0, v_k_3167_);
lean_closure_set(v___f_3174_, 1, v_inst_3159_);
lean_closure_set(v___f_3174_, 2, v_toApplicative_3170_);
lean_closure_set(v___f_3174_, 3, v_always_3162_);
lean_closure_set(v___f_3174_, 4, v_inst_3157_);
lean_closure_set(v___f_3174_, 5, v_inst_3158_);
lean_closure_set(v___f_3174_, 6, v_inst_3160_);
lean_closure_set(v___f_3174_, 7, v_inst_3164_);
lean_closure_set(v___f_3174_, 8, v_cls_3165_);
lean_closure_set(v___f_3174_, 9, v___x_3173_);
lean_closure_set(v___f_3174_, 10, v_tag_3169_);
lean_closure_set(v___f_3174_, 11, v_toBind_3171_);
lean_closure_set(v___f_3174_, 12, v_inst_3163_);
lean_closure_set(v___f_3174_, 13, v_msg_3166_);
lean_closure_set(v___f_3174_, 14, v___f_3172_);
lean_closure_set(v___f_3174_, 15, v_inst_3161_);
v___x_3175_ = lean_apply_4(v_toBind_3171_, lean_box(0), lean_box(0), v_inst_3161_, v___f_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_inst_3180_, lean_object* v_always_3181_, lean_object* v_inst_3182_, lean_object* v_inst_3183_, lean_object* v_cls_3184_, lean_object* v_msg_3185_, lean_object* v_k_3186_, lean_object* v_collapsed_3187_, lean_object* v_tag_3188_){
_start:
{
uint8_t v_collapsed_boxed_3189_; lean_object* v_res_3190_; 
v_collapsed_boxed_3189_ = lean_unbox(v_collapsed_3187_);
v_res_3190_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3176_, v_inst_3177_, v_inst_3178_, v_inst_3179_, v_inst_3180_, v_always_3181_, v_inst_3182_, v_inst_3183_, v_cls_3184_, v_msg_3185_, v_k_3186_, v_collapsed_boxed_3189_, v_tag_3188_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object* v_00_u03b1_3191_, lean_object* v_m_3192_, lean_object* v_inst_3193_, lean_object* v_inst_3194_, lean_object* v_00_u03b5_3195_, lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_always_3199_, lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_cls_3202_, lean_object* v_msg_3203_, lean_object* v_k_3204_, uint8_t v_collapsed_3205_, lean_object* v_tag_3206_){
_start:
{
lean_object* v_toApplicative_3207_; lean_object* v_toBind_3208_; lean_object* v___f_3209_; lean_object* v___x_3210_; lean_object* v___f_3211_; lean_object* v___x_3212_; 
v_toApplicative_3207_ = lean_ctor_get(v_inst_3193_, 0);
lean_inc_ref(v_toApplicative_3207_);
v_toBind_3208_ = lean_ctor_get(v_inst_3193_, 1);
lean_inc(v_toBind_3208_);
lean_inc(v_inst_3197_);
v___f_3209_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3209_, 0, v_inst_3197_);
v___x_3210_ = lean_box(v_collapsed_3205_);
lean_inc(v_inst_3198_);
lean_inc(v_toBind_3208_);
v___f_3211_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_3211_, 0, v_k_3204_);
lean_closure_set(v___f_3211_, 1, v_inst_3196_);
lean_closure_set(v___f_3211_, 2, v_toApplicative_3207_);
lean_closure_set(v___f_3211_, 3, v_always_3199_);
lean_closure_set(v___f_3211_, 4, v_inst_3193_);
lean_closure_set(v___f_3211_, 5, v_inst_3194_);
lean_closure_set(v___f_3211_, 6, v_inst_3197_);
lean_closure_set(v___f_3211_, 7, v_inst_3201_);
lean_closure_set(v___f_3211_, 8, v_cls_3202_);
lean_closure_set(v___f_3211_, 9, v___x_3210_);
lean_closure_set(v___f_3211_, 10, v_tag_3206_);
lean_closure_set(v___f_3211_, 11, v_toBind_3208_);
lean_closure_set(v___f_3211_, 12, v_inst_3200_);
lean_closure_set(v___f_3211_, 13, v_msg_3203_);
lean_closure_set(v___f_3211_, 14, v___f_3209_);
lean_closure_set(v___f_3211_, 15, v_inst_3198_);
v___x_3212_ = lean_apply_4(v_toBind_3208_, lean_box(0), lean_box(0), v_inst_3198_, v___f_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object* v_00_u03b1_3213_, lean_object* v_m_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_00_u03b5_3217_, lean_object* v_inst_3218_, lean_object* v_inst_3219_, lean_object* v_inst_3220_, lean_object* v_always_3221_, lean_object* v_inst_3222_, lean_object* v_inst_3223_, lean_object* v_cls_3224_, lean_object* v_msg_3225_, lean_object* v_k_3226_, lean_object* v_collapsed_3227_, lean_object* v_tag_3228_){
_start:
{
uint8_t v_collapsed_boxed_3229_; lean_object* v_res_3230_; 
v_collapsed_boxed_3229_ = lean_unbox(v_collapsed_3227_);
v_res_3230_ = l_Lean_withTraceNodeBefore(v_00_u03b1_3213_, v_m_3214_, v_inst_3215_, v_inst_3216_, v_00_u03b5_3217_, v_inst_3218_, v_inst_3219_, v_inst_3220_, v_always_3221_, v_inst_3222_, v_inst_3223_, v_cls_3224_, v_msg_3225_, v_k_3226_, v_collapsed_boxed_3229_, v_tag_3228_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0(lean_object* v_toApplicative_3231_, lean_object* v_____s_3232_){
_start:
{
lean_object* v_toPure_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_toPure_3233_ = lean_ctor_get(v_toApplicative_3231_, 1);
lean_inc(v_toPure_3233_);
lean_dec_ref(v_toApplicative_3231_);
v___x_3234_ = lean_box(0);
v___x_3235_ = lean_apply_2(v_toPure_3233_, lean_box(0), v___x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__1(lean_object* v_x_3236_, lean_object* v_x_3237_){
_start:
{
lean_object* v_fst_3238_; lean_object* v_fst_3239_; lean_object* v_fst_3240_; lean_object* v_fst_3241_; uint8_t v___x_3242_; 
v_fst_3238_ = lean_ctor_get(v_x_3236_, 0);
v_fst_3239_ = lean_ctor_get(v_x_3237_, 0);
v_fst_3240_ = lean_ctor_get(v_fst_3238_, 0);
v_fst_3241_ = lean_ctor_get(v_fst_3239_, 0);
v___x_3242_ = lean_nat_dec_lt(v_fst_3240_, v_fst_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1___boxed(lean_object* v_x_3243_, lean_object* v_x_3244_){
_start:
{
uint8_t v_res_3245_; lean_object* v_r_3246_; 
v_res_3245_ = l_Lean_addTraceAsMessages___redArg___lam__1(v_x_3243_, v_x_3244_);
lean_dec_ref(v_x_3244_);
lean_dec_ref(v_x_3243_);
v_r_3246_ = lean_box(v_res_3245_);
return v_r_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object* v_x1_3247_, lean_object* v_x2_3248_, lean_object* v_x3_3249_){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v_x2_3248_);
lean_ctor_set(v___x_3250_, 1, v_x3_3249_);
v___x_3251_ = lean_array_push(v_x1_3247_, v___x_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object* v_toApplicative_3252_, lean_object* v___x_3253_, lean_object* v_r_3254_){
_start:
{
lean_object* v_toPure_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v_toPure_3255_ = lean_ctor_get(v_toApplicative_3252_, 1);
lean_inc(v_toPure_3255_);
lean_dec_ref(v_toApplicative_3252_);
v___x_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3253_);
v___x_3257_ = lean_apply_2(v_toPure_3255_, lean_box(0), v___x_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object* v_____do__lift_3258_, lean_object* v___x_3259_, lean_object* v_fst_3260_, lean_object* v_snd_3261_, lean_object* v_logMessage_3262_, lean_object* v_toBind_3263_, lean_object* v___f_3264_, lean_object* v_____do__lift_3265_){
_start:
{
uint8_t v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3266_ = 0;
v___x_3267_ = l_Lean_Elab_mkMessageCore(v_____do__lift_3258_, v_____do__lift_3265_, v___x_3259_, v___x_3266_, v_fst_3260_, v_snd_3261_);
v___x_3268_ = lean_apply_1(v_logMessage_3262_, v___x_3267_);
v___x_3269_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v___x_3268_, v___f_3264_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object* v_____do__lift_3270_, lean_object* v___x_3271_, lean_object* v_fst_3272_, lean_object* v_snd_3273_, lean_object* v_logMessage_3274_, lean_object* v_toBind_3275_, lean_object* v___f_3276_, lean_object* v_____do__lift_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_addTraceAsMessages___redArg___lam__4(v_____do__lift_3270_, v___x_3271_, v_fst_3272_, v_snd_3273_, v_logMessage_3274_, v_toBind_3275_, v___f_3276_, v_____do__lift_3277_);
lean_dec(v_snd_3273_);
lean_dec(v_fst_3272_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object* v___x_3279_, lean_object* v_fst_3280_, lean_object* v_snd_3281_, lean_object* v_logMessage_3282_, lean_object* v_toBind_3283_, lean_object* v___f_3284_, lean_object* v_toMonadFileMap_3285_, lean_object* v_____do__lift_3286_){
_start:
{
lean_object* v___f_3287_; lean_object* v___x_3288_; 
lean_inc(v_toBind_3283_);
v___f_3287_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_3287_, 0, v_____do__lift_3286_);
lean_closure_set(v___f_3287_, 1, v___x_3279_);
lean_closure_set(v___f_3287_, 2, v_fst_3280_);
lean_closure_set(v___f_3287_, 3, v_snd_3281_);
lean_closure_set(v___f_3287_, 4, v_logMessage_3282_);
lean_closure_set(v___f_3287_, 5, v_toBind_3283_);
lean_closure_set(v___f_3287_, 6, v___f_3284_);
v___x_3288_ = lean_apply_4(v_toBind_3283_, lean_box(0), lean_box(0), v_toMonadFileMap_3285_, v___f_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object* v___x_3289_, uint8_t v___x_3290_, lean_object* v_inst_3291_, lean_object* v_toBind_3292_, lean_object* v___f_3293_, lean_object* v_a_3294_, lean_object* v_x_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_fst_3297_; lean_object* v_snd_3298_; lean_object* v_fst_3299_; lean_object* v_snd_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3320_; 
v_fst_3297_ = lean_ctor_get(v_a_3294_, 0);
lean_inc(v_fst_3297_);
v_snd_3298_ = lean_ctor_get(v_a_3294_, 1);
lean_inc(v_snd_3298_);
lean_dec_ref(v_a_3294_);
v_fst_3299_ = lean_ctor_get(v_fst_3297_, 0);
v_snd_3300_ = lean_ctor_get(v_fst_3297_, 1);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_fst_3297_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3302_ = v_fst_3297_;
v_isShared_3303_ = v_isSharedCheck_3320_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_snd_3300_);
lean_inc(v_fst_3299_);
lean_dec(v_fst_3297_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3320_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; double v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v_toMonadFileMap_3309_; lean_object* v_getFileName_3310_; lean_object* v_logMessage_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3316_; 
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_float_of_nat(v___x_3289_);
v___x_3307_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_3308_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3308_, 0, v___x_3304_);
lean_ctor_set(v___x_3308_, 1, v___x_3305_);
lean_ctor_set(v___x_3308_, 2, v___x_3307_);
lean_ctor_set_float(v___x_3308_, sizeof(void*)*3, v___x_3306_);
lean_ctor_set_float(v___x_3308_, sizeof(void*)*3 + 8, v___x_3306_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*3 + 16, v___x_3290_);
v_toMonadFileMap_3309_ = lean_ctor_get(v_inst_3291_, 0);
lean_inc(v_toMonadFileMap_3309_);
v_getFileName_3310_ = lean_ctor_get(v_inst_3291_, 2);
lean_inc(v_getFileName_3310_);
v_logMessage_3311_ = lean_ctor_get(v_inst_3291_, 4);
lean_inc(v_logMessage_3311_);
lean_dec_ref(v_inst_3291_);
v___x_3312_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_3313_ = l_Lean_MessageData_nil;
v___x_3314_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3308_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
lean_ctor_set(v___x_3314_, 2, v_snd_3298_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set_tag(v___x_3302_, 8);
lean_ctor_set(v___x_3302_, 1, v___x_3314_);
lean_ctor_set(v___x_3302_, 0, v___x_3312_);
v___x_3316_ = v___x_3302_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3312_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___f_3317_; lean_object* v___x_3318_; 
lean_inc(v_toBind_3292_);
v___f_3317_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__5), 8, 7);
lean_closure_set(v___f_3317_, 0, v___x_3316_);
lean_closure_set(v___f_3317_, 1, v_fst_3299_);
lean_closure_set(v___f_3317_, 2, v_snd_3300_);
lean_closure_set(v___f_3317_, 3, v_logMessage_3311_);
lean_closure_set(v___f_3317_, 4, v_toBind_3292_);
lean_closure_set(v___f_3317_, 5, v___f_3293_);
lean_closure_set(v___f_3317_, 6, v_toMonadFileMap_3309_);
v___x_3318_ = lean_apply_4(v_toBind_3292_, lean_box(0), lean_box(0), v_getFileName_3310_, v___f_3317_);
return v___x_3318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object* v___x_3321_, lean_object* v___x_3322_, lean_object* v_inst_3323_, lean_object* v_toBind_3324_, lean_object* v___f_3325_, lean_object* v_a_3326_, lean_object* v_x_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v___x_1915__boxed_3329_; lean_object* v_res_3330_; 
v___x_1915__boxed_3329_ = lean_unbox(v___x_3322_);
v_res_3330_ = l_Lean_addTraceAsMessages___redArg___lam__6(v___x_3321_, v___x_1915__boxed_3329_, v_inst_3323_, v_toBind_3324_, v___f_3325_, v_a_3326_, v_x_3327_, v___y_3328_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object* v___x_3331_, lean_object* v___f_3332_, lean_object* v_acc_3333_, lean_object* v_l_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_3331_, v___f_3332_, v_acc_3333_, v_l_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object* v_toApplicative_3336_, uint8_t v___x_3337_, lean_object* v_inst_3338_, lean_object* v_toBind_3339_, lean_object* v_inst_3340_, lean_object* v___f_3341_, lean_object* v___f_3342_, lean_object* v___f_3343_, lean_object* v_____s_3344_){
_start:
{
lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3371_; lean_object* v_size_3378_; lean_object* v_buckets_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; 
v_size_3378_ = lean_ctor_get(v_____s_3344_, 0);
lean_inc(v_size_3378_);
v_buckets_3379_ = lean_ctor_get(v_____s_3344_, 1);
lean_inc_ref(v_buckets_3379_);
lean_dec_ref(v_____s_3344_);
v___x_3380_ = lean_mk_empty_array_with_capacity(v_size_3378_);
lean_dec(v_size_3378_);
v___x_3381_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v___x_3382_ = lean_unsigned_to_nat(0u);
v___x_3383_ = lean_array_get_size(v_buckets_3379_);
v___x_3384_ = lean_nat_dec_lt(v___x_3382_, v___x_3383_);
if (v___x_3384_ == 0)
{
lean_dec_ref(v_buckets_3379_);
lean_dec_ref(v___f_3343_);
v___y_3371_ = v___x_3380_;
goto v___jp_3370_;
}
else
{
lean_object* v___f_3385_; uint8_t v___x_3386_; 
v___f_3385_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__7), 4, 2);
lean_closure_set(v___f_3385_, 0, v___x_3381_);
lean_closure_set(v___f_3385_, 1, v___f_3343_);
v___x_3386_ = lean_nat_dec_le(v___x_3383_, v___x_3383_);
if (v___x_3386_ == 0)
{
if (v___x_3384_ == 0)
{
lean_dec_ref(v___f_3385_);
lean_dec_ref(v_buckets_3379_);
v___y_3371_ = v___x_3380_;
goto v___jp_3370_;
}
else
{
size_t v___x_3387_; size_t v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = ((size_t)0ULL);
v___x_3388_ = lean_usize_of_nat(v___x_3383_);
v___x_3389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3381_, v___f_3385_, v_buckets_3379_, v___x_3387_, v___x_3388_, v___x_3380_);
v___y_3371_ = v___x_3389_;
goto v___jp_3370_;
}
}
else
{
size_t v___x_3390_; size_t v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = ((size_t)0ULL);
v___x_3391_ = lean_usize_of_nat(v___x_3383_);
v___x_3392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3381_, v___f_3385_, v_buckets_3379_, v___x_3390_, v___x_3391_, v___x_3380_);
v___y_3371_ = v___x_3392_;
goto v___jp_3370_;
}
}
v___jp_3345_:
{
lean_object* v___x_3348_; lean_object* v___f_3349_; lean_object* v___x_3350_; lean_object* v___f_3351_; size_t v_sz_3352_; size_t v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3348_ = lean_box(0);
v___f_3349_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3349_, 0, v_toApplicative_3336_);
lean_closure_set(v___f_3349_, 1, v___x_3348_);
v___x_3350_ = lean_box(v___x_3337_);
lean_inc(v_toBind_3339_);
v___f_3351_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__6___boxed), 8, 5);
lean_closure_set(v___f_3351_, 0, v___y_3346_);
lean_closure_set(v___f_3351_, 1, v___x_3350_);
lean_closure_set(v___f_3351_, 2, v_inst_3338_);
lean_closure_set(v___f_3351_, 3, v_toBind_3339_);
lean_closure_set(v___f_3351_, 4, v___f_3349_);
v_sz_3352_ = lean_array_size(v___y_3347_);
v___x_3353_ = ((size_t)0ULL);
v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3340_, v___y_3347_, v___f_3351_, v_sz_3352_, v___x_3353_, v___x_3348_);
v___x_3355_ = lean_apply_4(v_toBind_3339_, lean_box(0), lean_box(0), v___x_3354_, v___f_3341_);
return v___x_3355_;
}
v___jp_3356_:
{
lean_object* v___x_3362_; 
v___x_3362_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_3342_, v___y_3359_, v___y_3360_, v___y_3358_, v___y_3361_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_3361_);
lean_dec(v___y_3359_);
v___y_3346_ = v___y_3357_;
v___y_3347_ = v___x_3362_;
goto v___jp_3345_;
}
v___jp_3363_:
{
uint8_t v___x_3369_; 
v___x_3369_ = lean_nat_dec_le(v___y_3368_, v___y_3365_);
if (v___x_3369_ == 0)
{
lean_dec(v___y_3365_);
lean_inc(v___y_3368_);
v___y_3357_ = v___y_3364_;
v___y_3358_ = v___y_3368_;
v___y_3359_ = v___y_3366_;
v___y_3360_ = v___y_3367_;
v___y_3361_ = v___y_3368_;
goto v___jp_3356_;
}
else
{
v___y_3357_ = v___y_3364_;
v___y_3358_ = v___y_3368_;
v___y_3359_ = v___y_3366_;
v___y_3360_ = v___y_3367_;
v___y_3361_ = v___y_3365_;
goto v___jp_3356_;
}
}
v___jp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v___x_3372_ = lean_unsigned_to_nat(0u);
v___x_3373_ = lean_array_get_size(v___y_3371_);
v___x_3374_ = lean_nat_dec_eq(v___x_3373_, v___x_3372_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; 
v___x_3375_ = lean_unsigned_to_nat(1u);
v___x_3376_ = lean_nat_sub(v___x_3373_, v___x_3375_);
v___x_3377_ = lean_nat_dec_le(v___x_3372_, v___x_3376_);
if (v___x_3377_ == 0)
{
lean_inc(v___x_3376_);
v___y_3364_ = v___x_3372_;
v___y_3365_ = v___x_3376_;
v___y_3366_ = v___x_3373_;
v___y_3367_ = v___y_3371_;
v___y_3368_ = v___x_3376_;
goto v___jp_3363_;
}
else
{
v___y_3364_ = v___x_3372_;
v___y_3365_ = v___x_3376_;
v___y_3366_ = v___x_3373_;
v___y_3367_ = v___y_3371_;
v___y_3368_ = v___x_3372_;
goto v___jp_3363_;
}
}
else
{
lean_dec_ref(v___f_3342_);
v___y_3346_ = v___x_3372_;
v___y_3347_ = v___y_3371_;
goto v___jp_3345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object* v_toApplicative_3393_, lean_object* v___x_3394_, lean_object* v_inst_3395_, lean_object* v_toBind_3396_, lean_object* v_inst_3397_, lean_object* v___f_3398_, lean_object* v___f_3399_, lean_object* v___f_3400_, lean_object* v_____s_3401_){
_start:
{
uint8_t v___x_2003__boxed_3402_; lean_object* v_res_3403_; 
v___x_2003__boxed_3402_ = lean_unbox(v___x_3394_);
v_res_3403_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_toApplicative_3393_, v___x_2003__boxed_3402_, v_inst_3395_, v_toBind_3396_, v_inst_3397_, v___f_3398_, v___f_3399_, v___f_3400_, v_____s_3401_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object* v_traceElem_3404_, lean_object* v_toApplicative_3405_, lean_object* v___f_3406_, lean_object* v___f_3407_, lean_object* v_____s_3408_, uint8_t v___x_3409_, lean_object* v_____do__lift_3410_){
_start:
{
lean_object* v_ref_3411_; lean_object* v_msg_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3437_; 
v_ref_3411_ = lean_ctor_get(v_traceElem_3404_, 0);
v_msg_3412_ = lean_ctor_get(v_traceElem_3404_, 1);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_traceElem_3404_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3414_ = v_traceElem_3404_;
v_isShared_3415_ = v_isSharedCheck_3437_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_msg_3412_);
lean_inc(v_ref_3411_);
lean_dec(v_traceElem_3404_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3437_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v_ref_3429_; lean_object* v___y_3431_; lean_object* v___x_3434_; 
v_ref_3429_ = l_Lean_replaceRef(v_ref_3411_, v_____do__lift_3410_);
lean_dec(v_ref_3411_);
v___x_3434_ = l_Lean_Syntax_getPos_x3f(v_ref_3429_, v___x_3409_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_unsigned_to_nat(0u);
v___y_3431_ = v___x_3435_;
goto v___jp_3430_;
}
else
{
lean_object* v_val_3436_; 
v_val_3436_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_val_3436_);
lean_dec_ref(v___x_3434_);
v___y_3431_ = v_val_3436_;
goto v___jp_3430_;
}
v___jp_3416_:
{
lean_object* v_toPure_3419_; lean_object* v___x_3421_; 
v_toPure_3419_ = lean_ctor_get(v_toApplicative_3405_, 1);
lean_inc(v_toPure_3419_);
lean_dec_ref(v_toApplicative_3405_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 1, v___y_3418_);
lean_ctor_set(v___x_3414_, 0, v___y_3417_);
v___x_3421_ = v___x_3414_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___y_3417_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v___y_3418_);
v___x_3421_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v_pos2traces_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3422_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
lean_inc_ref(v___x_3421_);
lean_inc_ref(v___f_3407_);
lean_inc_ref(v___f_3406_);
v___x_3423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_3406_, v___f_3407_, v_____s_3408_, v___x_3421_, v___x_3422_);
v___x_3424_ = lean_array_push(v___x_3423_, v_msg_3412_);
v_pos2traces_3425_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3406_, v___f_3407_, v_____s_3408_, v___x_3421_, v___x_3424_);
v___x_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3426_, 0, v_pos2traces_3425_);
v___x_3427_ = lean_apply_2(v_toPure_3419_, lean_box(0), v___x_3426_);
return v___x_3427_;
}
}
v___jp_3430_:
{
lean_object* v___x_3432_; 
v___x_3432_ = l_Lean_Syntax_getTailPos_x3f(v_ref_3429_, v___x_3409_);
lean_dec(v_ref_3429_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_inc(v___y_3431_);
v___y_3417_ = v___y_3431_;
v___y_3418_ = v___y_3431_;
goto v___jp_3416_;
}
else
{
lean_object* v_val_3433_; 
v_val_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_val_3433_);
lean_dec_ref(v___x_3432_);
v___y_3417_ = v___y_3431_;
v___y_3418_ = v_val_3433_;
goto v___jp_3416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object* v_traceElem_3438_, lean_object* v_toApplicative_3439_, lean_object* v___f_3440_, lean_object* v___f_3441_, lean_object* v_____s_3442_, lean_object* v___x_3443_, lean_object* v_____do__lift_3444_){
_start:
{
uint8_t v___x_2128__boxed_3445_; lean_object* v_res_3446_; 
v___x_2128__boxed_3445_ = lean_unbox(v___x_3443_);
v_res_3446_ = l_Lean_addTraceAsMessages___redArg___lam__9(v_traceElem_3438_, v_toApplicative_3439_, v___f_3440_, v___f_3441_, v_____s_3442_, v___x_2128__boxed_3445_, v_____do__lift_3444_);
lean_dec(v_____do__lift_3444_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object* v_inst_3447_, lean_object* v_toApplicative_3448_, lean_object* v___f_3449_, lean_object* v___f_3450_, uint8_t v___x_3451_, lean_object* v_toBind_3452_, lean_object* v_traceElem_3453_, lean_object* v_____s_3454_){
_start:
{
lean_object* v_getRef_3455_; lean_object* v___x_3456_; lean_object* v___f_3457_; lean_object* v___x_3458_; 
v_getRef_3455_ = lean_ctor_get(v_inst_3447_, 0);
lean_inc(v_getRef_3455_);
lean_dec_ref(v_inst_3447_);
v___x_3456_ = lean_box(v___x_3451_);
v___f_3457_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_3457_, 0, v_traceElem_3453_);
lean_closure_set(v___f_3457_, 1, v_toApplicative_3448_);
lean_closure_set(v___f_3457_, 2, v___f_3449_);
lean_closure_set(v___f_3457_, 3, v___f_3450_);
lean_closure_set(v___f_3457_, 4, v_____s_3454_);
lean_closure_set(v___f_3457_, 5, v___x_3456_);
v___x_3458_ = lean_apply_4(v_toBind_3452_, lean_box(0), lean_box(0), v_getRef_3455_, v___f_3457_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object* v_inst_3459_, lean_object* v_toApplicative_3460_, lean_object* v___f_3461_, lean_object* v___f_3462_, lean_object* v___x_3463_, lean_object* v_toBind_3464_, lean_object* v_traceElem_3465_, lean_object* v_____s_3466_){
_start:
{
uint8_t v___x_2188__boxed_3467_; lean_object* v_res_3468_; 
v___x_2188__boxed_3467_ = lean_unbox(v___x_3463_);
v_res_3468_ = l_Lean_addTraceAsMessages___redArg___lam__10(v_inst_3459_, v_toApplicative_3460_, v___f_3461_, v___f_3462_, v___x_2188__boxed_3467_, v_toBind_3464_, v_traceElem_3465_, v_____s_3466_);
return v_res_3468_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___f_3470_; 
v___x_3469_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_3470_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3470_, 0, v___x_3469_);
return v___f_3470_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___f_3471_; lean_object* v___f_3472_; 
v___f_3471_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__0, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0);
v___f_3472_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3472_, 0, v___f_3471_);
lean_closure_set(v___f_3472_, 1, v___f_3471_);
return v___f_3472_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__3(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___f_3475_; 
v___x_3474_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___lam__11___closed__2));
v___f_3475_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3475_, 0, v___x_3474_);
lean_closure_set(v___f_3475_, 1, v___x_3474_);
return v___f_3475_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4(void){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3476_ = lean_box(0);
v___x_3477_ = lean_unsigned_to_nat(16u);
v___x_3478_ = lean_mk_array(v___x_3477_, v___x_3476_);
return v___x_3478_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5(void){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v_pos2traces_3481_; 
v___x_3479_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__4, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4);
v___x_3480_ = lean_unsigned_to_nat(0u);
v_pos2traces_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_3481_, 0, v___x_3480_);
lean_ctor_set(v_pos2traces_3481_, 1, v___x_3479_);
return v_pos2traces_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11(lean_object* v_inst_3482_, lean_object* v_toApplicative_3483_, lean_object* v_toBind_3484_, lean_object* v_inst_3485_, lean_object* v___f_3486_, lean_object* v_traces_3487_){
_start:
{
uint8_t v___x_3488_; 
v___x_3488_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_3487_);
if (v___x_3488_ == 0)
{
lean_object* v___f_3489_; lean_object* v___f_3490_; lean_object* v___x_3491_; lean_object* v___f_3492_; lean_object* v_pos2traces_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___f_3489_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__1, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1);
v___f_3490_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__3, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__3_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__3);
v___x_3491_ = lean_box(v___x_3488_);
lean_inc(v_toBind_3484_);
v___f_3492_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3492_, 0, v_inst_3482_);
lean_closure_set(v___f_3492_, 1, v_toApplicative_3483_);
lean_closure_set(v___f_3492_, 2, v___f_3489_);
lean_closure_set(v___f_3492_, 3, v___f_3490_);
lean_closure_set(v___f_3492_, 4, v___x_3491_);
lean_closure_set(v___f_3492_, 5, v_toBind_3484_);
v_pos2traces_3493_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__5, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5);
v___x_3494_ = l_Lean_PersistentArray_forIn___redArg(v_inst_3485_, v_traces_3487_, v_pos2traces_3493_, v___f_3492_);
v___x_3495_ = lean_apply_4(v_toBind_3484_, lean_box(0), lean_box(0), v___x_3494_, v___f_3486_);
return v___x_3495_;
}
else
{
lean_object* v_toPure_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
lean_dec_ref(v_traces_3487_);
lean_dec(v___f_3486_);
lean_dec_ref(v_inst_3485_);
lean_dec(v_toBind_3484_);
lean_dec_ref(v_inst_3482_);
v_toPure_3496_ = lean_ctor_get(v_toApplicative_3483_, 1);
lean_inc(v_toPure_3496_);
lean_dec_ref(v_toApplicative_3483_);
v___x_3497_ = lean_box(0);
v___x_3498_ = lean_apply_2(v_toPure_3496_, lean_box(0), v___x_3497_);
return v___x_3498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12(lean_object* v___x_3499_, lean_object* v_toApplicative_3500_, lean_object* v_inst_3501_, lean_object* v_toBind_3502_, lean_object* v_inst_3503_, lean_object* v___f_3504_, lean_object* v___f_3505_, lean_object* v___f_3506_, lean_object* v_inst_3507_, lean_object* v_inst_3508_, lean_object* v_____do__lift_3509_){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = l_Lean_trace_profiler_output;
v___x_3511_ = l_Lean_Option_get_x3f___redArg(v___x_3499_, v_____do__lift_3509_, v___x_3510_);
if (lean_obj_tag(v___x_3511_) == 0)
{
uint8_t v___x_3512_; lean_object* v___x_3513_; lean_object* v___f_3514_; lean_object* v___f_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3512_ = 1;
v___x_3513_ = lean_box(v___x_3512_);
lean_inc_ref(v_inst_3503_);
lean_inc(v_toBind_3502_);
lean_inc_ref(v_toApplicative_3500_);
v___f_3514_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__8___boxed), 9, 8);
lean_closure_set(v___f_3514_, 0, v_toApplicative_3500_);
lean_closure_set(v___f_3514_, 1, v___x_3513_);
lean_closure_set(v___f_3514_, 2, v_inst_3501_);
lean_closure_set(v___f_3514_, 3, v_toBind_3502_);
lean_closure_set(v___f_3514_, 4, v_inst_3503_);
lean_closure_set(v___f_3514_, 5, v___f_3504_);
lean_closure_set(v___f_3514_, 6, v___f_3505_);
lean_closure_set(v___f_3514_, 7, v___f_3506_);
lean_inc_ref(v_inst_3503_);
lean_inc(v_toBind_3502_);
v___f_3515_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__11), 6, 5);
lean_closure_set(v___f_3515_, 0, v_inst_3507_);
lean_closure_set(v___f_3515_, 1, v_toApplicative_3500_);
lean_closure_set(v___f_3515_, 2, v_toBind_3502_);
lean_closure_set(v___f_3515_, 3, v_inst_3503_);
lean_closure_set(v___f_3515_, 4, v___f_3514_);
v___x_3516_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3503_, v_inst_3508_);
v___x_3517_ = lean_apply_4(v_toBind_3502_, lean_box(0), lean_box(0), v___x_3516_, v___f_3515_);
return v___x_3517_;
}
else
{
lean_object* v_toPure_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
lean_dec_ref(v___x_3511_);
lean_dec_ref(v_inst_3508_);
lean_dec_ref(v_inst_3507_);
lean_dec_ref(v___f_3506_);
lean_dec_ref(v___f_3505_);
lean_dec(v___f_3504_);
lean_dec_ref(v_inst_3503_);
lean_dec(v_toBind_3502_);
lean_dec_ref(v_inst_3501_);
v_toPure_3518_ = lean_ctor_get(v_toApplicative_3500_, 1);
lean_inc(v_toPure_3518_);
lean_dec_ref(v_toApplicative_3500_);
v___x_3519_ = lean_box(0);
v___x_3520_ = lean_apply_2(v_toPure_3518_, lean_box(0), v___x_3519_);
return v___x_3520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12___boxed(lean_object* v___x_3521_, lean_object* v_toApplicative_3522_, lean_object* v_inst_3523_, lean_object* v_toBind_3524_, lean_object* v_inst_3525_, lean_object* v___f_3526_, lean_object* v___f_3527_, lean_object* v___f_3528_, lean_object* v_inst_3529_, lean_object* v_inst_3530_, lean_object* v_____do__lift_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_addTraceAsMessages___redArg___lam__12(v___x_3521_, v_toApplicative_3522_, v_inst_3523_, v_toBind_3524_, v_inst_3525_, v___f_3526_, v___f_3527_, v___f_3528_, v_inst_3529_, v_inst_3530_, v_____do__lift_3531_);
lean_dec_ref(v_____do__lift_3531_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object* v_inst_3535_, lean_object* v_inst_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_inst_3539_){
_start:
{
lean_object* v___x_3540_; lean_object* v_toApplicative_3541_; lean_object* v_toBind_3542_; lean_object* v___f_3543_; lean_object* v___f_3544_; lean_object* v___f_3545_; lean_object* v___f_3546_; lean_object* v___x_3547_; 
v___x_3540_ = l_Lean_KVMap_instValueString;
v_toApplicative_3541_ = lean_ctor_get(v_inst_3536_, 0);
lean_inc_ref(v_toApplicative_3541_);
v_toBind_3542_ = lean_ctor_get(v_inst_3536_, 1);
lean_inc(v_toBind_3542_);
lean_inc_ref(v_toApplicative_3541_);
v___f_3543_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3543_, 0, v_toApplicative_3541_);
v___f_3544_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__0));
v___f_3545_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__1));
lean_inc(v_toBind_3542_);
v___f_3546_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3546_, 0, v___x_3540_);
lean_closure_set(v___f_3546_, 1, v_toApplicative_3541_);
lean_closure_set(v___f_3546_, 2, v_inst_3538_);
lean_closure_set(v___f_3546_, 3, v_toBind_3542_);
lean_closure_set(v___f_3546_, 4, v_inst_3536_);
lean_closure_set(v___f_3546_, 5, v___f_3543_);
lean_closure_set(v___f_3546_, 6, v___f_3544_);
lean_closure_set(v___f_3546_, 7, v___f_3545_);
lean_closure_set(v___f_3546_, 8, v_inst_3537_);
lean_closure_set(v___f_3546_, 9, v_inst_3539_);
v___x_3547_ = lean_apply_4(v_toBind_3542_, lean_box(0), lean_box(0), v_inst_3535_, v___f_3546_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object* v_m_3548_, lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_inst_3551_, lean_object* v_inst_3552_, lean_object* v_inst_3553_){
_start:
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_addTraceAsMessages___redArg(v_inst_3549_, v_inst_3550_, v_inst_3551_, v_inst_3552_, v_inst_3553_);
return v___x_3554_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3596_ = lean_unsigned_to_nat(2826257906u);
v___x_3597_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3598_ = l_Lean_Name_num___override(v___x_3597_, v___x_3596_);
return v___x_3598_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3601_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3602_ = l_Lean_Name_str___override(v___x_3601_, v___x_3600_);
return v___x_3602_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3604_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3605_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3606_ = l_Lean_Name_str___override(v___x_3605_, v___x_3604_);
return v___x_3606_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3607_ = lean_unsigned_to_nat(2u);
v___x_3608_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3609_ = l_Lean_Name_num___override(v___x_3608_, v___x_3607_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3611_; uint8_t v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3611_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3612_ = 0;
v___x_3613_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3614_ = l_Lean_registerTraceClass(v___x_3611_, v___x_3612_, v___x_3613_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object* v_a_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
return v_res_3616_;
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
