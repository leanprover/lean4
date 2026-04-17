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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_instHashableRaw_hash___boxed(lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueString;
lean_object* l_Lean_Option_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_StateT_instMonadExceptOf___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonadExceptOf___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedTraceElem_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTraceElem_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceElem_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceElem;
static lean_once_cell_t l_Lean_instInhabitedTraceState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTraceState_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedTraceState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTraceState_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedTraceState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTraceState_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceState_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTraceState;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_printTraces___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringFormat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_printTraces___redArg___closed__0 = (const lean_object*)&l_Lean_printTraces___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_printTraces(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "profiler"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "activate nested traces with execution time above `trace.profiler.threshold` and annotate with time"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "threshold"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(184, 9, 42, 114, 12, 38, 11, 42)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 130, .m_capacity = 130, .m_length = 129, .m_data = "threshold in milliseconds (or heartbeats if `trace.profiler.useHeartbeats` is true), traces below threshold will not be activated"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 45, 177, 27, 189, 220, 1, 137)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "useHeartbeats"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 182, 122, 179, 202, 46, 182, 49)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "if true, measure and report heartbeats instead of seconds"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(89, 248, 181, 172, 128, 194, 123, 56)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_useHeartbeats;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "output"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(19, 45, 221, 139, 23, 193, 130, 68)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "output `trace.profiler` data in Firefox Profiler-compatible format to given file path"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addTrace___redArg___lam__0___closed__1_value),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(58, 195, 204, 148, 25, 40, 60, 227)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_output;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(19, 45, 221, 139, 23, 193, 130, 68)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(193, 225, 100, 102, 84, 233, 134, 170)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 232, .m_capacity = 232, .m_length = 231, .m_data = "if false, limit text in exported trace nodes to trace class name and `TraceData.tag`, if any\n\nThis is useful when we are interested in the time taken by specific subsystems instead of specific invocations, which is the common case."};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(58, 195, 204, 148, 25, 40, 60, 227)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(228, 86, 200, 244, 100, 192, 149, 216)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_instInhabitedTraceState_default___closed__0(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_unsigned_to_nat(32u);
v___x_7_ = lean_mk_empty_array_with_capacity(v___x_6_);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState_default___closed__1(void){
_start:
{
size_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_9_ = ((size_t)5ULL);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_unsigned_to_nat(32u);
v___x_12_ = lean_mk_empty_array_with_capacity(v___x_11_);
v___x_13_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__0, &l_Lean_instInhabitedTraceState_default___closed__0_once, _init_l_Lean_instInhabitedTraceState_default___closed__0);
v___x_14_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
lean_ctor_set(v___x_14_, 2, v___x_10_);
lean_ctor_set(v___x_14_, 3, v___x_10_);
lean_ctor_set_usize(v___x_14_, 4, v___x_9_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState_default___closed__2(void){
_start:
{
lean_object* v___x_15_; uint64_t v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__1, &l_Lean_instInhabitedTraceState_default___closed__1_once, _init_l_Lean_instInhabitedTraceState_default___closed__1);
v___x_16_ = 0ULL;
v___x_17_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_17_, 0, v___x_15_);
lean_ctor_set_uint64(v___x_17_, sizeof(void*)*1, v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState_default(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__2, &l_Lean_instInhabitedTraceState_default___closed__2_once, _init_l_Lean_instInhabitedTraceState_default___closed__2);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_instInhabitedTraceState(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_instInhabitedTraceState_default;
return v___x_19_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_20_ = lean_box(0);
v___x_21_ = lean_unsigned_to_nat(16u);
v___x_22_ = lean_mk_array(v___x_21_, v___x_20_);
return v___x_22_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
v___x_24_ = lean_unsigned_to_nat(0u);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v___x_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
v___x_28_ = lean_st_mk_ref(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2____boxed(lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
return v_res_31_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10));
v___x_59_ = l_Lean_mkAtom(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12);
v___x_61_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14));
v___x_65_ = lean_string_utf8_byte_size(v___x_64_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14));
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_75_ = lean_box(0);
v___x_76_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19));
v___x_77_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16);
v___x_78_ = lean_box(2);
v___x_79_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_76_);
lean_ctor_set(v___x_79_, 3, v___x_75_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20);
v___x_81_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_82_ = lean_array_push(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21);
v___x_84_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_85_ = lean_box(2);
v___x_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22);
v___x_88_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_89_ = lean_array_push(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23);
v___x_91_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_92_ = lean_box(2);
v___x_93_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
lean_ctor_set(v___x_93_, 2, v___x_90_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24);
v___x_95_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_96_ = lean_array_push(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25);
v___x_98_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_99_ = lean_box(2);
v___x_100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_97_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26);
v___x_102_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_103_ = lean_array_push(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27);
v___x_105_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_106_ = lean_box(2);
v___x_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_104_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg___lam__0(lean_object* v_modifyTraceState_109_, lean_object* v_inst_110_, lean_object* v_f_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_apply_1(v_modifyTraceState_109_, v_f_111_);
v___x_113_ = lean_apply_2(v_inst_110_, lean_box(0), v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object* v_inst_114_, lean_object* v_inst_115_){
_start:
{
lean_object* v_modifyTraceState_116_; lean_object* v_getTraceState_117_; lean_object* v_getInheritedTraceOptions_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_128_; 
v_modifyTraceState_116_ = lean_ctor_get(v_inst_115_, 0);
v_getTraceState_117_ = lean_ctor_get(v_inst_115_, 1);
v_getInheritedTraceOptions_118_ = lean_ctor_get(v_inst_115_, 2);
v_isSharedCheck_128_ = !lean_is_exclusive(v_inst_115_);
if (v_isSharedCheck_128_ == 0)
{
v___x_120_ = v_inst_115_;
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_getInheritedTraceOptions_118_);
lean_inc(v_getTraceState_117_);
lean_inc(v_modifyTraceState_116_);
lean_dec(v_inst_115_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___f_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
lean_inc_n(v_inst_114_, 2);
v___f_122_ = lean_alloc_closure((void*)(l_Lean_instMonadTraceOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_122_, 0, v_modifyTraceState_116_);
lean_closure_set(v___f_122_, 1, v_inst_114_);
v___x_123_ = lean_apply_2(v_inst_114_, lean_box(0), v_getTraceState_117_);
v___x_124_ = lean_apply_2(v_inst_114_, lean_box(0), v_getInheritedTraceOptions_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 2, v___x_124_);
lean_ctor_set(v___x_120_, 1, v___x_123_);
lean_ctor_set(v___x_120_, 0, v___f_122_);
v___x_126_ = v___x_120_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___f_122_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift(lean_object* v_m_129_, lean_object* v_n_130_, lean_object* v_inst_131_, lean_object* v_inst_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_instMonadTraceOfMonadLift___redArg(v_inst_131_, v_inst_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__0(lean_object* v_toPure_134_, lean_object* v_____s_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_box(0);
v___x_137_ = lean_apply_2(v_toPure_134_, lean_box(0), v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__1(lean_object* v___x_138_, lean_object* v_toPure_139_, lean_object* v_r_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_138_);
v___x_142_ = lean_apply_2(v_toPure_139_, lean_box(0), v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__2(lean_object* v___f_143_, lean_object* v_inst_144_, lean_object* v_toBind_145_, lean_object* v___f_146_, lean_object* v_____do__lift_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_alloc_closure((void*)(l_IO_println___boxed), 4, 3);
lean_closure_set(v___x_148_, 0, lean_box(0));
lean_closure_set(v___x_148_, 1, v___f_143_);
lean_closure_set(v___x_148_, 2, v_____do__lift_147_);
v___x_149_ = lean_apply_2(v_inst_144_, lean_box(0), v___x_148_);
v___x_150_ = lean_apply_4(v_toBind_145_, lean_box(0), lean_box(0), v___x_149_, v___f_146_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__3(lean_object* v_inst_151_, lean_object* v_toBind_152_, lean_object* v___f_153_, lean_object* v_x_154_, lean_object* v_____s_155_){
_start:
{
lean_object* v_msg_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_msg_156_ = lean_ctor_get(v_x_154_, 1);
lean_inc_ref(v_msg_156_);
lean_dec_ref(v_x_154_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_alloc_closure((void*)(l_Lean_MessageData_format___boxed), 3, 2);
lean_closure_set(v___x_158_, 0, v_msg_156_);
lean_closure_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_alloc_closure((void*)(l_BaseIO_toIO___boxed), 3, 2);
lean_closure_set(v___x_159_, 0, lean_box(0));
lean_closure_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_apply_2(v_inst_151_, lean_box(0), v___x_159_);
v___x_161_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v___x_160_, v___f_153_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4(lean_object* v_toPure_162_, lean_object* v___f_163_, lean_object* v_inst_164_, lean_object* v_toBind_165_, lean_object* v_inst_166_, lean_object* v___f_167_, lean_object* v_____do__lift_168_){
_start:
{
lean_object* v_traces_169_; lean_object* v___x_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_traces_169_ = lean_ctor_get(v_____do__lift_168_, 0);
v___x_170_ = lean_box(0);
v___f_171_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_171_, 0, v___x_170_);
lean_closure_set(v___f_171_, 1, v_toPure_162_);
lean_inc_n(v_toBind_165_, 2);
lean_inc(v_inst_164_);
v___f_172_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_172_, 0, v___f_163_);
lean_closure_set(v___f_172_, 1, v_inst_164_);
lean_closure_set(v___f_172_, 2, v_toBind_165_);
lean_closure_set(v___f_172_, 3, v___f_171_);
v___f_173_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__3), 5, 3);
lean_closure_set(v___f_173_, 0, v_inst_164_);
lean_closure_set(v___f_173_, 1, v_toBind_165_);
lean_closure_set(v___f_173_, 2, v___f_172_);
v___x_174_ = l_Lean_PersistentArray_forIn___redArg(v_inst_166_, v_traces_169_, v___x_170_, v___f_173_);
v___x_175_ = lean_apply_4(v_toBind_165_, lean_box(0), lean_box(0), v___x_174_, v___f_167_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4___boxed(lean_object* v_toPure_176_, lean_object* v___f_177_, lean_object* v_inst_178_, lean_object* v_toBind_179_, lean_object* v_inst_180_, lean_object* v___f_181_, lean_object* v_____do__lift_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_printTraces___redArg___lam__4(v_toPure_176_, v___f_177_, v_inst_178_, v_toBind_179_, v_inst_180_, v___f_181_, v_____do__lift_182_);
lean_dec_ref(v_____do__lift_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg(lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_){
_start:
{
lean_object* v_toApplicative_188_; lean_object* v_toBind_189_; lean_object* v_getTraceState_190_; lean_object* v_toPure_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___x_195_; 
v_toApplicative_188_ = lean_ctor_get(v_inst_185_, 0);
v_toBind_189_ = lean_ctor_get(v_inst_185_, 1);
lean_inc_n(v_toBind_189_, 2);
v_getTraceState_190_ = lean_ctor_get(v_inst_186_, 1);
lean_inc(v_getTraceState_190_);
lean_dec_ref(v_inst_186_);
v_toPure_191_ = lean_ctor_get(v_toApplicative_188_, 1);
lean_inc_n(v_toPure_191_, 2);
v___f_192_ = ((lean_object*)(l_Lean_printTraces___redArg___closed__0));
v___f_193_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_193_, 0, v_toPure_191_);
v___f_194_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_194_, 0, v_toPure_191_);
lean_closure_set(v___f_194_, 1, v___f_192_);
lean_closure_set(v___f_194_, 2, v_inst_187_);
lean_closure_set(v___f_194_, 3, v_toBind_189_);
lean_closure_set(v___f_194_, 4, v_inst_185_);
lean_closure_set(v___f_194_, 5, v___f_193_);
v___x_195_ = lean_apply_4(v_toBind_189_, lean_box(0), lean_box(0), v_getTraceState_190_, v___f_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces(lean_object* v_m_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_printTraces___redArg(v_inst_197_, v_inst_198_, v_inst_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0(lean_object* v_x_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_unsigned_to_nat(32u);
v___x_203_ = lean_mk_empty_array_with_capacity(v___x_202_);
lean_dec_ref(v___x_203_);
v___x_204_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__2, &l_Lean_instInhabitedTraceState_default___closed__2_once, _init_l_Lean_instInhabitedTraceState_default___closed__2);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0___boxed(lean_object* v_x_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_resetTraceState___redArg___lam__0(v_x_205_);
lean_dec_ref(v_x_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg(lean_object* v_inst_208_){
_start:
{
lean_object* v_modifyTraceState_209_; lean_object* v___f_210_; lean_object* v___x_211_; 
v_modifyTraceState_209_ = lean_ctor_get(v_inst_208_, 0);
lean_inc(v_modifyTraceState_209_);
lean_dec_ref(v_inst_208_);
v___f_210_ = ((lean_object*)(l_Lean_resetTraceState___redArg___closed__0));
v___x_211_ = lean_apply_1(v_modifyTraceState_209_, v___f_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState(lean_object* v_m_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_resetTraceState___redArg(v_inst_213_);
return v___x_214_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(lean_object* v_a_215_, lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
uint8_t v___x_217_; 
v___x_217_ = 0;
return v___x_217_;
}
else
{
lean_object* v_key_218_; lean_object* v_tail_219_; uint8_t v___x_220_; 
v_key_218_ = lean_ctor_get(v_x_216_, 0);
v_tail_219_ = lean_ctor_get(v_x_216_, 2);
v___x_220_ = lean_name_eq(v_key_218_, v_a_215_);
if (v___x_220_ == 0)
{
v_x_216_ = v_tail_219_;
goto _start;
}
else
{
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_222_, lean_object* v_x_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_222_, v_x_223_);
lean_dec(v_x_223_);
lean_dec(v_a_222_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_226_; uint64_t v___x_227_; 
v___x_226_ = lean_unsigned_to_nat(1723u);
v___x_227_ = lean_uint64_of_nat(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(lean_object* v_m_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_buckets_230_; lean_object* v___x_231_; uint64_t v___y_233_; 
v_buckets_230_ = lean_ctor_get(v_m_228_, 1);
v___x_231_ = lean_array_get_size(v_buckets_230_);
if (lean_obj_tag(v_a_229_) == 0)
{
uint64_t v___x_247_; 
v___x_247_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_233_ = v___x_247_;
goto v___jp_232_;
}
else
{
uint64_t v_hash_248_; 
v_hash_248_ = lean_ctor_get_uint64(v_a_229_, sizeof(void*)*2);
v___y_233_ = v_hash_248_;
goto v___jp_232_;
}
v___jp_232_:
{
uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v_fold_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_234_ = 32ULL;
v___x_235_ = lean_uint64_shift_right(v___y_233_, v___x_234_);
v_fold_236_ = lean_uint64_xor(v___y_233_, v___x_235_);
v___x_237_ = 16ULL;
v___x_238_ = lean_uint64_shift_right(v_fold_236_, v___x_237_);
v___x_239_ = lean_uint64_xor(v_fold_236_, v___x_238_);
v___x_240_ = lean_uint64_to_usize(v___x_239_);
v___x_241_ = lean_usize_of_nat(v___x_231_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_sub(v___x_241_, v___x_242_);
v___x_244_ = lean_usize_land(v___x_240_, v___x_243_);
v___x_245_ = lean_array_uget_borrowed(v_buckets_230_, v___x_244_);
v___x_246_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_229_, v___x_245_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___boxed(lean_object* v_m_249_, lean_object* v_a_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_m_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object* v_inherited_253_, lean_object* v_opts_254_, lean_object* v_opt_255_){
_start:
{
lean_object* v_map_261_; lean_object* v___x_262_; 
v_map_261_ = lean_ctor_get(v_opts_254_, 0);
v___x_262_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_261_, v_opt_255_);
if (lean_obj_tag(v___x_262_) == 0)
{
goto v___jp_256_;
}
else
{
lean_object* v_val_263_; 
v_val_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_val_263_);
lean_dec_ref(v___x_262_);
if (lean_obj_tag(v_val_263_) == 1)
{
uint8_t v_v_264_; 
v_v_264_ = lean_ctor_get_uint8(v_val_263_, 0);
lean_dec_ref(v_val_263_);
return v_v_264_;
}
else
{
lean_dec(v_val_263_);
goto v___jp_256_;
}
}
v___jp_256_:
{
if (lean_obj_tag(v_opt_255_) == 1)
{
lean_object* v_pre_257_; uint8_t v___x_258_; 
v_pre_257_ = lean_ctor_get(v_opt_255_, 0);
v___x_258_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_inherited_253_, v_opt_255_);
if (v___x_258_ == 0)
{
return v___x_258_;
}
else
{
v_opt_255_ = v_pre_257_;
goto _start;
}
}
else
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go___boxed(lean_object* v_inherited_265_, lean_object* v_opts_266_, lean_object* v_opt_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_265_, v_opts_266_, v_opt_267_);
lean_dec(v_opt_267_);
lean_dec_ref(v_opts_266_);
lean_dec_ref(v_inherited_265_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(lean_object* v_00_u03b2_270_, lean_object* v_m_271_, lean_object* v_a_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_271_, v_a_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(lean_object* v_00_u03b2_274_, lean_object* v_m_275_, lean_object* v_a_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(v_00_u03b2_274_, v_m_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_m_275_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(lean_object* v_00_u03b2_279_, lean_object* v_a_280_, lean_object* v_x_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_280_, v_x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_283_, lean_object* v_a_284_, lean_object* v_x_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(v_00_u03b2_283_, v_a_284_, v_x_285_);
lean_dec(v_x_285_);
lean_dec(v_a_284_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT uint8_t l_Lean_checkTraceOption(lean_object* v_inherited_291_, lean_object* v_opts_292_, lean_object* v_cls_293_){
_start:
{
uint8_t v_hasTrace_294_; 
v_hasTrace_294_ = lean_ctor_get_uint8(v_opts_292_, sizeof(void*)*1);
if (v_hasTrace_294_ == 0)
{
lean_dec(v_cls_293_);
return v_hasTrace_294_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_296_ = l_Lean_Name_append(v___x_295_, v_cls_293_);
v___x_297_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_291_, v_opts_292_, v___x_296_);
lean_dec(v___x_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkTraceOption___boxed(lean_object* v_inherited_298_, lean_object* v_opts_299_, lean_object* v_cls_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Lean_checkTraceOption(v_inherited_298_, v_opts_299_, v_cls_300_);
lean_dec_ref(v_opts_299_);
lean_dec_ref(v_inherited_298_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0(lean_object* v_toPure_303_, lean_object* v_cls_304_, lean_object* v_____do__lift_305_, lean_object* v_____do__lift_306_){
_start:
{
uint8_t v_hasTrace_307_; 
v_hasTrace_307_ = lean_ctor_get_uint8(v_____do__lift_306_, sizeof(void*)*1);
if (v_hasTrace_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_cls_304_);
v___x_308_ = lean_box(v_hasTrace_307_);
v___x_309_ = lean_apply_2(v_toPure_303_, lean_box(0), v___x_308_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_310_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_311_ = l_Lean_Name_append(v___x_310_, v_cls_304_);
v___x_312_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_305_, v_____do__lift_306_, v___x_311_);
lean_dec(v___x_311_);
v___x_313_ = lean_box(v___x_312_);
v___x_314_ = lean_apply_2(v_toPure_303_, lean_box(0), v___x_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0___boxed(lean_object* v_toPure_315_, lean_object* v_cls_316_, lean_object* v_____do__lift_317_, lean_object* v_____do__lift_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_isTracingEnabledFor___redArg___lam__0(v_toPure_315_, v_cls_316_, v_____do__lift_317_, v_____do__lift_318_);
lean_dec_ref(v_____do__lift_318_);
lean_dec_ref(v_____do__lift_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__1(lean_object* v_toPure_320_, lean_object* v_cls_321_, lean_object* v_toBind_322_, lean_object* v_inst_323_, lean_object* v_____do__lift_324_){
_start:
{
lean_object* v___f_325_; lean_object* v___x_326_; 
v___f_325_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_325_, 0, v_toPure_320_);
lean_closure_set(v___f_325_, 1, v_cls_321_);
lean_closure_set(v___f_325_, 2, v_____do__lift_324_);
v___x_326_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v_inst_323_, v___f_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_cls_330_){
_start:
{
lean_object* v_toApplicative_331_; lean_object* v_toBind_332_; lean_object* v_getInheritedTraceOptions_333_; lean_object* v_toPure_334_; lean_object* v___f_335_; lean_object* v___x_336_; 
v_toApplicative_331_ = lean_ctor_get(v_inst_327_, 0);
lean_inc_ref(v_toApplicative_331_);
v_toBind_332_ = lean_ctor_get(v_inst_327_, 1);
lean_inc_n(v_toBind_332_, 2);
lean_dec_ref(v_inst_327_);
v_getInheritedTraceOptions_333_ = lean_ctor_get(v_inst_328_, 2);
lean_inc(v_getInheritedTraceOptions_333_);
lean_dec_ref(v_inst_328_);
v_toPure_334_ = lean_ctor_get(v_toApplicative_331_, 1);
lean_inc(v_toPure_334_);
lean_dec_ref(v_toApplicative_331_);
v___f_335_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_335_, 0, v_toPure_334_);
lean_closure_set(v___f_335_, 1, v_cls_330_);
lean_closure_set(v___f_335_, 2, v_toBind_332_);
lean_closure_set(v___f_335_, 3, v_inst_329_);
v___x_336_ = lean_apply_4(v_toBind_332_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_333_, v___f_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor(lean_object* v_m_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_cls_341_){
_start:
{
lean_object* v_toApplicative_342_; lean_object* v_toBind_343_; lean_object* v_getInheritedTraceOptions_344_; lean_object* v_toPure_345_; lean_object* v___f_346_; lean_object* v___x_347_; 
v_toApplicative_342_ = lean_ctor_get(v_inst_338_, 0);
lean_inc_ref(v_toApplicative_342_);
v_toBind_343_ = lean_ctor_get(v_inst_338_, 1);
lean_inc_n(v_toBind_343_, 2);
lean_dec_ref(v_inst_338_);
v_getInheritedTraceOptions_344_ = lean_ctor_get(v_inst_339_, 2);
lean_inc(v_getInheritedTraceOptions_344_);
lean_dec_ref(v_inst_339_);
v_toPure_345_ = lean_ctor_get(v_toApplicative_342_, 1);
lean_inc(v_toPure_345_);
lean_dec_ref(v_toApplicative_342_);
v___f_346_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_346_, 0, v_toPure_345_);
lean_closure_set(v___f_346_, 1, v_cls_341_);
lean_closure_set(v___f_346_, 2, v_toBind_343_);
lean_closure_set(v___f_346_, 3, v_inst_340_);
v___x_347_ = lean_apply_4(v_toBind_343_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_344_, v___f_346_);
return v___x_347_;
}
}
LEAN_EXPORT uint8_t lean_is_trace_class_enabled(lean_object* v_opts_348_, lean_object* v_cls_349_){
_start:
{
uint8_t v_hasTrace_351_; 
v_hasTrace_351_ = lean_ctor_get_uint8(v_opts_348_, sizeof(void*)*1);
if (v_hasTrace_351_ == 0)
{
lean_dec(v_cls_349_);
lean_dec_ref(v_opts_348_);
return v_hasTrace_351_;
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_352_ = l_Lean_inheritedTraceOptions;
v___x_353_ = lean_st_ref_get(v___x_352_);
v___x_354_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_355_ = l_Lean_Name_append(v___x_354_, v_cls_349_);
v___x_356_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_353_, v_opts_348_, v___x_355_);
lean_dec(v___x_355_);
lean_dec_ref(v_opts_348_);
lean_dec(v___x_353_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object* v_opts_357_, lean_object* v_cls_358_, lean_object* v_a_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = lean_is_trace_class_enabled(v_opts_357_, v_cls_358_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object* v_toPure_362_, lean_object* v_s_363_){
_start:
{
lean_object* v_traces_364_; lean_object* v___x_365_; 
v_traces_364_ = lean_ctor_get(v_s_363_, 0);
lean_inc_ref(v_traces_364_);
lean_dec_ref(v_s_363_);
v___x_365_ = lean_apply_2(v_toPure_362_, lean_box(0), v_traces_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object* v_inst_366_, lean_object* v_inst_367_){
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
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object* v_m_374_, lean_object* v_inst_375_, lean_object* v_inst_376_){
_start:
{
lean_object* v_toApplicative_377_; lean_object* v_toBind_378_; lean_object* v_getTraceState_379_; lean_object* v_toPure_380_; lean_object* v___f_381_; lean_object* v___x_382_; 
v_toApplicative_377_ = lean_ctor_get(v_inst_375_, 0);
lean_inc_ref(v_toApplicative_377_);
v_toBind_378_ = lean_ctor_get(v_inst_375_, 1);
lean_inc(v_toBind_378_);
lean_dec_ref(v_inst_375_);
v_getTraceState_379_ = lean_ctor_get(v_inst_376_, 1);
lean_inc(v_getTraceState_379_);
lean_dec_ref(v_inst_376_);
v_toPure_380_ = lean_ctor_get(v_toApplicative_377_, 1);
lean_inc(v_toPure_380_);
lean_dec_ref(v_toApplicative_377_);
v___f_381_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_381_, 0, v_toPure_380_);
v___x_382_ = lean_apply_4(v_toBind_378_, lean_box(0), lean_box(0), v_getTraceState_379_, v___f_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object* v_f_383_, lean_object* v_s_384_){
_start:
{
uint64_t v_tid_385_; lean_object* v_traces_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_394_; 
v_tid_385_ = lean_ctor_get_uint64(v_s_384_, sizeof(void*)*1);
v_traces_386_ = lean_ctor_get(v_s_384_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v_s_384_);
if (v_isSharedCheck_394_ == 0)
{
v___x_388_ = v_s_384_;
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_traces_386_);
lean_dec(v_s_384_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = lean_apply_1(v_f_383_, v_traces_386_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_390_);
v___x_392_ = v___x_388_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
lean_ctor_set_uint64(v_reuseFailAlloc_393_, sizeof(void*)*1, v_tid_385_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object* v_inst_395_, lean_object* v_f_396_){
_start:
{
lean_object* v_modifyTraceState_397_; lean_object* v___f_398_; lean_object* v___x_399_; 
v_modifyTraceState_397_ = lean_ctor_get(v_inst_395_, 0);
lean_inc(v_modifyTraceState_397_);
lean_dec_ref(v_inst_395_);
v___f_398_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_398_, 0, v_f_396_);
v___x_399_ = lean_apply_1(v_modifyTraceState_397_, v___f_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object* v_m_400_, lean_object* v_inst_401_, lean_object* v_f_402_){
_start:
{
lean_object* v_modifyTraceState_403_; lean_object* v___f_404_; lean_object* v___x_405_; 
v_modifyTraceState_403_ = lean_ctor_get(v_inst_401_, 0);
lean_inc(v_modifyTraceState_403_);
lean_dec_ref(v_inst_401_);
v___f_404_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_404_, 0, v_f_402_);
v___x_405_ = lean_apply_1(v_modifyTraceState_403_, v___f_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object* v_s_406_, lean_object* v_x_407_){
_start:
{
lean_inc_ref(v_s_406_);
return v_s_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object* v_s_408_, lean_object* v_x_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_setTraceState___redArg___lam__0(v_s_408_, v_x_409_);
lean_dec_ref(v_x_409_);
lean_dec_ref(v_s_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object* v_inst_411_, lean_object* v_s_412_){
_start:
{
lean_object* v_modifyTraceState_413_; lean_object* v___f_414_; lean_object* v___x_415_; 
v_modifyTraceState_413_ = lean_ctor_get(v_inst_411_, 0);
lean_inc(v_modifyTraceState_413_);
lean_dec_ref(v_inst_411_);
v___f_414_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_414_, 0, v_s_412_);
v___x_415_ = lean_apply_1(v_modifyTraceState_413_, v___f_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object* v_m_416_, lean_object* v_inst_417_, lean_object* v_s_418_){
_start:
{
lean_object* v_modifyTraceState_419_; lean_object* v___f_420_; lean_object* v___x_421_; 
v_modifyTraceState_419_ = lean_ctor_get(v_inst_417_, 0);
lean_inc(v_modifyTraceState_419_);
lean_dec_ref(v_inst_417_);
v___f_420_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_420_, 0, v_s_418_);
v___x_421_ = lean_apply_1(v_modifyTraceState_419_, v___f_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object* v_s_422_){
_start:
{
uint64_t v_tid_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_433_; 
v_tid_423_ = lean_ctor_get_uint64(v_s_422_, sizeof(void*)*1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_s_422_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v_s_422_, 0);
lean_dec(v_unused_434_);
v___x_425_ = v_s_422_;
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
else
{
lean_dec(v_s_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_433_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_427_ = lean_unsigned_to_nat(32u);
v___x_428_ = lean_mk_empty_array_with_capacity(v___x_427_);
lean_dec_ref(v___x_428_);
v___x_429_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__1, &l_Lean_instInhabitedTraceState_default___closed__1_once, _init_l_Lean_instInhabitedTraceState_default___closed__1);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_429_);
v___x_431_ = v___x_425_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
lean_ctor_set_uint64(v_reuseFailAlloc_432_, sizeof(void*)*1, v_tid_423_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object* v_toPure_435_, lean_object* v_oldTraces_436_, lean_object* v_____r_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = lean_apply_2(v_toPure_435_, lean_box(0), v_oldTraces_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object* v_toPure_439_, lean_object* v_modifyTraceState_440_, lean_object* v___f_441_, lean_object* v_toBind_442_, lean_object* v_oldTraces_443_){
_start:
{
lean_object* v___f_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___f_444_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_444_, 0, v_toPure_439_);
lean_closure_set(v___f_444_, 1, v_oldTraces_443_);
v___x_445_ = lean_apply_1(v_modifyTraceState_440_, v___f_441_);
v___x_446_ = lean_apply_4(v_toBind_442_, lean_box(0), lean_box(0), v___x_445_, v___f_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object* v_inst_448_, lean_object* v_inst_449_){
_start:
{
lean_object* v_toApplicative_450_; lean_object* v_toBind_451_; lean_object* v_modifyTraceState_452_; lean_object* v_getTraceState_453_; lean_object* v_toPure_454_; lean_object* v___f_455_; lean_object* v___f_456_; lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_toApplicative_450_ = lean_ctor_get(v_inst_448_, 0);
lean_inc_ref(v_toApplicative_450_);
v_toBind_451_ = lean_ctor_get(v_inst_448_, 1);
lean_inc_n(v_toBind_451_, 3);
lean_dec_ref(v_inst_448_);
v_modifyTraceState_452_ = lean_ctor_get(v_inst_449_, 0);
lean_inc(v_modifyTraceState_452_);
v_getTraceState_453_ = lean_ctor_get(v_inst_449_, 1);
lean_inc(v_getTraceState_453_);
lean_dec_ref(v_inst_449_);
v_toPure_454_ = lean_ctor_get(v_toApplicative_450_, 1);
lean_inc_n(v_toPure_454_, 2);
lean_dec_ref(v_toApplicative_450_);
v___f_455_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0));
v___f_456_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_456_, 0, v_toPure_454_);
lean_closure_set(v___f_456_, 1, v_modifyTraceState_452_);
lean_closure_set(v___f_456_, 2, v___f_455_);
lean_closure_set(v___f_456_, 3, v_toBind_451_);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_457_, 0, v_toPure_454_);
v___x_458_ = lean_apply_4(v_toBind_451_, lean_box(0), lean_box(0), v_getTraceState_453_, v___f_457_);
v___x_459_ = lean_apply_4(v_toBind_451_, lean_box(0), lean_box(0), v___x_458_, v___f_456_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object* v_m_460_, lean_object* v_inst_461_, lean_object* v_inst_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_461_, v_inst_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object* v_ref_464_, lean_object* v_msg_465_, lean_object* v_s_466_){
_start:
{
uint64_t v_tid_467_; lean_object* v_traces_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_477_; 
v_tid_467_ = lean_ctor_get_uint64(v_s_466_, sizeof(void*)*1);
v_traces_468_ = lean_ctor_get(v_s_466_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_s_466_);
if (v_isSharedCheck_477_ == 0)
{
v___x_470_ = v_s_466_;
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_traces_468_);
lean_dec(v_s_466_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v_ref_464_);
lean_ctor_set(v___x_472_, 1, v_msg_465_);
v___x_473_ = l_Lean_PersistentArray_push___redArg(v_traces_468_, v___x_472_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_473_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
lean_ctor_set_uint64(v_reuseFailAlloc_476_, sizeof(void*)*1, v_tid_467_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object* v_inst_478_, lean_object* v_ref_479_, lean_object* v_msg_480_){
_start:
{
lean_object* v_modifyTraceState_481_; lean_object* v___f_482_; lean_object* v___x_483_; 
v_modifyTraceState_481_ = lean_ctor_get(v_inst_478_, 0);
lean_inc(v_modifyTraceState_481_);
lean_dec_ref(v_inst_478_);
v___f_482_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__0), 3, 2);
lean_closure_set(v___f_482_, 0, v_ref_479_);
lean_closure_set(v___f_482_, 1, v_msg_480_);
v___x_483_ = lean_apply_1(v_modifyTraceState_481_, v___f_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_msg_486_, lean_object* v_toBind_487_, lean_object* v_ref_488_){
_start:
{
lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___f_489_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__1), 3, 2);
lean_closure_set(v___f_489_, 0, v_inst_484_);
lean_closure_set(v___f_489_, 1, v_ref_488_);
v___x_490_ = lean_apply_1(v_inst_485_, v_msg_486_);
v___x_491_ = lean_apply_4(v_toBind_487_, lean_box(0), lean_box(0), v___x_490_, v___f_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_msg_496_){
_start:
{
lean_object* v_toBind_497_; lean_object* v_getRef_498_; lean_object* v___f_499_; lean_object* v___x_500_; 
v_toBind_497_ = lean_ctor_get(v_inst_492_, 1);
lean_inc_n(v_toBind_497_, 2);
lean_dec_ref(v_inst_492_);
v_getRef_498_ = lean_ctor_get(v_inst_494_, 0);
lean_inc(v_getRef_498_);
lean_dec_ref(v_inst_494_);
v___f_499_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__2), 5, 4);
lean_closure_set(v___f_499_, 0, v_inst_493_);
lean_closure_set(v___f_499_, 1, v_inst_495_);
lean_closure_set(v___f_499_, 2, v_msg_496_);
lean_closure_set(v___f_499_, 3, v_toBind_497_);
v___x_500_ = lean_apply_4(v_toBind_497_, lean_box(0), lean_box(0), v_getRef_498_, v___f_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object* v_m_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_msg_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_addRawTrace___redArg(v_inst_502_, v_inst_503_, v_inst_504_, v_inst_505_, v_msg_506_);
return v___x_507_;
}
}
static double _init_l_Lean_addTrace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_508_; double v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_float_of_nat(v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object* v_cls_513_, lean_object* v_msg_514_, lean_object* v_ref_515_, lean_object* v_s_516_){
_start:
{
uint64_t v_tid_517_; lean_object* v_traces_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_534_; 
v_tid_517_ = lean_ctor_get_uint64(v_s_516_, sizeof(void*)*1);
v_traces_518_ = lean_ctor_get(v_s_516_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_s_516_);
if (v_isSharedCheck_534_ == 0)
{
v___x_520_ = v_s_516_;
v_isShared_521_ = v_isSharedCheck_534_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_traces_518_);
lean_dec(v_s_516_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_534_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; double v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_522_ = lean_box(0);
v___x_523_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
v___x_524_ = 0;
v___x_525_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_526_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_526_, 0, v_cls_513_);
lean_ctor_set(v___x_526_, 1, v___x_522_);
lean_ctor_set(v___x_526_, 2, v___x_525_);
lean_ctor_set_float(v___x_526_, sizeof(void*)*3, v___x_523_);
lean_ctor_set_float(v___x_526_, sizeof(void*)*3 + 8, v___x_523_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*3 + 16, v___x_524_);
v___x_527_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
v___x_528_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v_msg_514_);
lean_ctor_set(v___x_528_, 2, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_ref_515_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_PersistentArray_push___redArg(v_traces_518_, v___x_529_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_530_);
v___x_532_ = v___x_520_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
lean_ctor_set_uint64(v_reuseFailAlloc_533_, sizeof(void*)*1, v_tid_517_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object* v_inst_535_, lean_object* v_cls_536_, lean_object* v_ref_537_, lean_object* v_msg_538_){
_start:
{
lean_object* v_modifyTraceState_539_; lean_object* v___f_540_; lean_object* v___x_541_; 
v_modifyTraceState_539_ = lean_ctor_get(v_inst_535_, 0);
lean_inc(v_modifyTraceState_539_);
lean_dec_ref(v_inst_535_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_540_, 0, v_cls_536_);
lean_closure_set(v___f_540_, 1, v_msg_538_);
lean_closure_set(v___f_540_, 2, v_ref_537_);
v___x_541_ = lean_apply_1(v_modifyTraceState_539_, v___f_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object* v_inst_542_, lean_object* v_cls_543_, lean_object* v_inst_544_, lean_object* v_msg_545_, lean_object* v_toBind_546_, lean_object* v_ref_547_){
_start:
{
lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___f_548_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__1), 4, 3);
lean_closure_set(v___f_548_, 0, v_inst_542_);
lean_closure_set(v___f_548_, 1, v_cls_543_);
lean_closure_set(v___f_548_, 2, v_ref_547_);
v___x_549_ = lean_apply_1(v_inst_544_, v_msg_545_);
v___x_550_ = lean_apply_4(v_toBind_546_, lean_box(0), lean_box(0), v___x_549_, v___f_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_cls_555_, lean_object* v_msg_556_){
_start:
{
lean_object* v_toBind_557_; lean_object* v_getRef_558_; lean_object* v___f_559_; lean_object* v___x_560_; 
v_toBind_557_ = lean_ctor_get(v_inst_551_, 1);
lean_inc_n(v_toBind_557_, 2);
lean_dec_ref(v_inst_551_);
v_getRef_558_ = lean_ctor_get(v_inst_553_, 0);
lean_inc(v_getRef_558_);
lean_dec_ref(v_inst_553_);
v___f_559_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__2), 6, 5);
lean_closure_set(v___f_559_, 0, v_inst_552_);
lean_closure_set(v___f_559_, 1, v_cls_555_);
lean_closure_set(v___f_559_, 2, v_inst_554_);
lean_closure_set(v___f_559_, 3, v_msg_556_);
lean_closure_set(v___f_559_, 4, v_toBind_557_);
v___x_560_ = lean_apply_4(v_toBind_557_, lean_box(0), lean_box(0), v_getRef_558_, v___f_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object* v_m_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_cls_566_, lean_object* v_msg_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_addTrace___redArg(v_inst_562_, v_inst_563_, v_inst_564_, v_inst_565_, v_cls_566_, v_msg_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0(lean_object* v_toPure_569_, lean_object* v_msg_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_cls_575_, uint8_t v_____do__lift_576_){
_start:
{
if (v_____do__lift_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v_cls_575_);
lean_dec(v_inst_574_);
lean_dec_ref(v_inst_573_);
lean_dec_ref(v_inst_572_);
lean_dec_ref(v_inst_571_);
lean_dec_ref(v_msg_570_);
v___x_577_ = lean_box(0);
v___x_578_ = lean_apply_2(v_toPure_569_, lean_box(0), v___x_577_);
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_toPure_569_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_apply_1(v_msg_570_, v___x_579_);
v___x_581_ = l_Lean_addTrace___redArg(v_inst_571_, v_inst_572_, v_inst_573_, v_inst_574_, v_cls_575_, v___x_580_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object* v_toPure_582_, lean_object* v_msg_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_cls_588_, lean_object* v_____do__lift_589_){
_start:
{
uint8_t v_____do__lift_147__boxed_590_; lean_object* v_res_591_; 
v_____do__lift_147__boxed_590_ = lean_unbox(v_____do__lift_589_);
v_res_591_ = l_Lean_trace___redArg___lam__0(v_toPure_582_, v_msg_583_, v_inst_584_, v_inst_585_, v_inst_586_, v_inst_587_, v_cls_588_, v_____do__lift_147__boxed_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_cls_597_, lean_object* v_msg_598_){
_start:
{
lean_object* v_toApplicative_599_; lean_object* v_toBind_600_; lean_object* v_getInheritedTraceOptions_601_; lean_object* v_toPure_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_toApplicative_599_ = lean_ctor_get(v_inst_592_, 0);
v_toBind_600_ = lean_ctor_get(v_inst_592_, 1);
lean_inc_n(v_toBind_600_, 3);
v_getInheritedTraceOptions_601_ = lean_ctor_get(v_inst_593_, 2);
lean_inc(v_getInheritedTraceOptions_601_);
v_toPure_602_ = lean_ctor_get(v_toApplicative_599_, 1);
lean_inc_n(v_toPure_602_, 2);
lean_inc(v_cls_597_);
v___f_603_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_603_, 0, v_toPure_602_);
lean_closure_set(v___f_603_, 1, v_msg_598_);
lean_closure_set(v___f_603_, 2, v_inst_592_);
lean_closure_set(v___f_603_, 3, v_inst_593_);
lean_closure_set(v___f_603_, 4, v_inst_594_);
lean_closure_set(v___f_603_, 5, v_inst_595_);
lean_closure_set(v___f_603_, 6, v_cls_597_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_604_, 0, v_toPure_602_);
lean_closure_set(v___f_604_, 1, v_cls_597_);
lean_closure_set(v___f_604_, 2, v_toBind_600_);
lean_closure_set(v___f_604_, 3, v_inst_596_);
v___x_605_ = lean_apply_4(v_toBind_600_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_601_, v___f_604_);
v___x_606_ = lean_apply_4(v_toBind_600_, lean_box(0), lean_box(0), v___x_605_, v___f_603_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace(lean_object* v_m_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_cls_613_, lean_object* v_msg_614_){
_start:
{
lean_object* v_toApplicative_615_; lean_object* v_toBind_616_; lean_object* v_getInheritedTraceOptions_617_; lean_object* v_toPure_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_toApplicative_615_ = lean_ctor_get(v_inst_608_, 0);
v_toBind_616_ = lean_ctor_get(v_inst_608_, 1);
lean_inc_n(v_toBind_616_, 3);
v_getInheritedTraceOptions_617_ = lean_ctor_get(v_inst_609_, 2);
lean_inc(v_getInheritedTraceOptions_617_);
v_toPure_618_ = lean_ctor_get(v_toApplicative_615_, 1);
lean_inc_n(v_toPure_618_, 2);
lean_inc(v_cls_613_);
v___f_619_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_619_, 0, v_toPure_618_);
lean_closure_set(v___f_619_, 1, v_msg_614_);
lean_closure_set(v___f_619_, 2, v_inst_608_);
lean_closure_set(v___f_619_, 3, v_inst_609_);
lean_closure_set(v___f_619_, 4, v_inst_610_);
lean_closure_set(v___f_619_, 5, v_inst_611_);
lean_closure_set(v___f_619_, 6, v_cls_613_);
v___f_620_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_620_, 0, v_toPure_618_);
lean_closure_set(v___f_620_, 1, v_cls_613_);
lean_closure_set(v___f_620_, 2, v_toBind_616_);
lean_closure_set(v___f_620_, 3, v_inst_612_);
v___x_621_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_617_, v___f_620_);
v___x_622_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_621_, v___f_619_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_cls_627_, lean_object* v_msg_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_addTrace___redArg(v_inst_623_, v_inst_624_, v_inst_625_, v_inst_626_, v_cls_627_, v_msg_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1(lean_object* v_toPure_630_, lean_object* v_toBind_631_, lean_object* v_mkMsg_632_, lean_object* v___f_633_, uint8_t v_____do__lift_634_){
_start:
{
if (v_____do__lift_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v___f_633_);
lean_dec(v_mkMsg_632_);
lean_dec(v_toBind_631_);
v___x_635_ = lean_box(0);
v___x_636_ = lean_apply_2(v_toPure_630_, lean_box(0), v___x_635_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; 
lean_dec(v_toPure_630_);
v___x_637_ = lean_apply_4(v_toBind_631_, lean_box(0), lean_box(0), v_mkMsg_632_, v___f_633_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object* v_toPure_638_, lean_object* v_toBind_639_, lean_object* v_mkMsg_640_, lean_object* v___f_641_, lean_object* v_____do__lift_642_){
_start:
{
uint8_t v_____do__lift_153__boxed_643_; lean_object* v_res_644_; 
v_____do__lift_153__boxed_643_ = lean_unbox(v_____do__lift_642_);
v_res_644_ = l_Lean_traceM___redArg___lam__1(v_toPure_638_, v_toBind_639_, v_mkMsg_640_, v___f_641_, v_____do__lift_153__boxed_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_cls_650_, lean_object* v_mkMsg_651_){
_start:
{
lean_object* v_toApplicative_652_; lean_object* v_toBind_653_; lean_object* v_getInheritedTraceOptions_654_; lean_object* v_toPure_655_; lean_object* v___f_656_; lean_object* v___f_657_; lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_toApplicative_652_ = lean_ctor_get(v_inst_645_, 0);
v_toBind_653_ = lean_ctor_get(v_inst_645_, 1);
lean_inc_n(v_toBind_653_, 4);
v_getInheritedTraceOptions_654_ = lean_ctor_get(v_inst_646_, 2);
lean_inc(v_getInheritedTraceOptions_654_);
v_toPure_655_ = lean_ctor_get(v_toApplicative_652_, 1);
lean_inc_n(v_toPure_655_, 2);
lean_inc(v_cls_650_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_656_, 0, v_inst_645_);
lean_closure_set(v___f_656_, 1, v_inst_646_);
lean_closure_set(v___f_656_, 2, v_inst_647_);
lean_closure_set(v___f_656_, 3, v_inst_648_);
lean_closure_set(v___f_656_, 4, v_cls_650_);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_657_, 0, v_toPure_655_);
lean_closure_set(v___f_657_, 1, v_toBind_653_);
lean_closure_set(v___f_657_, 2, v_mkMsg_651_);
lean_closure_set(v___f_657_, 3, v___f_656_);
v___f_658_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_658_, 0, v_toPure_655_);
lean_closure_set(v___f_658_, 1, v_cls_650_);
lean_closure_set(v___f_658_, 2, v_toBind_653_);
lean_closure_set(v___f_658_, 3, v_inst_649_);
v___x_659_ = lean_apply_4(v_toBind_653_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_654_, v___f_658_);
v___x_660_ = lean_apply_4(v_toBind_653_, lean_box(0), lean_box(0), v___x_659_, v___f_657_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object* v_m_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_cls_667_, lean_object* v_mkMsg_668_){
_start:
{
lean_object* v_toApplicative_669_; lean_object* v_toBind_670_; lean_object* v_getInheritedTraceOptions_671_; lean_object* v_toPure_672_; lean_object* v___f_673_; lean_object* v___f_674_; lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_toApplicative_669_ = lean_ctor_get(v_inst_662_, 0);
v_toBind_670_ = lean_ctor_get(v_inst_662_, 1);
lean_inc_n(v_toBind_670_, 4);
v_getInheritedTraceOptions_671_ = lean_ctor_get(v_inst_663_, 2);
lean_inc(v_getInheritedTraceOptions_671_);
v_toPure_672_ = lean_ctor_get(v_toApplicative_669_, 1);
lean_inc_n(v_toPure_672_, 2);
lean_inc(v_cls_667_);
v___f_673_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_673_, 0, v_inst_662_);
lean_closure_set(v___f_673_, 1, v_inst_663_);
lean_closure_set(v___f_673_, 2, v_inst_664_);
lean_closure_set(v___f_673_, 3, v_inst_665_);
lean_closure_set(v___f_673_, 4, v_cls_667_);
v___f_674_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_674_, 0, v_toPure_672_);
lean_closure_set(v___f_674_, 1, v_toBind_670_);
lean_closure_set(v___f_674_, 2, v_mkMsg_668_);
lean_closure_set(v___f_674_, 3, v___f_673_);
v___f_675_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_675_, 0, v_toPure_672_);
lean_closure_set(v___f_675_, 1, v_cls_667_);
lean_closure_set(v___f_675_, 2, v_toBind_670_);
lean_closure_set(v___f_675_, 3, v_inst_666_);
v___x_676_ = lean_apply_4(v_toBind_670_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_671_, v___f_675_);
v___x_677_ = lean_apply_4(v_toBind_670_, lean_box(0), lean_box(0), v___x_676_, v___f_674_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object* v_x_678_){
_start:
{
lean_object* v_msg_679_; 
v_msg_679_ = lean_ctor_get(v_x_678_, 1);
lean_inc_ref(v_msg_679_);
return v_msg_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object* v_x_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_680_);
lean_dec_ref(v_x_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object* v_ref_682_, lean_object* v_msg_683_, lean_object* v_oldTraces_684_, lean_object* v_s_685_){
_start:
{
uint64_t v_tid_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v_tid_686_ = lean_ctor_get_uint64(v_s_685_, sizeof(void*)*1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_s_685_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_s_685_, 0);
lean_dec(v_unused_696_);
v___x_688_ = v_s_685_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_dec(v_s_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_ref_682_);
lean_ctor_set(v___x_690_, 1, v_msg_683_);
v___x_691_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_684_, v___x_690_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
lean_ctor_set_uint64(v_reuseFailAlloc_694_, sizeof(void*)*1, v_tid_686_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object* v_ref_697_, lean_object* v_oldTraces_698_, lean_object* v_modifyTraceState_699_, lean_object* v_msg_700_){
_start:
{
lean_object* v___f_701_; lean_object* v___x_702_; 
v___f_701_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0), 4, 3);
lean_closure_set(v___f_701_, 0, v_ref_697_);
lean_closure_set(v___f_701_, 1, v_msg_700_);
lean_closure_set(v___f_701_, 2, v_oldTraces_698_);
v___x_702_ = lean_apply_1(v_modifyTraceState_699_, v___f_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object* v___f_722_, lean_object* v_data_723_, lean_object* v_msg_724_, lean_object* v_inst_725_, lean_object* v_toBind_726_, lean_object* v___f_727_, lean_object* v_____do__lift_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; size_t v_sz_731_; size_t v___x_732_; lean_object* v___x_733_; lean_object* v_msg_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_729_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_728_);
v___x_730_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v_sz_731_ = lean_array_size(v___x_729_);
v___x_732_ = ((size_t)0ULL);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_730_, v___f_722_, v_sz_731_, v___x_732_, v___x_729_);
v_msg_734_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_734_, 0, v_data_723_);
lean_ctor_set(v_msg_734_, 1, v_msg_724_);
lean_ctor_set(v_msg_734_, 2, v___x_733_);
v___x_735_ = lean_apply_1(v_inst_725_, v_msg_734_);
v___x_736_ = lean_apply_4(v_toBind_726_, lean_box(0), lean_box(0), v___x_735_, v___f_727_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object* v___f_737_, lean_object* v_data_738_, lean_object* v_msg_739_, lean_object* v_inst_740_, lean_object* v_toBind_741_, lean_object* v___f_742_, lean_object* v_____do__lift_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(v___f_737_, v_data_738_, v_msg_739_, v_inst_740_, v_toBind_741_, v___f_742_, v_____do__lift_743_);
lean_dec_ref(v_____do__lift_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object* v_ref_745_, lean_object* v_withRef_746_, lean_object* v___x_747_, lean_object* v_oldRef_748_){
_start:
{
lean_object* v_ref_749_; lean_object* v___x_750_; 
v_ref_749_ = l_Lean_replaceRef(v_ref_745_, v_oldRef_748_);
v___x_750_ = lean_apply_3(v_withRef_746_, lean_box(0), v_ref_749_, v___x_747_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object* v_ref_751_, lean_object* v_withRef_752_, lean_object* v___x_753_, lean_object* v_oldRef_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(v_ref_751_, v_withRef_752_, v___x_753_, v_oldRef_754_);
lean_dec(v_oldRef_754_);
lean_dec(v_ref_751_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_oldTraces_761_, lean_object* v_data_762_, lean_object* v_ref_763_, lean_object* v_msg_764_){
_start:
{
lean_object* v_toApplicative_765_; lean_object* v_toBind_766_; lean_object* v_modifyTraceState_767_; lean_object* v_getTraceState_768_; lean_object* v_toPure_769_; lean_object* v_getRef_770_; lean_object* v_withRef_771_; lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v___x_779_; 
v_toApplicative_765_ = lean_ctor_get(v_inst_757_, 0);
lean_inc_ref(v_toApplicative_765_);
v_toBind_766_ = lean_ctor_get(v_inst_757_, 1);
lean_inc_n(v_toBind_766_, 4);
lean_dec_ref(v_inst_757_);
v_modifyTraceState_767_ = lean_ctor_get(v_inst_758_, 0);
lean_inc(v_modifyTraceState_767_);
v_getTraceState_768_ = lean_ctor_get(v_inst_758_, 1);
lean_inc(v_getTraceState_768_);
lean_dec_ref(v_inst_758_);
v_toPure_769_ = lean_ctor_get(v_toApplicative_765_, 1);
lean_inc(v_toPure_769_);
lean_dec_ref(v_toApplicative_765_);
v_getRef_770_ = lean_ctor_get(v_inst_759_, 0);
lean_inc(v_getRef_770_);
v_withRef_771_ = lean_ctor_get(v_inst_759_, 1);
lean_inc(v_withRef_771_);
lean_dec_ref(v_inst_759_);
v___f_772_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_772_, 0, v_toPure_769_);
v___x_773_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v_getTraceState_768_, v___f_772_);
v___f_774_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0));
lean_inc(v_ref_763_);
v___f_775_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2), 4, 3);
lean_closure_set(v___f_775_, 0, v_ref_763_);
lean_closure_set(v___f_775_, 1, v_oldTraces_761_);
lean_closure_set(v___f_775_, 2, v_modifyTraceState_767_);
v___f_776_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_776_, 0, v___f_774_);
lean_closure_set(v___f_776_, 1, v_data_762_);
lean_closure_set(v___f_776_, 2, v_msg_764_);
lean_closure_set(v___f_776_, 3, v_inst_760_);
lean_closure_set(v___f_776_, 4, v_toBind_766_);
lean_closure_set(v___f_776_, 5, v___f_775_);
v___x_777_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v___x_773_, v___f_776_);
v___f_778_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_778_, 0, v_ref_763_);
lean_closure_set(v___f_778_, 1, v_withRef_771_);
lean_closure_set(v___f_778_, 2, v___x_777_);
v___x_779_ = lean_apply_4(v_toBind_766_, lean_box(0), lean_box(0), v_getRef_770_, v___f_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object* v_m_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_oldTraces_785_, lean_object* v_data_786_, lean_object* v_ref_787_, lean_object* v_msg_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_781_, v_inst_782_, v_inst_783_, v_inst_784_, v_oldTraces_785_, v_data_786_, v_ref_787_, v_msg_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object* v_name_790_, lean_object* v_decl_791_, lean_object* v_ref_792_){
_start:
{
lean_object* v_defValue_794_; lean_object* v_descr_795_; lean_object* v_deprecation_x3f_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_defValue_794_ = lean_ctor_get(v_decl_791_, 0);
v_descr_795_ = lean_ctor_get(v_decl_791_, 1);
v_deprecation_x3f_796_ = lean_ctor_get(v_decl_791_, 2);
v___x_797_ = lean_alloc_ctor(1, 0, 1);
v___x_798_ = lean_unbox(v_defValue_794_);
lean_ctor_set_uint8(v___x_797_, 0, v___x_798_);
lean_inc(v_deprecation_x3f_796_);
lean_inc_ref(v_descr_795_);
lean_inc_n(v_name_790_, 2);
v___x_799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_799_, 0, v_name_790_);
lean_ctor_set(v___x_799_, 1, v_ref_792_);
lean_ctor_set(v___x_799_, 2, v___x_797_);
lean_ctor_set(v___x_799_, 3, v_descr_795_);
lean_ctor_set(v___x_799_, 4, v_deprecation_x3f_796_);
v___x_800_ = lean_register_option(v_name_790_, v___x_799_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___x_800_, 0);
lean_dec(v_unused_809_);
v___x_802_ = v___x_800_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_dec(v___x_800_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
lean_inc(v_defValue_794_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_name_790_);
lean_ctor_set(v___x_804_, 1, v_defValue_794_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_804_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_name_790_);
v_a_810_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_800_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_800_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_818_, lean_object* v_decl_819_, lean_object* v_ref_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_818_, v_decl_819_, v_ref_820_);
lean_dec_ref(v_decl_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_838_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_839_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_840_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_841_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_838_, v___x_839_, v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object* v_name_844_, lean_object* v_decl_845_, lean_object* v_ref_846_){
_start:
{
lean_object* v_defValue_848_; lean_object* v_descr_849_; lean_object* v_deprecation_x3f_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_defValue_848_ = lean_ctor_get(v_decl_845_, 0);
v_descr_849_ = lean_ctor_get(v_decl_845_, 1);
v_deprecation_x3f_850_ = lean_ctor_get(v_decl_845_, 2);
lean_inc(v_defValue_848_);
v___x_851_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_851_, 0, v_defValue_848_);
lean_inc(v_deprecation_x3f_850_);
lean_inc_ref(v_descr_849_);
lean_inc_n(v_name_844_, 2);
v___x_852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_852_, 0, v_name_844_);
lean_ctor_set(v___x_852_, 1, v_ref_846_);
lean_ctor_set(v___x_852_, 2, v___x_851_);
lean_ctor_set(v___x_852_, 3, v_descr_849_);
lean_ctor_set(v___x_852_, 4, v_deprecation_x3f_850_);
v___x_853_ = lean_register_option(v_name_844_, v___x_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_861_; 
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v___x_853_, 0);
lean_dec(v_unused_862_);
v___x_855_ = v___x_853_;
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
else
{
lean_dec(v___x_853_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
lean_inc(v_defValue_848_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_name_844_);
lean_ctor_set(v___x_857_, 1, v_defValue_848_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec(v_name_844_);
v_a_863_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_853_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_853_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_871_, lean_object* v_decl_872_, lean_object* v_ref_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_871_, v_decl_872_, v_ref_873_);
lean_dec_ref(v_decl_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_892_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_893_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_894_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_895_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_892_, v___x_893_, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_915_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_916_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_917_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_918_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_915_, v___x_916_, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object* v_name_921_, lean_object* v_decl_922_, lean_object* v_ref_923_){
_start:
{
lean_object* v_defValue_925_; lean_object* v_descr_926_; lean_object* v_deprecation_x3f_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_defValue_925_ = lean_ctor_get(v_decl_922_, 0);
v_descr_926_ = lean_ctor_get(v_decl_922_, 1);
v_deprecation_x3f_927_ = lean_ctor_get(v_decl_922_, 2);
lean_inc(v_defValue_925_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v_defValue_925_);
lean_inc(v_deprecation_x3f_927_);
lean_inc_ref(v_descr_926_);
lean_inc_n(v_name_921_, 2);
v___x_929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_929_, 0, v_name_921_);
lean_ctor_set(v___x_929_, 1, v_ref_923_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
lean_ctor_set(v___x_929_, 3, v_descr_926_);
lean_ctor_set(v___x_929_, 4, v_deprecation_x3f_927_);
v___x_930_ = lean_register_option(v_name_921_, v___x_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_938_; 
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v___x_930_, 0);
lean_dec(v_unused_939_);
v___x_932_ = v___x_930_;
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
else
{
lean_dec(v___x_930_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
lean_inc(v_defValue_925_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_name_921_);
lean_ctor_set(v___x_934_, 1, v_defValue_925_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_934_);
v___x_936_ = v___x_932_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_name_921_);
v_a_940_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_930_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_930_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_948_, lean_object* v_decl_949_, lean_object* v_ref_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_948_, v_decl_949_, v_ref_950_);
lean_dec_ref(v_decl_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_970_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_971_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_972_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_969_, v___x_970_, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_994_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_995_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_996_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_997_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_994_, v___x_995_, v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
return v_res_999_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1000_; double v___x_1001_; 
v___x_1000_ = lean_unsigned_to_nat(1000000000u);
v___x_1001_ = lean_float_of_nat(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object* v_toApplicative_1002_, lean_object* v_start_1003_, lean_object* v_a_1004_, lean_object* v_stop_1005_){
_start:
{
lean_object* v_toPure_1006_; double v___x_1007_; double v___x_1008_; double v___x_1009_; double v___x_1010_; double v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_toPure_1006_ = lean_ctor_get(v_toApplicative_1002_, 1);
lean_inc(v_toPure_1006_);
lean_dec_ref(v_toApplicative_1002_);
v___x_1007_ = lean_float_of_nat(v_start_1003_);
v___x_1008_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1009_ = lean_float_div(v___x_1007_, v___x_1008_);
v___x_1010_ = lean_float_of_nat(v_stop_1005_);
v___x_1011_ = lean_float_div(v___x_1010_, v___x_1008_);
v___x_1012_ = lean_box_float(v___x_1009_);
v___x_1013_ = lean_box_float(v___x_1011_);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_a_1004_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_apply_2(v_toPure_1006_, lean_box(0), v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object* v_toApplicative_1017_, lean_object* v_start_1018_, lean_object* v_toBind_1019_, lean_object* v___x_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___f_1022_; lean_object* v___x_1023_; 
v___f_1022_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1022_, 0, v_toApplicative_1017_);
lean_closure_set(v___f_1022_, 1, v_start_1018_);
lean_closure_set(v___f_1022_, 2, v_a_1021_);
v___x_1023_ = lean_apply_4(v_toBind_1019_, lean_box(0), lean_box(0), v___x_1020_, v___f_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object* v_toApplicative_1024_, lean_object* v_toBind_1025_, lean_object* v___x_1026_, lean_object* v_act_1027_, lean_object* v_start_1028_){
_start:
{
lean_object* v___f_1029_; lean_object* v___x_1030_; 
lean_inc(v_toBind_1025_);
v___f_1029_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1029_, 0, v_toApplicative_1024_);
lean_closure_set(v___f_1029_, 1, v_start_1028_);
lean_closure_set(v___f_1029_, 2, v_toBind_1025_);
lean_closure_set(v___f_1029_, 3, v___x_1026_);
v___x_1030_ = lean_apply_4(v_toBind_1025_, lean_box(0), lean_box(0), v_act_1027_, v___f_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object* v_toApplicative_1031_, lean_object* v_start_1032_, lean_object* v_a_1033_, lean_object* v_stop_1034_){
_start:
{
lean_object* v_toPure_1035_; double v___x_1036_; double v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_toPure_1035_ = lean_ctor_get(v_toApplicative_1031_, 1);
lean_inc(v_toPure_1035_);
lean_dec_ref(v_toApplicative_1031_);
v___x_1036_ = lean_float_of_nat(v_start_1032_);
v___x_1037_ = lean_float_of_nat(v_stop_1034_);
v___x_1038_ = lean_box_float(v___x_1036_);
v___x_1039_ = lean_box_float(v___x_1037_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_a_1033_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object* v_toApplicative_1043_, lean_object* v_start_1044_, lean_object* v_toBind_1045_, lean_object* v___x_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___f_1048_; lean_object* v___x_1049_; 
v___f_1048_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1048_, 0, v_toApplicative_1043_);
lean_closure_set(v___f_1048_, 1, v_start_1044_);
lean_closure_set(v___f_1048_, 2, v_a_1047_);
v___x_1049_ = lean_apply_4(v_toBind_1045_, lean_box(0), lean_box(0), v___x_1046_, v___f_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object* v_toApplicative_1050_, lean_object* v_toBind_1051_, lean_object* v___x_1052_, lean_object* v_act_1053_, lean_object* v_start_1054_){
_start:
{
lean_object* v___f_1055_; lean_object* v___x_1056_; 
lean_inc(v_toBind_1051_);
v___f_1055_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1055_, 0, v_toApplicative_1050_);
lean_closure_set(v___f_1055_, 1, v_start_1054_);
lean_closure_set(v___f_1055_, 2, v_toBind_1051_);
lean_closure_set(v___f_1055_, 3, v___x_1052_);
v___x_1056_ = lean_apply_4(v_toBind_1051_, lean_box(0), lean_box(0), v_act_1053_, v___f_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_opts_1061_, lean_object* v_act_1062_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1063_ = l_Lean_KVMap_instValueBool;
v___x_1064_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1065_ = l_Lean_Option_get___redArg(v___x_1063_, v_opts_1061_, v___x_1064_);
v___x_1066_ = lean_unbox(v___x_1065_);
lean_dec(v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v_toApplicative_1067_; lean_object* v_toBind_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___f_1071_; lean_object* v___x_1072_; 
v_toApplicative_1067_ = lean_ctor_get(v_inst_1059_, 0);
lean_inc_ref(v_toApplicative_1067_);
v_toBind_1068_ = lean_ctor_get(v_inst_1059_, 1);
lean_inc_n(v_toBind_1068_, 2);
lean_dec_ref(v_inst_1059_);
v___x_1069_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1070_ = lean_apply_2(v_inst_1060_, lean_box(0), v___x_1069_);
lean_inc(v___x_1070_);
v___f_1071_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1071_, 0, v_toApplicative_1067_);
lean_closure_set(v___f_1071_, 1, v_toBind_1068_);
lean_closure_set(v___f_1071_, 2, v___x_1070_);
lean_closure_set(v___f_1071_, 3, v_act_1062_);
v___x_1072_ = lean_apply_4(v_toBind_1068_, lean_box(0), lean_box(0), v___x_1070_, v___f_1071_);
return v___x_1072_;
}
else
{
lean_object* v_toApplicative_1073_; lean_object* v_toBind_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; 
v_toApplicative_1073_ = lean_ctor_get(v_inst_1059_, 0);
lean_inc_ref(v_toApplicative_1073_);
v_toBind_1074_ = lean_ctor_get(v_inst_1059_, 1);
lean_inc_n(v_toBind_1074_, 2);
lean_dec_ref(v_inst_1059_);
v___x_1075_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1076_ = lean_apply_2(v_inst_1060_, lean_box(0), v___x_1075_);
lean_inc(v___x_1076_);
v___f_1077_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1077_, 0, v_toApplicative_1073_);
lean_closure_set(v___f_1077_, 1, v_toBind_1074_);
lean_closure_set(v___f_1077_, 2, v___x_1076_);
lean_closure_set(v___f_1077_, 3, v_act_1062_);
v___x_1078_ = lean_apply_4(v_toBind_1074_, lean_box(0), lean_box(0), v___x_1076_, v___f_1077_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_opts_1081_, lean_object* v_act_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(v_inst_1079_, v_inst_1080_, v_opts_1081_, v_act_1082_);
lean_dec_ref(v_opts_1081_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object* v_00_u03b1_1084_, lean_object* v_m_1085_, lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v_opts_1088_, lean_object* v_act_1089_){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1090_ = l_Lean_KVMap_instValueBool;
v___x_1091_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1092_ = l_Lean_Option_get___redArg(v___x_1090_, v_opts_1088_, v___x_1091_);
v___x_1093_ = lean_unbox(v___x_1092_);
lean_dec(v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v_toApplicative_1094_; lean_object* v_toBind_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___f_1098_; lean_object* v___x_1099_; 
v_toApplicative_1094_ = lean_ctor_get(v_inst_1086_, 0);
lean_inc_ref(v_toApplicative_1094_);
v_toBind_1095_ = lean_ctor_get(v_inst_1086_, 1);
lean_inc_n(v_toBind_1095_, 2);
lean_dec_ref(v_inst_1086_);
v___x_1096_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1097_ = lean_apply_2(v_inst_1087_, lean_box(0), v___x_1096_);
lean_inc(v___x_1097_);
v___f_1098_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1098_, 0, v_toApplicative_1094_);
lean_closure_set(v___f_1098_, 1, v_toBind_1095_);
lean_closure_set(v___f_1098_, 2, v___x_1097_);
lean_closure_set(v___f_1098_, 3, v_act_1089_);
v___x_1099_ = lean_apply_4(v_toBind_1095_, lean_box(0), lean_box(0), v___x_1097_, v___f_1098_);
return v___x_1099_;
}
else
{
lean_object* v_toApplicative_1100_; lean_object* v_toBind_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; 
v_toApplicative_1100_ = lean_ctor_get(v_inst_1086_, 0);
lean_inc_ref(v_toApplicative_1100_);
v_toBind_1101_ = lean_ctor_get(v_inst_1086_, 1);
lean_inc_n(v_toBind_1101_, 2);
lean_dec_ref(v_inst_1086_);
v___x_1102_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1103_ = lean_apply_2(v_inst_1087_, lean_box(0), v___x_1102_);
lean_inc(v___x_1103_);
v___f_1104_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1104_, 0, v_toApplicative_1100_);
lean_closure_set(v___f_1104_, 1, v_toBind_1101_);
lean_closure_set(v___f_1104_, 2, v___x_1103_);
lean_closure_set(v___f_1104_, 3, v_act_1089_);
v___x_1105_ = lean_apply_4(v_toBind_1101_, lean_box(0), lean_box(0), v___x_1103_, v___f_1104_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object* v_00_u03b1_1106_, lean_object* v_m_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_opts_1110_, lean_object* v_act_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(v_00_u03b1_1106_, v_m_1107_, v_inst_1108_, v_inst_1109_, v_opts_1110_, v_act_1111_);
lean_dec_ref(v_opts_1110_);
return v_res_1112_;
}
}
static double _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0(void){
_start:
{
lean_object* v___x_1113_; double v___x_1114_; 
v___x_1113_ = lean_unsigned_to_nat(1000u);
v___x_1114_ = lean_float_of_nat(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object* v_o_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1116_ = l_Lean_KVMap_instValueBool;
v___x_1117_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1118_ = l_Lean_Option_get___redArg(v___x_1116_, v_o_1115_, v___x_1117_);
v___x_1119_ = lean_unbox(v___x_1118_);
lean_dec(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; double v___x_1123_; double v___x_1124_; double v___x_1125_; 
v___x_1120_ = l_Lean_KVMap_instValueNat;
v___x_1121_ = l_Lean_trace_profiler_threshold;
v___x_1122_ = l_Lean_Option_get___redArg(v___x_1120_, v_o_1115_, v___x_1121_);
v___x_1123_ = lean_float_of_nat(v___x_1122_);
v___x_1124_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1125_ = lean_float_div(v___x_1123_, v___x_1124_);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; double v___x_1129_; 
v___x_1126_ = l_Lean_KVMap_instValueNat;
v___x_1127_ = l_Lean_trace_profiler_threshold;
v___x_1128_ = l_Lean_Option_get___redArg(v___x_1126_, v_o_1115_, v___x_1127_);
v___x_1129_ = lean_float_of_nat(v___x_1128_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object* v_o_1130_){
_start:
{
double v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1130_);
lean_dec_ref(v_o_1130_);
v_r_1132_ = lean_box_float(v_res_1131_);
return v_r_1132_;
}
}
static lean_object* _init_l_Lean_instMonadAlwaysExceptEIO___closed__0(void){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object* v_00_u03b5_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___closed__0, &l_Lean_instMonadAlwaysExceptEIO___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___closed__0);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object* v_inst_1136_, lean_object* v_always_1137_){
_start:
{
lean_object* v___f_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; 
lean_inc_ref(v_always_1137_);
v___f_1138_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1138_, 0, v_always_1137_);
lean_closure_set(v___f_1138_, 1, v_inst_1136_);
v___f_1139_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_1139_, 0, v_always_1137_);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___f_1138_);
lean_ctor_set(v___x_1140_, 1, v___f_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object* v_m_1141_, lean_object* v_inst_1142_, lean_object* v_00_u03b5_1143_, lean_object* v_00_u03c3_1144_, lean_object* v_always_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_1142_, v_always_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object* v_always_1147_){
_start:
{
lean_object* v___f_1148_; lean_object* v___f_1149_; lean_object* v___x_1150_; 
lean_inc_ref(v_always_1147_);
v___f_1148_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1148_, 0, v_always_1147_);
v___f_1149_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1149_, 0, v_always_1147_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___f_1148_);
lean_ctor_set(v___x_1150_, 1, v___f_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object* v_m_1151_, lean_object* v_00_u03b5_1152_, lean_object* v_00_u03c9_1153_, lean_object* v_00_u03c3_1154_, lean_object* v_always_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object* v_always_1157_){
_start:
{
lean_object* v___f_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; 
lean_inc_ref(v_always_1157_);
v___f_1158_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1158_, 0, v_always_1157_);
v___f_1159_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1159_, 0, v_always_1157_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___f_1158_);
lean_ctor_set(v___x_1160_, 1, v___f_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object* v_m_1161_, lean_object* v_00_u03b5_1162_, lean_object* v_00_u03c1_1163_, lean_object* v_always_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object* v_always_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1167_, v_inst_1168_, v_inst_1169_, v_always_1166_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object* v_00_u03b1_1171_, lean_object* v_m_1172_, lean_object* v_00_u03b5_1173_, lean_object* v_00_u03c9_1174_, lean_object* v_00_u03b2_1175_, lean_object* v_always_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1177_, v_inst_1178_, v_inst_1179_, v_always_1176_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t v_x_1187_){
_start:
{
switch(v_x_1187_)
{
case 0:
{
lean_object* v___x_1188_; 
v___x_1188_ = ((lean_object*)(l_Lean_checkEmoji___closed__0));
return v___x_1188_;
}
case 1:
{
lean_object* v___x_1189_; 
v___x_1189_ = ((lean_object*)(l_Lean_crossEmoji___closed__0));
return v___x_1189_;
}
default: 
{
lean_object* v___x_1190_; 
v___x_1190_ = ((lean_object*)(l_Lean_bombEmoji___closed__0));
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object* v_x_1191_){
_start:
{
uint8_t v_x_31__boxed_1192_; lean_object* v_res_1193_; 
v_x_31__boxed_1192_ = lean_unbox(v_x_1191_);
v_res_1193_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_1192_);
return v_res_1193_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___lam__0(lean_object* v_x_1194_){
_start:
{
if (lean_obj_tag(v_x_1194_) == 0)
{
uint8_t v___x_1195_; 
v___x_1195_ = 2;
return v___x_1195_;
}
else
{
lean_object* v_a_1196_; uint8_t v___x_1197_; 
v_a_1196_ = lean_ctor_get(v_x_1194_, 0);
v___x_1197_ = lean_unbox(v_a_1196_);
if (v___x_1197_ == 0)
{
uint8_t v___x_1198_; 
v___x_1198_ = 1;
return v___x_1198_;
}
else
{
uint8_t v___x_1199_; 
v___x_1199_ = 0;
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object* v_x_1200_){
_start:
{
uint8_t v_res_1201_; lean_object* v_r_1202_; 
v_res_1201_ = l_Lean_instExceptToTraceResultBool___lam__0(v_x_1200_);
lean_dec_ref(v_x_1200_);
v_r_1202_ = lean_box(v_res_1201_);
return v_r_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object* v_00_u03b5_1204_){
_start:
{
lean_object* v___f_1205_; 
v___f_1205_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___closed__0));
return v___f_1205_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___lam__0(lean_object* v_x_1206_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 0)
{
uint8_t v___x_1207_; 
v___x_1207_ = 2;
return v___x_1207_;
}
else
{
lean_object* v_a_1208_; 
v_a_1208_ = lean_ctor_get(v_x_1206_, 0);
if (lean_obj_tag(v_a_1208_) == 0)
{
uint8_t v___x_1209_; 
v___x_1209_ = 1;
return v___x_1209_;
}
else
{
uint8_t v___x_1210_; 
v___x_1210_ = 0;
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object* v_x_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l_Lean_instExceptToTraceResultOption___lam__0(v_x_1211_);
lean_dec_ref(v_x_1211_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object* v_00_u03b1_1215_, lean_object* v_00_u03b5_1216_){
_start:
{
lean_object* v___f_1217_; 
v___f_1217_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___closed__0));
return v___f_1217_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object* v_x_1218_){
_start:
{
if (lean_obj_tag(v_x_1218_) == 0)
{
uint8_t v___x_1219_; 
v___x_1219_ = 2;
return v___x_1219_;
}
else
{
uint8_t v___x_1220_; 
v___x_1220_ = 0;
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object* v_x_1221_){
_start:
{
uint8_t v_res_1222_; lean_object* v_r_1223_; 
v_res_1222_ = l_Lean_instExceptToTraceResult___lam__0(v_x_1221_);
lean_dec_ref(v_x_1221_);
v_r_1223_ = lean_box(v_res_1222_);
return v_r_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object* v_00_u03b1_1225_, lean_object* v_00_u03b5_1226_){
_start:
{
lean_object* v___f_1227_; 
v___f_1227_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
return v___f_1227_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___redArg(lean_object* v_inst_1228_, lean_object* v_e_1229_){
_start:
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = lean_apply_1(v_inst_1228_, v_e_1229_);
v___x_1231_ = lean_unbox(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___redArg___boxed(lean_object* v_inst_1232_, lean_object* v_e_1233_){
_start:
{
uint8_t v_res_1234_; lean_object* v_r_1235_; 
v_res_1234_ = l_Except_toTraceResult___redArg(v_inst_1232_, v_e_1233_);
v_r_1235_ = lean_box(v_res_1234_);
return v_r_1235_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult(lean_object* v_00_u03b1_1236_, lean_object* v_00_u03b5_1237_, lean_object* v_inst_1238_, lean_object* v_e_1239_){
_start:
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = lean_apply_1(v_inst_1238_, v_e_1239_);
v___x_1241_ = lean_unbox(v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___boxed(lean_object* v_00_u03b1_1242_, lean_object* v_00_u03b5_1243_, lean_object* v_inst_1244_, lean_object* v_e_1245_){
_start:
{
uint8_t v_res_1246_; lean_object* v_r_1247_; 
v_res_1246_ = l_Except_toTraceResult(v_00_u03b1_1242_, v_00_u03b5_1243_, v_inst_1244_, v_e_1245_);
v_r_1247_ = lean_box(v_res_1246_);
return v_r_1247_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0));
v___x_1250_ = l_Lean_stringToMessageData(v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object* v_inst_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v_toApplicative_1253_; lean_object* v_toPure_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_toApplicative_1253_ = lean_ctor_get(v_inst_1251_, 0);
lean_inc_ref(v_toApplicative_1253_);
lean_dec_ref(v_inst_1251_);
v_toPure_1254_ = lean_ctor_get(v_toApplicative_1253_, 1);
lean_inc(v_toPure_1254_);
lean_dec_ref(v_toApplicative_1253_);
v___x_1255_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1);
v___x_1256_ = lean_apply_2(v_toPure_1254_, lean_box(0), v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(lean_object* v_inst_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(v_inst_1257_, v_x_1258_);
lean_dec(v_x_1258_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object* v_oldTraces_1260_, lean_object* v_s_1261_){
_start:
{
uint64_t v_tid_1262_; lean_object* v_traces_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_tid_1262_ = lean_ctor_get_uint64(v_s_1261_, sizeof(void*)*1);
v_traces_1263_ = lean_ctor_get(v_s_1261_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_s_1261_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v_s_1261_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_traces_1263_);
lean_dec(v_s_1261_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1260_, v_traces_1263_);
lean_dec_ref(v_traces_1263_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1267_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
lean_ctor_set_uint64(v_reuseFailAlloc_1270_, sizeof(void*)*1, v_tid_1262_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object* v_always_1272_, lean_object* v_inst_1273_, lean_object* v_fst_1274_, lean_object* v_____r_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1272_);
v___x_1277_ = l_MonadExcept_ofExcept___redArg(v_inst_1273_, v___x_1276_, v_fst_1274_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object* v_inst_1278_, lean_object* v___x_1279_, lean_object* v_fst_1280_, lean_object* v_____r_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_MonadExcept_ofExcept___redArg(v_inst_1278_, v___x_1279_, v_fst_1280_);
return v___x_1282_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object* v_inst_1286_, lean_object* v_fst_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_oldTraces_1292_, lean_object* v_ref_1293_, lean_object* v_toBind_1294_, lean_object* v___f_1295_, lean_object* v_cls_1296_, uint8_t v_collapsed_1297_, lean_object* v_tag_1298_, uint8_t v___x_1299_, double v_fst_1300_, double v_snd_1301_, lean_object* v_m_1302_){
_start:
{
lean_object* v_result_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v_m_1309_; lean_object* v_data_1311_; lean_object* v___x_1314_; double v___x_1315_; lean_object* v_data_1316_; 
v_result_1303_ = lean_apply_1(v_inst_1286_, v_fst_1287_);
v___x_1304_ = lean_unbox(v_result_1303_);
v___x_1305_ = l_Lean_TraceResult_toEmoji(v___x_1304_);
v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
v___x_1307_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v_m_1309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_m_1309_, 0, v___x_1308_);
lean_ctor_set(v_m_1309_, 1, v_m_1302_);
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_result_1303_);
v___x_1315_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_1298_);
lean_inc_ref(v___x_1314_);
lean_inc(v_cls_1296_);
v_data_1316_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1316_, 0, v_cls_1296_);
lean_ctor_set(v_data_1316_, 1, v___x_1314_);
lean_ctor_set(v_data_1316_, 2, v_tag_1298_);
lean_ctor_set_float(v_data_1316_, sizeof(void*)*3, v___x_1315_);
lean_ctor_set_float(v_data_1316_, sizeof(void*)*3 + 8, v___x_1315_);
lean_ctor_set_uint8(v_data_1316_, sizeof(void*)*3 + 16, v_collapsed_1297_);
if (v___x_1299_ == 0)
{
lean_dec_ref(v___x_1314_);
lean_dec_ref(v_tag_1298_);
lean_dec(v_cls_1296_);
v_data_1311_ = v_data_1316_;
goto v___jp_1310_;
}
else
{
lean_object* v_data_1317_; 
lean_dec_ref(v_data_1316_);
v_data_1317_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1317_, 0, v_cls_1296_);
lean_ctor_set(v_data_1317_, 1, v___x_1314_);
lean_ctor_set(v_data_1317_, 2, v_tag_1298_);
lean_ctor_set_float(v_data_1317_, sizeof(void*)*3, v_fst_1300_);
lean_ctor_set_float(v_data_1317_, sizeof(void*)*3 + 8, v_snd_1301_);
lean_ctor_set_uint8(v_data_1317_, sizeof(void*)*3 + 16, v_collapsed_1297_);
v_data_1311_ = v_data_1317_;
goto v___jp_1310_;
}
v___jp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_1288_, v_inst_1289_, v_inst_1290_, v_inst_1291_, v_oldTraces_1292_, v_data_1311_, v_ref_1293_, v_m_1309_);
v___x_1313_ = lean_apply_4(v_toBind_1294_, lean_box(0), lean_box(0), v___x_1312_, v___f_1295_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_1318_ = _args[0];
lean_object* v_fst_1319_ = _args[1];
lean_object* v_inst_1320_ = _args[2];
lean_object* v_inst_1321_ = _args[3];
lean_object* v_inst_1322_ = _args[4];
lean_object* v_inst_1323_ = _args[5];
lean_object* v_oldTraces_1324_ = _args[6];
lean_object* v_ref_1325_ = _args[7];
lean_object* v_toBind_1326_ = _args[8];
lean_object* v___f_1327_ = _args[9];
lean_object* v_cls_1328_ = _args[10];
lean_object* v_collapsed_1329_ = _args[11];
lean_object* v_tag_1330_ = _args[12];
lean_object* v___x_1331_ = _args[13];
lean_object* v_fst_1332_ = _args[14];
lean_object* v_snd_1333_ = _args[15];
lean_object* v_m_1334_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1335_; uint8_t v___x_676__boxed_1336_; double v_fst_677__boxed_1337_; double v_snd_678__boxed_1338_; lean_object* v_res_1339_; 
v_collapsed_boxed_1335_ = lean_unbox(v_collapsed_1329_);
v___x_676__boxed_1336_ = lean_unbox(v___x_1331_);
v_fst_677__boxed_1337_ = lean_unbox_float(v_fst_1332_);
lean_dec_ref(v_fst_1332_);
v_snd_678__boxed_1338_ = lean_unbox_float(v_snd_1333_);
lean_dec_ref(v_snd_1333_);
v_res_1339_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1318_, v_fst_1319_, v_inst_1320_, v_inst_1321_, v_inst_1322_, v_inst_1323_, v_oldTraces_1324_, v_ref_1325_, v_toBind_1326_, v___f_1327_, v_cls_1328_, v_collapsed_boxed_1335_, v_tag_1330_, v___x_676__boxed_1336_, v_fst_677__boxed_1337_, v_snd_678__boxed_1338_, v_m_1334_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(lean_object* v_always_1340_, lean_object* v_inst_1341_, lean_object* v_fst_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_oldTraces_1347_, lean_object* v_toBind_1348_, lean_object* v_cls_1349_, uint8_t v_collapsed_1350_, lean_object* v_tag_1351_, uint8_t v___x_1352_, double v_fst_1353_, double v_snd_1354_, lean_object* v_msg_1355_, lean_object* v___f_1356_, lean_object* v_ref_1357_){
_start:
{
lean_object* v___x_1358_; lean_object* v_tryCatch_1359_; lean_object* v___f_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___f_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_inc_ref(v_always_1340_);
v___x_1358_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1340_);
v_tryCatch_1359_ = lean_ctor_get(v_always_1340_, 1);
lean_inc(v_tryCatch_1359_);
lean_dec_ref(v_always_1340_);
lean_inc_ref_n(v_fst_1342_, 2);
lean_inc_ref(v_inst_1341_);
v___f_1360_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1360_, 0, v_inst_1341_);
lean_closure_set(v___f_1360_, 1, v___x_1358_);
lean_closure_set(v___f_1360_, 2, v_fst_1342_);
v___x_1361_ = lean_box(v_collapsed_1350_);
v___x_1362_ = lean_box(v___x_1352_);
v___x_1363_ = lean_box_float(v_fst_1353_);
v___x_1364_ = lean_box_float(v_snd_1354_);
lean_inc(v_toBind_1348_);
v___f_1365_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1365_, 0, v_inst_1343_);
lean_closure_set(v___f_1365_, 1, v_fst_1342_);
lean_closure_set(v___f_1365_, 2, v_inst_1341_);
lean_closure_set(v___f_1365_, 3, v_inst_1344_);
lean_closure_set(v___f_1365_, 4, v_inst_1345_);
lean_closure_set(v___f_1365_, 5, v_inst_1346_);
lean_closure_set(v___f_1365_, 6, v_oldTraces_1347_);
lean_closure_set(v___f_1365_, 7, v_ref_1357_);
lean_closure_set(v___f_1365_, 8, v_toBind_1348_);
lean_closure_set(v___f_1365_, 9, v___f_1360_);
lean_closure_set(v___f_1365_, 10, v_cls_1349_);
lean_closure_set(v___f_1365_, 11, v___x_1361_);
lean_closure_set(v___f_1365_, 12, v_tag_1351_);
lean_closure_set(v___f_1365_, 13, v___x_1362_);
lean_closure_set(v___f_1365_, 14, v___x_1363_);
lean_closure_set(v___f_1365_, 15, v___x_1364_);
v___x_1366_ = lean_apply_1(v_msg_1355_, v_fst_1342_);
v___x_1367_ = lean_apply_3(v_tryCatch_1359_, lean_box(0), v___x_1366_, v___f_1356_);
v___x_1368_ = lean_apply_4(v_toBind_1348_, lean_box(0), lean_box(0), v___x_1367_, v___f_1365_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_always_1369_ = _args[0];
lean_object* v_inst_1370_ = _args[1];
lean_object* v_fst_1371_ = _args[2];
lean_object* v_inst_1372_ = _args[3];
lean_object* v_inst_1373_ = _args[4];
lean_object* v_inst_1374_ = _args[5];
lean_object* v_inst_1375_ = _args[6];
lean_object* v_oldTraces_1376_ = _args[7];
lean_object* v_toBind_1377_ = _args[8];
lean_object* v_cls_1378_ = _args[9];
lean_object* v_collapsed_1379_ = _args[10];
lean_object* v_tag_1380_ = _args[11];
lean_object* v___x_1381_ = _args[12];
lean_object* v_fst_1382_ = _args[13];
lean_object* v_snd_1383_ = _args[14];
lean_object* v_msg_1384_ = _args[15];
lean_object* v___f_1385_ = _args[16];
lean_object* v_ref_1386_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_1387_; uint8_t v___x_728__boxed_1388_; double v_fst_729__boxed_1389_; double v_snd_730__boxed_1390_; lean_object* v_res_1391_; 
v_collapsed_boxed_1387_ = lean_unbox(v_collapsed_1379_);
v___x_728__boxed_1388_ = lean_unbox(v___x_1381_);
v_fst_729__boxed_1389_ = lean_unbox_float(v_fst_1382_);
lean_dec_ref(v_fst_1382_);
v_snd_730__boxed_1390_ = lean_unbox_float(v_snd_1383_);
lean_dec_ref(v_snd_1383_);
v_res_1391_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(v_always_1369_, v_inst_1370_, v_fst_1371_, v_inst_1372_, v_inst_1373_, v_inst_1374_, v_inst_1375_, v_oldTraces_1376_, v_toBind_1377_, v_cls_1378_, v_collapsed_boxed_1387_, v_tag_1380_, v___x_728__boxed_1388_, v_fst_729__boxed_1389_, v_snd_730__boxed_1390_, v_msg_1384_, v___f_1385_, v_ref_1386_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v_always_1396_, lean_object* v_inst_1397_, lean_object* v_cls_1398_, uint8_t v_collapsed_1399_, lean_object* v_tag_1400_, lean_object* v_opts_1401_, uint8_t v_clsEnabled_1402_, lean_object* v_oldTraces_1403_, lean_object* v_msg_1404_, lean_object* v_resStartStop_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v_snd_1407_; lean_object* v_fst_1408_; lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v___f_1411_; lean_object* v___f_1412_; lean_object* v___f_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___y_1423_; double v___y_1429_; uint8_t v___x_1434_; 
v___x_1406_ = l_Lean_KVMap_instValueBool;
v_snd_1407_ = lean_ctor_get(v_resStartStop_1405_, 1);
lean_inc(v_snd_1407_);
v_fst_1408_ = lean_ctor_get(v_resStartStop_1405_, 0);
lean_inc_n(v_fst_1408_, 2);
lean_dec_ref(v_resStartStop_1405_);
v_fst_1409_ = lean_ctor_get(v_snd_1407_, 0);
lean_inc(v_fst_1409_);
v_snd_1410_ = lean_ctor_get(v_snd_1407_, 1);
lean_inc(v_snd_1410_);
lean_dec(v_snd_1407_);
lean_inc_ref_n(v_inst_1392_, 2);
v___f_1411_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1411_, 0, v_inst_1392_);
lean_inc_ref(v_oldTraces_1403_);
v___f_1412_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1412_, 0, v_oldTraces_1403_);
lean_inc_ref(v_always_1396_);
v___f_1413_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1413_, 0, v_always_1396_);
lean_closure_set(v___f_1413_, 1, v_inst_1392_);
lean_closure_set(v___f_1413_, 2, v_fst_1408_);
v___x_1414_ = l_Lean_trace_profiler;
v___x_1415_ = l_Lean_Option_get___redArg(v___x_1406_, v_opts_1401_, v___x_1414_);
v___x_1434_ = lean_unbox(v___x_1415_);
if (v___x_1434_ == 0)
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_unbox(v___x_1415_);
v___y_1423_ = v___x_1435_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1436_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1437_ = l_Lean_Option_get___redArg(v___x_1406_, v_opts_1401_, v___x_1436_);
v___x_1438_ = lean_unbox(v___x_1437_);
lean_dec(v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; double v___x_1442_; double v___x_1443_; double v___x_1444_; 
v___x_1439_ = l_Lean_KVMap_instValueNat;
v___x_1440_ = l_Lean_trace_profiler_threshold;
v___x_1441_ = l_Lean_Option_get___redArg(v___x_1439_, v_opts_1401_, v___x_1440_);
v___x_1442_ = lean_float_of_nat(v___x_1441_);
v___x_1443_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1444_ = lean_float_div(v___x_1442_, v___x_1443_);
v___y_1429_ = v___x_1444_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; double v___x_1448_; 
v___x_1445_ = l_Lean_KVMap_instValueNat;
v___x_1446_ = l_Lean_trace_profiler_threshold;
v___x_1447_ = l_Lean_Option_get___redArg(v___x_1445_, v_opts_1401_, v___x_1446_);
v___x_1448_ = lean_float_of_nat(v___x_1447_);
v___y_1429_ = v___x_1448_;
goto v___jp_1428_;
}
}
v___jp_1416_:
{
lean_object* v_toBind_1417_; lean_object* v_getRef_1418_; lean_object* v___x_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; 
v_toBind_1417_ = lean_ctor_get(v_inst_1392_, 1);
lean_inc_n(v_toBind_1417_, 2);
v_getRef_1418_ = lean_ctor_get(v_inst_1394_, 0);
lean_inc(v_getRef_1418_);
v___x_1419_ = lean_box(v_collapsed_1399_);
v___f_1420_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed), 18, 17);
lean_closure_set(v___f_1420_, 0, v_always_1396_);
lean_closure_set(v___f_1420_, 1, v_inst_1392_);
lean_closure_set(v___f_1420_, 2, v_fst_1408_);
lean_closure_set(v___f_1420_, 3, v_inst_1397_);
lean_closure_set(v___f_1420_, 4, v_inst_1393_);
lean_closure_set(v___f_1420_, 5, v_inst_1394_);
lean_closure_set(v___f_1420_, 6, v_inst_1395_);
lean_closure_set(v___f_1420_, 7, v_oldTraces_1403_);
lean_closure_set(v___f_1420_, 8, v_toBind_1417_);
lean_closure_set(v___f_1420_, 9, v_cls_1398_);
lean_closure_set(v___f_1420_, 10, v___x_1419_);
lean_closure_set(v___f_1420_, 11, v_tag_1400_);
lean_closure_set(v___f_1420_, 12, v___x_1415_);
lean_closure_set(v___f_1420_, 13, v_fst_1409_);
lean_closure_set(v___f_1420_, 14, v_snd_1410_);
lean_closure_set(v___f_1420_, 15, v_msg_1404_);
lean_closure_set(v___f_1420_, 16, v___f_1411_);
v___x_1421_ = lean_apply_4(v_toBind_1417_, lean_box(0), lean_box(0), v_getRef_1418_, v___f_1420_);
return v___x_1421_;
}
v___jp_1422_:
{
if (v_clsEnabled_1402_ == 0)
{
if (v___y_1423_ == 0)
{
lean_object* v_toBind_1424_; lean_object* v_modifyTraceState_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec(v___x_1415_);
lean_dec_ref(v___f_1411_);
lean_dec(v_snd_1410_);
lean_dec(v_fst_1409_);
lean_dec(v_fst_1408_);
lean_dec(v_msg_1404_);
lean_dec_ref(v_oldTraces_1403_);
lean_dec_ref(v_tag_1400_);
lean_dec(v_cls_1398_);
lean_dec_ref(v_inst_1397_);
lean_dec_ref(v_always_1396_);
lean_dec(v_inst_1395_);
lean_dec_ref(v_inst_1394_);
v_toBind_1424_ = lean_ctor_get(v_inst_1392_, 1);
lean_inc(v_toBind_1424_);
lean_dec_ref(v_inst_1392_);
v_modifyTraceState_1425_ = lean_ctor_get(v_inst_1393_, 0);
lean_inc(v_modifyTraceState_1425_);
lean_dec_ref(v_inst_1393_);
v___x_1426_ = lean_apply_1(v_modifyTraceState_1425_, v___f_1412_);
v___x_1427_ = lean_apply_4(v_toBind_1424_, lean_box(0), lean_box(0), v___x_1426_, v___f_1413_);
return v___x_1427_;
}
else
{
lean_dec_ref(v___f_1413_);
lean_dec_ref(v___f_1412_);
goto v___jp_1416_;
}
}
else
{
lean_dec_ref(v___f_1413_);
lean_dec_ref(v___f_1412_);
goto v___jp_1416_;
}
}
v___jp_1428_:
{
double v___x_1430_; double v___x_1431_; double v___x_1432_; uint8_t v___x_1433_; 
v___x_1430_ = lean_unbox_float(v_snd_1410_);
v___x_1431_ = lean_unbox_float(v_fst_1409_);
v___x_1432_ = lean_float_sub(v___x_1430_, v___x_1431_);
v___x_1433_ = lean_float_decLt(v___y_1429_, v___x_1432_);
v___y_1423_ = v___x_1433_;
goto v___jp_1422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object* v_inst_1449_, lean_object* v_inst_1450_, lean_object* v_inst_1451_, lean_object* v_inst_1452_, lean_object* v_always_1453_, lean_object* v_inst_1454_, lean_object* v_cls_1455_, lean_object* v_collapsed_1456_, lean_object* v_tag_1457_, lean_object* v_opts_1458_, lean_object* v_clsEnabled_1459_, lean_object* v_oldTraces_1460_, lean_object* v_msg_1461_, lean_object* v_resStartStop_1462_){
_start:
{
uint8_t v_collapsed_boxed_1463_; uint8_t v_clsEnabled_boxed_1464_; lean_object* v_res_1465_; 
v_collapsed_boxed_1463_ = lean_unbox(v_collapsed_1456_);
v_clsEnabled_boxed_1464_ = lean_unbox(v_clsEnabled_1459_);
v_res_1465_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1449_, v_inst_1450_, v_inst_1451_, v_inst_1452_, v_always_1453_, v_inst_1454_, v_cls_1455_, v_collapsed_boxed_1463_, v_tag_1457_, v_opts_1458_, v_clsEnabled_boxed_1464_, v_oldTraces_1460_, v_msg_1461_, v_resStartStop_1462_);
lean_dec_ref(v_opts_1458_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object* v_00_u03b1_1466_, lean_object* v_m_1467_, lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_00_u03b5_1472_, lean_object* v_always_1473_, lean_object* v_inst_1474_, lean_object* v_cls_1475_, uint8_t v_collapsed_1476_, lean_object* v_tag_1477_, lean_object* v_opts_1478_, uint8_t v_clsEnabled_1479_, lean_object* v_oldTraces_1480_, lean_object* v_msg_1481_, lean_object* v_resStartStop_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1468_, v_inst_1469_, v_inst_1470_, v_inst_1471_, v_always_1473_, v_inst_1474_, v_cls_1475_, v_collapsed_1476_, v_tag_1477_, v_opts_1478_, v_clsEnabled_1479_, v_oldTraces_1480_, v_msg_1481_, v_resStartStop_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_1484_ = _args[0];
lean_object* v_m_1485_ = _args[1];
lean_object* v_inst_1486_ = _args[2];
lean_object* v_inst_1487_ = _args[3];
lean_object* v_inst_1488_ = _args[4];
lean_object* v_inst_1489_ = _args[5];
lean_object* v_00_u03b5_1490_ = _args[6];
lean_object* v_always_1491_ = _args[7];
lean_object* v_inst_1492_ = _args[8];
lean_object* v_cls_1493_ = _args[9];
lean_object* v_collapsed_1494_ = _args[10];
lean_object* v_tag_1495_ = _args[11];
lean_object* v_opts_1496_ = _args[12];
lean_object* v_clsEnabled_1497_ = _args[13];
lean_object* v_oldTraces_1498_ = _args[14];
lean_object* v_msg_1499_ = _args[15];
lean_object* v_resStartStop_1500_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1501_; uint8_t v_clsEnabled_boxed_1502_; lean_object* v_res_1503_; 
v_collapsed_boxed_1501_ = lean_unbox(v_collapsed_1494_);
v_clsEnabled_boxed_1502_ = lean_unbox(v_clsEnabled_1497_);
v_res_1503_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(v_00_u03b1_1484_, v_m_1485_, v_inst_1486_, v_inst_1487_, v_inst_1488_, v_inst_1489_, v_00_u03b5_1490_, v_always_1491_, v_inst_1492_, v_cls_1493_, v_collapsed_boxed_1501_, v_tag_1495_, v_opts_1496_, v_clsEnabled_boxed_1502_, v_oldTraces_1498_, v_msg_1499_, v_resStartStop_1500_);
lean_dec_ref(v_opts_1496_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_always_1508_, lean_object* v_inst_1509_, lean_object* v_cls_1510_, uint8_t v_collapsed_1511_, lean_object* v_tag_1512_, lean_object* v_opts_1513_, uint8_t v_clsEnabled_1514_, lean_object* v_oldTraces_1515_, lean_object* v_msg_1516_, lean_object* v_resStartStop_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1504_, v_inst_1505_, v_inst_1506_, v_inst_1507_, v_always_1508_, v_inst_1509_, v_cls_1510_, v_collapsed_1511_, v_tag_1512_, v_opts_1513_, v_clsEnabled_1514_, v_oldTraces_1515_, v_msg_1516_, v_resStartStop_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_always_1523_, lean_object* v_inst_1524_, lean_object* v_cls_1525_, lean_object* v_collapsed_1526_, lean_object* v_tag_1527_, lean_object* v_opts_1528_, lean_object* v_clsEnabled_1529_, lean_object* v_oldTraces_1530_, lean_object* v_msg_1531_, lean_object* v_resStartStop_1532_){
_start:
{
uint8_t v_collapsed_boxed_1533_; uint8_t v_clsEnabled_boxed_1534_; lean_object* v_res_1535_; 
v_collapsed_boxed_1533_ = lean_unbox(v_collapsed_1526_);
v_clsEnabled_boxed_1534_ = lean_unbox(v_clsEnabled_1529_);
v_res_1535_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1519_, v_inst_1520_, v_inst_1521_, v_inst_1522_, v_always_1523_, v_inst_1524_, v_cls_1525_, v_collapsed_boxed_1533_, v_tag_1527_, v_opts_1528_, v_clsEnabled_boxed_1534_, v_oldTraces_1530_, v_msg_1531_, v_resStartStop_1532_);
lean_dec_ref(v_opts_1528_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object* v_toPure_1536_, lean_object* v_ex_1537_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_ex_1537_);
v___x_1539_ = lean_apply_2(v_toPure_1536_, lean_box(0), v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object* v_toPure_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_a_1541_);
v___x_1543_ = lean_apply_2(v_toPure_1540_, lean_box(0), v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object* v_start_1544_, lean_object* v_a_1545_, lean_object* v_toPure_1546_, lean_object* v_stop_1547_){
_start:
{
double v___x_1548_; double v___x_1549_; double v___x_1550_; double v___x_1551_; double v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1548_ = lean_float_of_nat(v_start_1544_);
v___x_1549_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1550_ = lean_float_div(v___x_1548_, v___x_1549_);
v___x_1551_ = lean_float_of_nat(v_stop_1547_);
v___x_1552_ = lean_float_div(v___x_1551_, v___x_1549_);
v___x_1553_ = lean_box_float(v___x_1550_);
v___x_1554_ = lean_box_float(v___x_1552_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_a_1545_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_apply_2(v_toPure_1546_, lean_box(0), v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object* v_start_1558_, lean_object* v_toPure_1559_, lean_object* v_toBind_1560_, lean_object* v___x_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v___f_1563_; lean_object* v___x_1564_; 
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1563_, 0, v_start_1558_);
lean_closure_set(v___f_1563_, 1, v_a_1562_);
lean_closure_set(v___f_1563_, 2, v_toPure_1559_);
v___x_1564_ = lean_apply_4(v_toBind_1560_, lean_box(0), lean_box(0), v___x_1561_, v___f_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object* v_toPure_1565_, lean_object* v_toBind_1566_, lean_object* v___x_1567_, lean_object* v___x_1568_, lean_object* v_start_1569_){
_start:
{
lean_object* v___f_1570_; lean_object* v___x_1571_; 
lean_inc(v_toBind_1566_);
v___f_1570_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1570_, 0, v_start_1569_);
lean_closure_set(v___f_1570_, 1, v_toPure_1565_);
lean_closure_set(v___f_1570_, 2, v_toBind_1566_);
lean_closure_set(v___f_1570_, 3, v___x_1567_);
v___x_1571_ = lean_apply_4(v_toBind_1566_, lean_box(0), lean_box(0), v___x_1568_, v___f_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object* v_start_1572_, lean_object* v_a_1573_, lean_object* v_toPure_1574_, lean_object* v_stop_1575_){
_start:
{
double v___x_1576_; double v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1576_ = lean_float_of_nat(v_start_1572_);
v___x_1577_ = lean_float_of_nat(v_stop_1575_);
v___x_1578_ = lean_box_float(v___x_1576_);
v___x_1579_ = lean_box_float(v___x_1577_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v_a_1573_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = lean_apply_2(v_toPure_1574_, lean_box(0), v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object* v_start_1583_, lean_object* v_toPure_1584_, lean_object* v_toBind_1585_, lean_object* v___x_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v___f_1588_; lean_object* v___x_1589_; 
v___f_1588_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__6), 4, 3);
lean_closure_set(v___f_1588_, 0, v_start_1583_);
lean_closure_set(v___f_1588_, 1, v_a_1587_);
lean_closure_set(v___f_1588_, 2, v_toPure_1584_);
v___x_1589_ = lean_apply_4(v_toBind_1585_, lean_box(0), lean_box(0), v___x_1586_, v___f_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object* v_toPure_1590_, lean_object* v_toBind_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v_start_1594_){
_start:
{
lean_object* v___f_1595_; lean_object* v___x_1596_; 
lean_inc(v_toBind_1591_);
v___f_1595_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1595_, 0, v_start_1594_);
lean_closure_set(v___f_1595_, 1, v_toPure_1590_);
lean_closure_set(v___f_1595_, 2, v_toBind_1591_);
lean_closure_set(v___f_1595_, 3, v___x_1592_);
v___x_1596_ = lean_apply_4(v_toBind_1591_, lean_box(0), lean_box(0), v___x_1593_, v___f_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object* v_always_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_inst_1602_, lean_object* v_cls_1603_, uint8_t v_collapsed_1604_, lean_object* v_tag_1605_, lean_object* v_opts_1606_, uint8_t v_clsEnabled_1607_, lean_object* v_msg_1608_, lean_object* v_toPure_1609_, lean_object* v_toBind_1610_, lean_object* v_k_1611_, lean_object* v_inst_1612_, lean_object* v_oldTraces_1613_){
_start:
{
lean_object* v_tryCatch_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___f_1617_; lean_object* v___f_1618_; lean_object* v___f_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_tryCatch_1614_ = lean_ctor_get(v_always_1597_, 1);
lean_inc(v_tryCatch_1614_);
v___x_1615_ = lean_box(v_collapsed_1604_);
v___x_1616_ = lean_box(v_clsEnabled_1607_);
lean_inc_ref(v_opts_1606_);
v___f_1617_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1617_, 0, v_inst_1598_);
lean_closure_set(v___f_1617_, 1, v_inst_1599_);
lean_closure_set(v___f_1617_, 2, v_inst_1600_);
lean_closure_set(v___f_1617_, 3, v_inst_1601_);
lean_closure_set(v___f_1617_, 4, v_always_1597_);
lean_closure_set(v___f_1617_, 5, v_inst_1602_);
lean_closure_set(v___f_1617_, 6, v_cls_1603_);
lean_closure_set(v___f_1617_, 7, v___x_1615_);
lean_closure_set(v___f_1617_, 8, v_tag_1605_);
lean_closure_set(v___f_1617_, 9, v_opts_1606_);
lean_closure_set(v___f_1617_, 10, v___x_1616_);
lean_closure_set(v___f_1617_, 11, v_oldTraces_1613_);
lean_closure_set(v___f_1617_, 12, v_msg_1608_);
lean_inc_n(v_toPure_1609_, 2);
v___f_1618_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1618_, 0, v_toPure_1609_);
v___f_1619_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1619_, 0, v_toPure_1609_);
lean_inc(v_toBind_1610_);
v___x_1620_ = lean_apply_4(v_toBind_1610_, lean_box(0), lean_box(0), v_k_1611_, v___f_1619_);
v___x_1621_ = lean_apply_3(v_tryCatch_1614_, lean_box(0), v___x_1620_, v___f_1618_);
v___x_1622_ = l_Lean_KVMap_instValueBool;
v___x_1623_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1624_ = l_Lean_Option_get___redArg(v___x_1622_, v_opts_1606_, v___x_1623_);
lean_dec_ref(v_opts_1606_);
v___x_1625_ = lean_unbox(v___x_1624_);
lean_dec(v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___f_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1626_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1627_ = lean_apply_2(v_inst_1612_, lean_box(0), v___x_1626_);
lean_inc(v___x_1627_);
lean_inc_n(v_toBind_1610_, 2);
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1628_, 0, v_toPure_1609_);
lean_closure_set(v___f_1628_, 1, v_toBind_1610_);
lean_closure_set(v___f_1628_, 2, v___x_1627_);
lean_closure_set(v___f_1628_, 3, v___x_1621_);
v___x_1629_ = lean_apply_4(v_toBind_1610_, lean_box(0), lean_box(0), v___x_1627_, v___f_1628_);
v___x_1630_ = lean_apply_4(v_toBind_1610_, lean_box(0), lean_box(0), v___x_1629_, v___f_1617_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___f_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1632_ = lean_apply_2(v_inst_1612_, lean_box(0), v___x_1631_);
lean_inc(v___x_1632_);
lean_inc_n(v_toBind_1610_, 2);
v___f_1633_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_1633_, 0, v_toPure_1609_);
lean_closure_set(v___f_1633_, 1, v_toBind_1610_);
lean_closure_set(v___f_1633_, 2, v___x_1632_);
lean_closure_set(v___f_1633_, 3, v___x_1621_);
v___x_1634_ = lean_apply_4(v_toBind_1610_, lean_box(0), lean_box(0), v___x_1632_, v___f_1633_);
v___x_1635_ = lean_apply_4(v_toBind_1610_, lean_box(0), lean_box(0), v___x_1634_, v___f_1617_);
return v___x_1635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_always_1636_ = _args[0];
lean_object* v_inst_1637_ = _args[1];
lean_object* v_inst_1638_ = _args[2];
lean_object* v_inst_1639_ = _args[3];
lean_object* v_inst_1640_ = _args[4];
lean_object* v_inst_1641_ = _args[5];
lean_object* v_cls_1642_ = _args[6];
lean_object* v_collapsed_1643_ = _args[7];
lean_object* v_tag_1644_ = _args[8];
lean_object* v_opts_1645_ = _args[9];
lean_object* v_clsEnabled_1646_ = _args[10];
lean_object* v_msg_1647_ = _args[11];
lean_object* v_toPure_1648_ = _args[12];
lean_object* v_toBind_1649_ = _args[13];
lean_object* v_k_1650_ = _args[14];
lean_object* v_inst_1651_ = _args[15];
lean_object* v_oldTraces_1652_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1653_; uint8_t v_clsEnabled_boxed_1654_; lean_object* v_res_1655_; 
v_collapsed_boxed_1653_ = lean_unbox(v_collapsed_1643_);
v_clsEnabled_boxed_1654_ = lean_unbox(v_clsEnabled_1646_);
v_res_1655_ = l_Lean_withTraceNode___redArg___lam__9(v_always_1636_, v_inst_1637_, v_inst_1638_, v_inst_1639_, v_inst_1640_, v_inst_1641_, v_cls_1642_, v_collapsed_boxed_1653_, v_tag_1644_, v_opts_1645_, v_clsEnabled_boxed_1654_, v_msg_1647_, v_toPure_1648_, v_toBind_1649_, v_k_1650_, v_inst_1651_, v_oldTraces_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object* v_always_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_inst_1661_, lean_object* v_cls_1662_, uint8_t v_collapsed_1663_, lean_object* v_tag_1664_, lean_object* v_opts_1665_, lean_object* v_msg_1666_, lean_object* v_toPure_1667_, lean_object* v_toBind_1668_, lean_object* v_k_1669_, lean_object* v_inst_1670_, uint8_t v_clsEnabled_1671_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___f_1674_; 
v___x_1672_ = lean_box(v_collapsed_1663_);
v___x_1673_ = lean_box(v_clsEnabled_1671_);
lean_inc(v_k_1669_);
lean_inc(v_toBind_1668_);
lean_inc_ref(v_opts_1665_);
lean_inc_ref(v_inst_1658_);
lean_inc_ref(v_inst_1657_);
v___f_1674_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_1674_, 0, v_always_1656_);
lean_closure_set(v___f_1674_, 1, v_inst_1657_);
lean_closure_set(v___f_1674_, 2, v_inst_1658_);
lean_closure_set(v___f_1674_, 3, v_inst_1659_);
lean_closure_set(v___f_1674_, 4, v_inst_1660_);
lean_closure_set(v___f_1674_, 5, v_inst_1661_);
lean_closure_set(v___f_1674_, 6, v_cls_1662_);
lean_closure_set(v___f_1674_, 7, v___x_1672_);
lean_closure_set(v___f_1674_, 8, v_tag_1664_);
lean_closure_set(v___f_1674_, 9, v_opts_1665_);
lean_closure_set(v___f_1674_, 10, v___x_1673_);
lean_closure_set(v___f_1674_, 11, v_msg_1666_);
lean_closure_set(v___f_1674_, 12, v_toPure_1667_);
lean_closure_set(v___f_1674_, 13, v_toBind_1668_);
lean_closure_set(v___f_1674_, 14, v_k_1669_);
lean_closure_set(v___f_1674_, 15, v_inst_1670_);
if (v_clsEnabled_1671_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1678_ = l_Lean_KVMap_instValueBool;
v___x_1679_ = l_Lean_trace_profiler;
v___x_1680_ = l_Lean_Option_get___redArg(v___x_1678_, v_opts_1665_, v___x_1679_);
lean_dec_ref(v_opts_1665_);
v___x_1681_ = lean_unbox(v___x_1680_);
lean_dec(v___x_1680_);
if (v___x_1681_ == 0)
{
lean_dec_ref(v___f_1674_);
lean_dec(v_toBind_1668_);
lean_dec_ref(v_inst_1658_);
lean_dec_ref(v_inst_1657_);
return v_k_1669_;
}
else
{
lean_dec(v_k_1669_);
goto v___jp_1675_;
}
}
else
{
lean_dec(v_k_1669_);
lean_dec_ref(v_opts_1665_);
goto v___jp_1675_;
}
v___jp_1675_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1657_, v_inst_1658_);
v___x_1677_ = lean_apply_4(v_toBind_1668_, lean_box(0), lean_box(0), v___x_1676_, v___f_1674_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object* v_always_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v_cls_1688_, lean_object* v_collapsed_1689_, lean_object* v_tag_1690_, lean_object* v_opts_1691_, lean_object* v_msg_1692_, lean_object* v_toPure_1693_, lean_object* v_toBind_1694_, lean_object* v_k_1695_, lean_object* v_inst_1696_, lean_object* v_clsEnabled_1697_){
_start:
{
uint8_t v_collapsed_boxed_1698_; uint8_t v_clsEnabled_boxed_1699_; lean_object* v_res_1700_; 
v_collapsed_boxed_1698_ = lean_unbox(v_collapsed_1689_);
v_clsEnabled_boxed_1699_ = lean_unbox(v_clsEnabled_1697_);
v_res_1700_ = l_Lean_withTraceNode___redArg___lam__10(v_always_1682_, v_inst_1683_, v_inst_1684_, v_inst_1685_, v_inst_1686_, v_inst_1687_, v_cls_1688_, v_collapsed_boxed_1698_, v_tag_1690_, v_opts_1691_, v_msg_1692_, v_toPure_1693_, v_toBind_1694_, v_k_1695_, v_inst_1696_, v_clsEnabled_boxed_1699_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object* v_k_1701_, lean_object* v_inst_1702_, lean_object* v_toApplicative_1703_, lean_object* v_always_1704_, lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_cls_1709_, uint8_t v_collapsed_1710_, lean_object* v_tag_1711_, lean_object* v_msg_1712_, lean_object* v_toBind_1713_, lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_opts_1716_){
_start:
{
uint8_t v_hasTrace_1717_; 
v_hasTrace_1717_ = lean_ctor_get_uint8(v_opts_1716_, sizeof(void*)*1);
if (v_hasTrace_1717_ == 0)
{
lean_dec_ref(v_opts_1716_);
lean_dec(v_inst_1715_);
lean_dec(v_inst_1714_);
lean_dec(v_toBind_1713_);
lean_dec(v_msg_1712_);
lean_dec_ref(v_tag_1711_);
lean_dec(v_cls_1709_);
lean_dec_ref(v_inst_1708_);
lean_dec(v_inst_1707_);
lean_dec_ref(v_inst_1706_);
lean_dec_ref(v_inst_1705_);
lean_dec_ref(v_always_1704_);
lean_dec_ref(v_toApplicative_1703_);
lean_dec_ref(v_inst_1702_);
return v_k_1701_;
}
else
{
lean_object* v_getInheritedTraceOptions_1718_; lean_object* v_toPure_1719_; lean_object* v___x_1720_; lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_getInheritedTraceOptions_1718_ = lean_ctor_get(v_inst_1702_, 2);
lean_inc(v_getInheritedTraceOptions_1718_);
v_toPure_1719_ = lean_ctor_get(v_toApplicative_1703_, 1);
lean_inc_n(v_toPure_1719_, 2);
lean_dec_ref(v_toApplicative_1703_);
v___x_1720_ = lean_box(v_collapsed_1710_);
lean_inc_n(v_toBind_1713_, 3);
lean_inc(v_cls_1709_);
v___f_1721_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_1721_, 0, v_always_1704_);
lean_closure_set(v___f_1721_, 1, v_inst_1705_);
lean_closure_set(v___f_1721_, 2, v_inst_1702_);
lean_closure_set(v___f_1721_, 3, v_inst_1706_);
lean_closure_set(v___f_1721_, 4, v_inst_1707_);
lean_closure_set(v___f_1721_, 5, v_inst_1708_);
lean_closure_set(v___f_1721_, 6, v_cls_1709_);
lean_closure_set(v___f_1721_, 7, v___x_1720_);
lean_closure_set(v___f_1721_, 8, v_tag_1711_);
lean_closure_set(v___f_1721_, 9, v_opts_1716_);
lean_closure_set(v___f_1721_, 10, v_msg_1712_);
lean_closure_set(v___f_1721_, 11, v_toPure_1719_);
lean_closure_set(v___f_1721_, 12, v_toBind_1713_);
lean_closure_set(v___f_1721_, 13, v_k_1701_);
lean_closure_set(v___f_1721_, 14, v_inst_1714_);
v___f_1722_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1722_, 0, v_toPure_1719_);
lean_closure_set(v___f_1722_, 1, v_cls_1709_);
lean_closure_set(v___f_1722_, 2, v_toBind_1713_);
lean_closure_set(v___f_1722_, 3, v_inst_1715_);
v___x_1723_ = lean_apply_4(v_toBind_1713_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1718_, v___f_1722_);
v___x_1724_ = lean_apply_4(v_toBind_1713_, lean_box(0), lean_box(0), v___x_1723_, v___f_1721_);
return v___x_1724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13___boxed(lean_object* v_k_1725_, lean_object* v_inst_1726_, lean_object* v_toApplicative_1727_, lean_object* v_always_1728_, lean_object* v_inst_1729_, lean_object* v_inst_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_cls_1733_, lean_object* v_collapsed_1734_, lean_object* v_tag_1735_, lean_object* v_msg_1736_, lean_object* v_toBind_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_opts_1740_){
_start:
{
uint8_t v_collapsed_boxed_1741_; lean_object* v_res_1742_; 
v_collapsed_boxed_1741_ = lean_unbox(v_collapsed_1734_);
v_res_1742_ = l_Lean_withTraceNode___redArg___lam__13(v_k_1725_, v_inst_1726_, v_toApplicative_1727_, v_always_1728_, v_inst_1729_, v_inst_1730_, v_inst_1731_, v_inst_1732_, v_cls_1733_, v_collapsed_boxed_1741_, v_tag_1735_, v_msg_1736_, v_toBind_1737_, v_inst_1738_, v_inst_1739_, v_opts_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object* v_inst_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_inst_1747_, lean_object* v_always_1748_, lean_object* v_inst_1749_, lean_object* v_inst_1750_, lean_object* v_cls_1751_, lean_object* v_msg_1752_, lean_object* v_k_1753_, uint8_t v_collapsed_1754_, lean_object* v_tag_1755_){
_start:
{
lean_object* v_toApplicative_1756_; lean_object* v_toBind_1757_; lean_object* v___x_1758_; lean_object* v___f_1759_; lean_object* v___x_1760_; 
v_toApplicative_1756_ = lean_ctor_get(v_inst_1743_, 0);
lean_inc_ref(v_toApplicative_1756_);
v_toBind_1757_ = lean_ctor_get(v_inst_1743_, 1);
lean_inc_n(v_toBind_1757_, 2);
v___x_1758_ = lean_box(v_collapsed_1754_);
lean_inc(v_inst_1747_);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1759_, 0, v_k_1753_);
lean_closure_set(v___f_1759_, 1, v_inst_1744_);
lean_closure_set(v___f_1759_, 2, v_toApplicative_1756_);
lean_closure_set(v___f_1759_, 3, v_always_1748_);
lean_closure_set(v___f_1759_, 4, v_inst_1743_);
lean_closure_set(v___f_1759_, 5, v_inst_1745_);
lean_closure_set(v___f_1759_, 6, v_inst_1746_);
lean_closure_set(v___f_1759_, 7, v_inst_1750_);
lean_closure_set(v___f_1759_, 8, v_cls_1751_);
lean_closure_set(v___f_1759_, 9, v___x_1758_);
lean_closure_set(v___f_1759_, 10, v_tag_1755_);
lean_closure_set(v___f_1759_, 11, v_msg_1752_);
lean_closure_set(v___f_1759_, 12, v_toBind_1757_);
lean_closure_set(v___f_1759_, 13, v_inst_1749_);
lean_closure_set(v___f_1759_, 14, v_inst_1747_);
v___x_1760_ = lean_apply_4(v_toBind_1757_, lean_box(0), lean_box(0), v_inst_1747_, v___f_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object* v_inst_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_always_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_cls_1769_, lean_object* v_msg_1770_, lean_object* v_k_1771_, lean_object* v_collapsed_1772_, lean_object* v_tag_1773_){
_start:
{
uint8_t v_collapsed_boxed_1774_; lean_object* v_res_1775_; 
v_collapsed_boxed_1774_ = lean_unbox(v_collapsed_1772_);
v_res_1775_ = l_Lean_withTraceNode___redArg(v_inst_1761_, v_inst_1762_, v_inst_1763_, v_inst_1764_, v_inst_1765_, v_always_1766_, v_inst_1767_, v_inst_1768_, v_cls_1769_, v_msg_1770_, v_k_1771_, v_collapsed_boxed_1774_, v_tag_1773_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object* v_00_u03b1_1776_, lean_object* v_m_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_00_u03b5_1783_, lean_object* v_always_1784_, lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_cls_1787_, lean_object* v_msg_1788_, lean_object* v_k_1789_, uint8_t v_collapsed_1790_, lean_object* v_tag_1791_){
_start:
{
lean_object* v_toApplicative_1792_; lean_object* v_toBind_1793_; lean_object* v___x_1794_; lean_object* v___f_1795_; lean_object* v___x_1796_; 
v_toApplicative_1792_ = lean_ctor_get(v_inst_1778_, 0);
lean_inc_ref(v_toApplicative_1792_);
v_toBind_1793_ = lean_ctor_get(v_inst_1778_, 1);
lean_inc_n(v_toBind_1793_, 2);
v___x_1794_ = lean_box(v_collapsed_1790_);
lean_inc(v_inst_1782_);
v___f_1795_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1795_, 0, v_k_1789_);
lean_closure_set(v___f_1795_, 1, v_inst_1779_);
lean_closure_set(v___f_1795_, 2, v_toApplicative_1792_);
lean_closure_set(v___f_1795_, 3, v_always_1784_);
lean_closure_set(v___f_1795_, 4, v_inst_1778_);
lean_closure_set(v___f_1795_, 5, v_inst_1780_);
lean_closure_set(v___f_1795_, 6, v_inst_1781_);
lean_closure_set(v___f_1795_, 7, v_inst_1786_);
lean_closure_set(v___f_1795_, 8, v_cls_1787_);
lean_closure_set(v___f_1795_, 9, v___x_1794_);
lean_closure_set(v___f_1795_, 10, v_tag_1791_);
lean_closure_set(v___f_1795_, 11, v_msg_1788_);
lean_closure_set(v___f_1795_, 12, v_toBind_1793_);
lean_closure_set(v___f_1795_, 13, v_inst_1785_);
lean_closure_set(v___f_1795_, 14, v_inst_1782_);
v___x_1796_ = lean_apply_4(v_toBind_1793_, lean_box(0), lean_box(0), v_inst_1782_, v___f_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object* v_00_u03b1_1797_, lean_object* v_m_1798_, lean_object* v_inst_1799_, lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_00_u03b5_1804_, lean_object* v_always_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_cls_1808_, lean_object* v_msg_1809_, lean_object* v_k_1810_, lean_object* v_collapsed_1811_, lean_object* v_tag_1812_){
_start:
{
uint8_t v_collapsed_boxed_1813_; lean_object* v_res_1814_; 
v_collapsed_boxed_1813_ = lean_unbox(v_collapsed_1811_);
v_res_1814_ = l_Lean_withTraceNode(v_00_u03b1_1797_, v_m_1798_, v_inst_1799_, v_inst_1800_, v_inst_1801_, v_inst_1802_, v_inst_1803_, v_00_u03b5_1804_, v_always_1805_, v_inst_1806_, v_inst_1807_, v_cls_1808_, v_msg_1809_, v_k_1810_, v_collapsed_boxed_1813_, v_tag_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object* v_self_1815_){
_start:
{
lean_object* v_fst_1816_; 
v_fst_1816_ = lean_ctor_get(v_self_1815_, 0);
lean_inc(v_fst_1816_);
return v_fst_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object* v_self_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_1817_);
lean_dec_ref(v_self_1817_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object* v_toPure_1819_, lean_object* v_x_1820_){
_start:
{
if (lean_obj_tag(v_x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_a_1821_ = lean_ctor_get(v_x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref(v_x_1820_);
v___x_1822_ = l_Lean_Exception_toMessageData(v_a_1821_);
v___x_1823_ = lean_apply_2(v_toPure_1819_, lean_box(0), v___x_1822_);
return v___x_1823_;
}
else
{
lean_object* v_a_1824_; lean_object* v_snd_1825_; lean_object* v___x_1826_; 
v_a_1824_ = lean_ctor_get(v_x_1820_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v_x_1820_);
v_snd_1825_ = lean_ctor_get(v_a_1824_, 1);
lean_inc(v_snd_1825_);
lean_dec(v_a_1824_);
v___x_1826_ = lean_apply_2(v_toPure_1819_, lean_box(0), v_snd_1825_);
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object* v_toPure_1827_, lean_object* v_ex_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v_ex_1828_);
v___x_1830_ = lean_apply_2(v_toPure_1827_, lean_box(0), v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object* v_toPure_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1833_, 0, v_a_1832_);
v___x_1834_ = lean_apply_2(v_toPure_1831_, lean_box(0), v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v___f_1840_, lean_object* v_cls_1841_, uint8_t v_collapsed_1842_, lean_object* v_tag_1843_, lean_object* v_opts_1844_, uint8_t v_clsEnabled_1845_, lean_object* v_oldTraces_1846_, lean_object* v_msg_1847_, lean_object* v_resStartStop_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1835_, v_inst_1836_, v_inst_1837_, v_inst_1838_, v_inst_1839_, v___f_1840_, v_cls_1841_, v_collapsed_1842_, v_tag_1843_, v_opts_1844_, v_clsEnabled_1845_, v_oldTraces_1846_, v_msg_1847_, v_resStartStop_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3___boxed(lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v___f_1855_, lean_object* v_cls_1856_, lean_object* v_collapsed_1857_, lean_object* v_tag_1858_, lean_object* v_opts_1859_, lean_object* v_clsEnabled_1860_, lean_object* v_oldTraces_1861_, lean_object* v_msg_1862_, lean_object* v_resStartStop_1863_){
_start:
{
uint8_t v_collapsed_boxed_1864_; uint8_t v_clsEnabled_boxed_1865_; lean_object* v_res_1866_; 
v_collapsed_boxed_1864_ = lean_unbox(v_collapsed_1857_);
v_clsEnabled_boxed_1865_ = lean_unbox(v_clsEnabled_1860_);
v_res_1866_ = l_Lean_withTraceNode_x27___redArg___lam__3(v_inst_1850_, v_inst_1851_, v_inst_1852_, v_inst_1853_, v_inst_1854_, v___f_1855_, v_cls_1856_, v_collapsed_boxed_1864_, v_tag_1858_, v_opts_1859_, v_clsEnabled_boxed_1865_, v_oldTraces_1861_, v_msg_1862_, v_resStartStop_1863_);
lean_dec_ref(v_opts_1859_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object* v_start_1867_, lean_object* v_a_1868_, lean_object* v_toPure_1869_, lean_object* v_stop_1870_){
_start:
{
double v___x_1871_; double v___x_1872_; double v___x_1873_; double v___x_1874_; double v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1871_ = lean_float_of_nat(v_start_1867_);
v___x_1872_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1873_ = lean_float_div(v___x_1871_, v___x_1872_);
v___x_1874_ = lean_float_of_nat(v_stop_1870_);
v___x_1875_ = lean_float_div(v___x_1874_, v___x_1872_);
v___x_1876_ = lean_box_float(v___x_1873_);
v___x_1877_ = lean_box_float(v___x_1875_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v_a_1868_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_apply_2(v_toPure_1869_, lean_box(0), v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object* v_start_1881_, lean_object* v_toPure_1882_, lean_object* v_toBind_1883_, lean_object* v___x_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v___f_1886_; lean_object* v___x_1887_; 
v___f_1886_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__5), 4, 3);
lean_closure_set(v___f_1886_, 0, v_start_1881_);
lean_closure_set(v___f_1886_, 1, v_a_1885_);
lean_closure_set(v___f_1886_, 2, v_toPure_1882_);
v___x_1887_ = lean_apply_4(v_toBind_1883_, lean_box(0), lean_box(0), v___x_1884_, v___f_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object* v_toPure_1888_, lean_object* v_toBind_1889_, lean_object* v___x_1890_, lean_object* v___x_1891_, lean_object* v_start_1892_){
_start:
{
lean_object* v___f_1893_; lean_object* v___x_1894_; 
lean_inc(v_toBind_1889_);
v___f_1893_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__6), 5, 4);
lean_closure_set(v___f_1893_, 0, v_start_1892_);
lean_closure_set(v___f_1893_, 1, v_toPure_1888_);
lean_closure_set(v___f_1893_, 2, v_toBind_1889_);
lean_closure_set(v___f_1893_, 3, v___x_1890_);
v___x_1894_ = lean_apply_4(v_toBind_1889_, lean_box(0), lean_box(0), v___x_1891_, v___f_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object* v_start_1895_, lean_object* v_a_1896_, lean_object* v_toPure_1897_, lean_object* v_stop_1898_){
_start:
{
double v___x_1899_; double v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1899_ = lean_float_of_nat(v_start_1895_);
v___x_1900_ = lean_float_of_nat(v_stop_1898_);
v___x_1901_ = lean_box_float(v___x_1899_);
v___x_1902_ = lean_box_float(v___x_1900_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_a_1896_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = lean_apply_2(v_toPure_1897_, lean_box(0), v___x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object* v_start_1906_, lean_object* v_toPure_1907_, lean_object* v_toBind_1908_, lean_object* v___x_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v___f_1911_; lean_object* v___x_1912_; 
v___f_1911_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__8), 4, 3);
lean_closure_set(v___f_1911_, 0, v_start_1906_);
lean_closure_set(v___f_1911_, 1, v_a_1910_);
lean_closure_set(v___f_1911_, 2, v_toPure_1907_);
v___x_1912_ = lean_apply_4(v_toBind_1908_, lean_box(0), lean_box(0), v___x_1909_, v___f_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object* v_toPure_1913_, lean_object* v_toBind_1914_, lean_object* v___x_1915_, lean_object* v___x_1916_, lean_object* v_start_1917_){
_start:
{
lean_object* v___f_1918_; lean_object* v___x_1919_; 
lean_inc(v_toBind_1914_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__9), 5, 4);
lean_closure_set(v___f_1918_, 0, v_start_1917_);
lean_closure_set(v___f_1918_, 1, v_toPure_1913_);
lean_closure_set(v___f_1918_, 2, v_toBind_1914_);
lean_closure_set(v___f_1918_, 3, v___x_1915_);
v___x_1919_ = lean_apply_4(v_toBind_1914_, lean_box(0), lean_box(0), v___x_1916_, v___f_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object* v_inst_1920_, lean_object* v_inst_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v___f_1925_, lean_object* v_cls_1926_, uint8_t v_collapsed_1927_, lean_object* v_tag_1928_, lean_object* v_opts_1929_, uint8_t v_clsEnabled_1930_, lean_object* v_msg_1931_, lean_object* v_toBind_1932_, lean_object* v_k_1933_, lean_object* v___f_1934_, lean_object* v___f_1935_, lean_object* v_inst_1936_, lean_object* v_toPure_1937_, lean_object* v_oldTraces_1938_){
_start:
{
lean_object* v_tryCatch_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v_tryCatch_1939_ = lean_ctor_get(v_inst_1920_, 1);
lean_inc(v_tryCatch_1939_);
v___x_1940_ = lean_box(v_collapsed_1927_);
v___x_1941_ = lean_box(v_clsEnabled_1930_);
lean_inc_ref(v_opts_1929_);
v___f_1942_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_1942_, 0, v_inst_1921_);
lean_closure_set(v___f_1942_, 1, v_inst_1922_);
lean_closure_set(v___f_1942_, 2, v_inst_1923_);
lean_closure_set(v___f_1942_, 3, v_inst_1924_);
lean_closure_set(v___f_1942_, 4, v_inst_1920_);
lean_closure_set(v___f_1942_, 5, v___f_1925_);
lean_closure_set(v___f_1942_, 6, v_cls_1926_);
lean_closure_set(v___f_1942_, 7, v___x_1940_);
lean_closure_set(v___f_1942_, 8, v_tag_1928_);
lean_closure_set(v___f_1942_, 9, v_opts_1929_);
lean_closure_set(v___f_1942_, 10, v___x_1941_);
lean_closure_set(v___f_1942_, 11, v_oldTraces_1938_);
lean_closure_set(v___f_1942_, 12, v_msg_1931_);
lean_inc(v_toBind_1932_);
v___x_1943_ = lean_apply_4(v_toBind_1932_, lean_box(0), lean_box(0), v_k_1933_, v___f_1934_);
v___x_1944_ = lean_apply_3(v_tryCatch_1939_, lean_box(0), v___x_1943_, v___f_1935_);
v___x_1945_ = l_Lean_KVMap_instValueBool;
v___x_1946_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1947_ = l_Lean_Option_get___redArg(v___x_1945_, v_opts_1929_, v___x_1946_);
lean_dec_ref(v_opts_1929_);
v___x_1948_ = lean_unbox(v___x_1947_);
lean_dec(v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___f_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1949_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1950_ = lean_apply_2(v_inst_1936_, lean_box(0), v___x_1949_);
lean_inc(v___x_1950_);
lean_inc_n(v_toBind_1932_, 2);
v___f_1951_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1951_, 0, v_toPure_1937_);
lean_closure_set(v___f_1951_, 1, v_toBind_1932_);
lean_closure_set(v___f_1951_, 2, v___x_1950_);
lean_closure_set(v___f_1951_, 3, v___x_1944_);
v___x_1952_ = lean_apply_4(v_toBind_1932_, lean_box(0), lean_box(0), v___x_1950_, v___f_1951_);
v___x_1953_ = lean_apply_4(v_toBind_1932_, lean_box(0), lean_box(0), v___x_1952_, v___f_1942_);
return v___x_1953_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___f_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1954_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1955_ = lean_apply_2(v_inst_1936_, lean_box(0), v___x_1954_);
lean_inc(v___x_1955_);
lean_inc_n(v_toBind_1932_, 2);
v___f_1956_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__10), 5, 4);
lean_closure_set(v___f_1956_, 0, v_toPure_1937_);
lean_closure_set(v___f_1956_, 1, v_toBind_1932_);
lean_closure_set(v___f_1956_, 2, v___x_1955_);
lean_closure_set(v___f_1956_, 3, v___x_1944_);
v___x_1957_ = lean_apply_4(v_toBind_1932_, lean_box(0), lean_box(0), v___x_1955_, v___f_1956_);
v___x_1958_ = lean_apply_4(v_toBind_1932_, lean_box(0), lean_box(0), v___x_1957_, v___f_1942_);
return v___x_1958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_1959_ = _args[0];
lean_object* v_inst_1960_ = _args[1];
lean_object* v_inst_1961_ = _args[2];
lean_object* v_inst_1962_ = _args[3];
lean_object* v_inst_1963_ = _args[4];
lean_object* v___f_1964_ = _args[5];
lean_object* v_cls_1965_ = _args[6];
lean_object* v_collapsed_1966_ = _args[7];
lean_object* v_tag_1967_ = _args[8];
lean_object* v_opts_1968_ = _args[9];
lean_object* v_clsEnabled_1969_ = _args[10];
lean_object* v_msg_1970_ = _args[11];
lean_object* v_toBind_1971_ = _args[12];
lean_object* v_k_1972_ = _args[13];
lean_object* v___f_1973_ = _args[14];
lean_object* v___f_1974_ = _args[15];
lean_object* v_inst_1975_ = _args[16];
lean_object* v_toPure_1976_ = _args[17];
lean_object* v_oldTraces_1977_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_1978_; uint8_t v_clsEnabled_boxed_1979_; lean_object* v_res_1980_; 
v_collapsed_boxed_1978_ = lean_unbox(v_collapsed_1966_);
v_clsEnabled_boxed_1979_ = lean_unbox(v_clsEnabled_1969_);
v_res_1980_ = l_Lean_withTraceNode_x27___redArg___lam__11(v_inst_1959_, v_inst_1960_, v_inst_1961_, v_inst_1962_, v_inst_1963_, v___f_1964_, v_cls_1965_, v_collapsed_boxed_1978_, v_tag_1967_, v_opts_1968_, v_clsEnabled_boxed_1979_, v_msg_1970_, v_toBind_1971_, v_k_1972_, v___f_1973_, v___f_1974_, v_inst_1975_, v_toPure_1976_, v_oldTraces_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v___f_1986_, lean_object* v_cls_1987_, uint8_t v_collapsed_1988_, lean_object* v_tag_1989_, lean_object* v_opts_1990_, lean_object* v_msg_1991_, lean_object* v_toBind_1992_, lean_object* v_k_1993_, lean_object* v___f_1994_, lean_object* v___f_1995_, lean_object* v_inst_1996_, lean_object* v_toPure_1997_, uint8_t v_clsEnabled_1998_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___f_2001_; 
v___x_1999_ = lean_box(v_collapsed_1988_);
v___x_2000_ = lean_box(v_clsEnabled_1998_);
lean_inc(v_k_1993_);
lean_inc(v_toBind_1992_);
lean_inc_ref(v_opts_1990_);
lean_inc_ref(v_inst_1983_);
lean_inc_ref(v_inst_1982_);
v___f_2001_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__11___boxed), 19, 18);
lean_closure_set(v___f_2001_, 0, v_inst_1981_);
lean_closure_set(v___f_2001_, 1, v_inst_1982_);
lean_closure_set(v___f_2001_, 2, v_inst_1983_);
lean_closure_set(v___f_2001_, 3, v_inst_1984_);
lean_closure_set(v___f_2001_, 4, v_inst_1985_);
lean_closure_set(v___f_2001_, 5, v___f_1986_);
lean_closure_set(v___f_2001_, 6, v_cls_1987_);
lean_closure_set(v___f_2001_, 7, v___x_1999_);
lean_closure_set(v___f_2001_, 8, v_tag_1989_);
lean_closure_set(v___f_2001_, 9, v_opts_1990_);
lean_closure_set(v___f_2001_, 10, v___x_2000_);
lean_closure_set(v___f_2001_, 11, v_msg_1991_);
lean_closure_set(v___f_2001_, 12, v_toBind_1992_);
lean_closure_set(v___f_2001_, 13, v_k_1993_);
lean_closure_set(v___f_2001_, 14, v___f_1994_);
lean_closure_set(v___f_2001_, 15, v___f_1995_);
lean_closure_set(v___f_2001_, 16, v_inst_1996_);
lean_closure_set(v___f_2001_, 17, v_toPure_1997_);
if (v_clsEnabled_1998_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2005_ = l_Lean_KVMap_instValueBool;
v___x_2006_ = l_Lean_trace_profiler;
v___x_2007_ = l_Lean_Option_get___redArg(v___x_2005_, v_opts_1990_, v___x_2006_);
lean_dec_ref(v_opts_1990_);
v___x_2008_ = lean_unbox(v___x_2007_);
lean_dec(v___x_2007_);
if (v___x_2008_ == 0)
{
lean_dec_ref(v___f_2001_);
lean_dec(v_toBind_1992_);
lean_dec_ref(v_inst_1983_);
lean_dec_ref(v_inst_1982_);
return v_k_1993_;
}
else
{
lean_dec(v_k_1993_);
goto v___jp_2002_;
}
}
else
{
lean_dec(v_k_1993_);
lean_dec_ref(v_opts_1990_);
goto v___jp_2002_;
}
v___jp_2002_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1982_, v_inst_1983_);
v___x_2004_ = lean_apply_4(v_toBind_1992_, lean_box(0), lean_box(0), v___x_2003_, v___f_2001_);
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_inst_2009_ = _args[0];
lean_object* v_inst_2010_ = _args[1];
lean_object* v_inst_2011_ = _args[2];
lean_object* v_inst_2012_ = _args[3];
lean_object* v_inst_2013_ = _args[4];
lean_object* v___f_2014_ = _args[5];
lean_object* v_cls_2015_ = _args[6];
lean_object* v_collapsed_2016_ = _args[7];
lean_object* v_tag_2017_ = _args[8];
lean_object* v_opts_2018_ = _args[9];
lean_object* v_msg_2019_ = _args[10];
lean_object* v_toBind_2020_ = _args[11];
lean_object* v_k_2021_ = _args[12];
lean_object* v___f_2022_ = _args[13];
lean_object* v___f_2023_ = _args[14];
lean_object* v_inst_2024_ = _args[15];
lean_object* v_toPure_2025_ = _args[16];
lean_object* v_clsEnabled_2026_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2027_; uint8_t v_clsEnabled_boxed_2028_; lean_object* v_res_2029_; 
v_collapsed_boxed_2027_ = lean_unbox(v_collapsed_2016_);
v_clsEnabled_boxed_2028_ = lean_unbox(v_clsEnabled_2026_);
v_res_2029_ = l_Lean_withTraceNode_x27___redArg___lam__12(v_inst_2009_, v_inst_2010_, v_inst_2011_, v_inst_2012_, v_inst_2013_, v___f_2014_, v_cls_2015_, v_collapsed_boxed_2027_, v_tag_2017_, v_opts_2018_, v_msg_2019_, v_toBind_2020_, v_k_2021_, v___f_2022_, v___f_2023_, v_inst_2024_, v_toPure_2025_, v_clsEnabled_boxed_2028_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object* v_k_2030_, lean_object* v_inst_2031_, lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v___f_2036_, lean_object* v_cls_2037_, uint8_t v_collapsed_2038_, lean_object* v_tag_2039_, lean_object* v_msg_2040_, lean_object* v_toBind_2041_, lean_object* v___f_2042_, lean_object* v___f_2043_, lean_object* v_inst_2044_, lean_object* v_toPure_2045_, lean_object* v___f_2046_, lean_object* v_opts_2047_){
_start:
{
uint8_t v_hasTrace_2048_; 
v_hasTrace_2048_ = lean_ctor_get_uint8(v_opts_2047_, sizeof(void*)*1);
if (v_hasTrace_2048_ == 0)
{
lean_dec_ref(v_opts_2047_);
lean_dec(v___f_2046_);
lean_dec(v_toPure_2045_);
lean_dec(v_inst_2044_);
lean_dec(v___f_2043_);
lean_dec(v___f_2042_);
lean_dec(v_toBind_2041_);
lean_dec(v_msg_2040_);
lean_dec_ref(v_tag_2039_);
lean_dec(v_cls_2037_);
lean_dec_ref(v___f_2036_);
lean_dec(v_inst_2035_);
lean_dec_ref(v_inst_2034_);
lean_dec_ref(v_inst_2033_);
lean_dec_ref(v_inst_2032_);
lean_dec_ref(v_inst_2031_);
return v_k_2030_;
}
else
{
lean_object* v_getInheritedTraceOptions_2049_; lean_object* v___x_2050_; lean_object* v___f_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_getInheritedTraceOptions_2049_ = lean_ctor_get(v_inst_2031_, 2);
lean_inc(v_getInheritedTraceOptions_2049_);
v___x_2050_ = lean_box(v_collapsed_2038_);
lean_inc_n(v_toBind_2041_, 2);
v___f_2051_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_2051_, 0, v_inst_2032_);
lean_closure_set(v___f_2051_, 1, v_inst_2033_);
lean_closure_set(v___f_2051_, 2, v_inst_2031_);
lean_closure_set(v___f_2051_, 3, v_inst_2034_);
lean_closure_set(v___f_2051_, 4, v_inst_2035_);
lean_closure_set(v___f_2051_, 5, v___f_2036_);
lean_closure_set(v___f_2051_, 6, v_cls_2037_);
lean_closure_set(v___f_2051_, 7, v___x_2050_);
lean_closure_set(v___f_2051_, 8, v_tag_2039_);
lean_closure_set(v___f_2051_, 9, v_opts_2047_);
lean_closure_set(v___f_2051_, 10, v_msg_2040_);
lean_closure_set(v___f_2051_, 11, v_toBind_2041_);
lean_closure_set(v___f_2051_, 12, v_k_2030_);
lean_closure_set(v___f_2051_, 13, v___f_2042_);
lean_closure_set(v___f_2051_, 14, v___f_2043_);
lean_closure_set(v___f_2051_, 15, v_inst_2044_);
lean_closure_set(v___f_2051_, 16, v_toPure_2045_);
v___x_2052_ = lean_apply_4(v_toBind_2041_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2049_, v___f_2046_);
v___x_2053_ = lean_apply_4(v_toBind_2041_, lean_box(0), lean_box(0), v___x_2052_, v___f_2051_);
return v___x_2053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_k_2054_ = _args[0];
lean_object* v_inst_2055_ = _args[1];
lean_object* v_inst_2056_ = _args[2];
lean_object* v_inst_2057_ = _args[3];
lean_object* v_inst_2058_ = _args[4];
lean_object* v_inst_2059_ = _args[5];
lean_object* v___f_2060_ = _args[6];
lean_object* v_cls_2061_ = _args[7];
lean_object* v_collapsed_2062_ = _args[8];
lean_object* v_tag_2063_ = _args[9];
lean_object* v_msg_2064_ = _args[10];
lean_object* v_toBind_2065_ = _args[11];
lean_object* v___f_2066_ = _args[12];
lean_object* v___f_2067_ = _args[13];
lean_object* v_inst_2068_ = _args[14];
lean_object* v_toPure_2069_ = _args[15];
lean_object* v___f_2070_ = _args[16];
lean_object* v_opts_2071_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2072_; lean_object* v_res_2073_; 
v_collapsed_boxed_2072_ = lean_unbox(v_collapsed_2062_);
v_res_2073_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_k_2054_, v_inst_2055_, v_inst_2056_, v_inst_2057_, v_inst_2058_, v_inst_2059_, v___f_2060_, v_cls_2061_, v_collapsed_boxed_2072_, v_tag_2063_, v_msg_2064_, v_toBind_2065_, v___f_2066_, v___f_2067_, v_inst_2068_, v_toPure_2069_, v___f_2070_, v_opts_2071_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_cls_2082_, lean_object* v_k_2083_, uint8_t v_collapsed_2084_, lean_object* v_tag_2085_){
_start:
{
lean_object* v_toApplicative_2086_; lean_object* v_toFunctor_2087_; lean_object* v_toBind_2088_; lean_object* v_toPure_2089_; lean_object* v_map_2090_; lean_object* v___f_2091_; lean_object* v_msg_2092_; lean_object* v___f_2093_; lean_object* v___f_2094_; lean_object* v___f_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; lean_object* v___f_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_toApplicative_2086_ = lean_ctor_get(v_inst_2075_, 0);
v_toFunctor_2087_ = lean_ctor_get(v_toApplicative_2086_, 0);
v_toBind_2088_ = lean_ctor_get(v_inst_2075_, 1);
lean_inc_n(v_toBind_2088_, 3);
v_toPure_2089_ = lean_ctor_get(v_toApplicative_2086_, 1);
lean_inc_n(v_toPure_2089_, 5);
v_map_2090_ = lean_ctor_get(v_toFunctor_2087_, 0);
lean_inc(v_map_2090_);
v___f_2091_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2092_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2092_, 0, v_toPure_2089_);
lean_inc(v_inst_2079_);
lean_inc(v_cls_2082_);
v___f_2093_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2093_, 0, v_toPure_2089_);
lean_closure_set(v___f_2093_, 1, v_cls_2082_);
lean_closure_set(v___f_2093_, 2, v_toBind_2088_);
lean_closure_set(v___f_2093_, 3, v_inst_2079_);
v___f_2094_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2094_, 0, v_toPure_2089_);
v___f_2095_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2095_, 0, v_toPure_2089_);
v___f_2096_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2097_ = lean_box(v_collapsed_2084_);
v___f_2098_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2098_, 0, v_k_2083_);
lean_closure_set(v___f_2098_, 1, v_inst_2076_);
lean_closure_set(v___f_2098_, 2, v_inst_2080_);
lean_closure_set(v___f_2098_, 3, v_inst_2075_);
lean_closure_set(v___f_2098_, 4, v_inst_2077_);
lean_closure_set(v___f_2098_, 5, v_inst_2078_);
lean_closure_set(v___f_2098_, 6, v___f_2096_);
lean_closure_set(v___f_2098_, 7, v_cls_2082_);
lean_closure_set(v___f_2098_, 8, v___x_2097_);
lean_closure_set(v___f_2098_, 9, v_tag_2085_);
lean_closure_set(v___f_2098_, 10, v_msg_2092_);
lean_closure_set(v___f_2098_, 11, v_toBind_2088_);
lean_closure_set(v___f_2098_, 12, v___f_2095_);
lean_closure_set(v___f_2098_, 13, v___f_2094_);
lean_closure_set(v___f_2098_, 14, v_inst_2081_);
lean_closure_set(v___f_2098_, 15, v_toPure_2089_);
lean_closure_set(v___f_2098_, 16, v___f_2093_);
v___x_2099_ = lean_apply_4(v_toBind_2088_, lean_box(0), lean_box(0), v_inst_2079_, v___f_2098_);
v___x_2100_ = lean_apply_4(v_map_2090_, lean_box(0), lean_box(0), v___f_2091_, v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_cls_2108_, lean_object* v_k_2109_, lean_object* v_collapsed_2110_, lean_object* v_tag_2111_){
_start:
{
uint8_t v_collapsed_boxed_2112_; lean_object* v_res_2113_; 
v_collapsed_boxed_2112_ = lean_unbox(v_collapsed_2110_);
v_res_2113_ = l_Lean_withTraceNode_x27___redArg(v_inst_2101_, v_inst_2102_, v_inst_2103_, v_inst_2104_, v_inst_2105_, v_inst_2106_, v_inst_2107_, v_cls_2108_, v_k_2109_, v_collapsed_boxed_2112_, v_tag_2111_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object* v_00_u03b1_2114_, lean_object* v_m_2115_, lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_cls_2123_, lean_object* v_k_2124_, uint8_t v_collapsed_2125_, lean_object* v_tag_2126_){
_start:
{
lean_object* v_toApplicative_2127_; lean_object* v_toFunctor_2128_; lean_object* v_toBind_2129_; lean_object* v_toPure_2130_; lean_object* v_map_2131_; lean_object* v___f_2132_; lean_object* v_msg_2133_; lean_object* v___f_2134_; lean_object* v___f_2135_; lean_object* v___f_2136_; lean_object* v___f_2137_; lean_object* v___x_2138_; lean_object* v___f_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_toApplicative_2127_ = lean_ctor_get(v_inst_2116_, 0);
v_toFunctor_2128_ = lean_ctor_get(v_toApplicative_2127_, 0);
v_toBind_2129_ = lean_ctor_get(v_inst_2116_, 1);
lean_inc_n(v_toBind_2129_, 3);
v_toPure_2130_ = lean_ctor_get(v_toApplicative_2127_, 1);
lean_inc_n(v_toPure_2130_, 5);
v_map_2131_ = lean_ctor_get(v_toFunctor_2128_, 0);
lean_inc(v_map_2131_);
v___f_2132_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2133_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2133_, 0, v_toPure_2130_);
lean_inc(v_inst_2120_);
lean_inc(v_cls_2123_);
v___f_2134_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2134_, 0, v_toPure_2130_);
lean_closure_set(v___f_2134_, 1, v_cls_2123_);
lean_closure_set(v___f_2134_, 2, v_toBind_2129_);
lean_closure_set(v___f_2134_, 3, v_inst_2120_);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2135_, 0, v_toPure_2130_);
v___f_2136_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2136_, 0, v_toPure_2130_);
v___f_2137_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2138_ = lean_box(v_collapsed_2125_);
v___f_2139_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2139_, 0, v_k_2124_);
lean_closure_set(v___f_2139_, 1, v_inst_2117_);
lean_closure_set(v___f_2139_, 2, v_inst_2121_);
lean_closure_set(v___f_2139_, 3, v_inst_2116_);
lean_closure_set(v___f_2139_, 4, v_inst_2118_);
lean_closure_set(v___f_2139_, 5, v_inst_2119_);
lean_closure_set(v___f_2139_, 6, v___f_2137_);
lean_closure_set(v___f_2139_, 7, v_cls_2123_);
lean_closure_set(v___f_2139_, 8, v___x_2138_);
lean_closure_set(v___f_2139_, 9, v_tag_2126_);
lean_closure_set(v___f_2139_, 10, v_msg_2133_);
lean_closure_set(v___f_2139_, 11, v_toBind_2129_);
lean_closure_set(v___f_2139_, 12, v___f_2136_);
lean_closure_set(v___f_2139_, 13, v___f_2135_);
lean_closure_set(v___f_2139_, 14, v_inst_2122_);
lean_closure_set(v___f_2139_, 15, v_toPure_2130_);
lean_closure_set(v___f_2139_, 16, v___f_2134_);
v___x_2140_ = lean_apply_4(v_toBind_2129_, lean_box(0), lean_box(0), v_inst_2120_, v___f_2139_);
v___x_2141_ = lean_apply_4(v_map_2131_, lean_box(0), lean_box(0), v___f_2132_, v___x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object* v_00_u03b1_2142_, lean_object* v_m_2143_, lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_inst_2150_, lean_object* v_cls_2151_, lean_object* v_k_2152_, lean_object* v_collapsed_2153_, lean_object* v_tag_2154_){
_start:
{
uint8_t v_collapsed_boxed_2155_; lean_object* v_res_2156_; 
v_collapsed_boxed_2155_ = lean_unbox(v_collapsed_2153_);
v_res_2156_ = l_Lean_withTraceNode_x27(v_00_u03b1_2142_, v_m_2143_, v_inst_2144_, v_inst_2145_, v_inst_2146_, v_inst_2147_, v_inst_2148_, v_inst_2149_, v_inst_2150_, v_cls_2151_, v_k_2152_, v_collapsed_boxed_2155_, v_tag_2154_);
return v_res_2156_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__4(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__3));
v___x_2166_ = l_Lean_mkAtom(v___x_2165_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__5(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__4, &l_Lean_registerTraceClass___auto__1___closed__4_once, _init_l_Lean_registerTraceClass___auto__1___closed__4);
v___x_2168_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2169_ = lean_array_push(v___x_2168_, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__6(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__5, &l_Lean_registerTraceClass___auto__1___closed__5_once, _init_l_Lean_registerTraceClass___auto__1___closed__5);
v___x_2171_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__2));
v___x_2172_ = lean_box(2);
v___x_2173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
lean_ctor_set(v___x_2173_, 1, v___x_2171_);
lean_ctor_set(v___x_2173_, 2, v___x_2170_);
return v___x_2173_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__7(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__6, &l_Lean_registerTraceClass___auto__1___closed__6_once, _init_l_Lean_registerTraceClass___auto__1___closed__6);
v___x_2175_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_2176_ = lean_array_push(v___x_2175_, v___x_2174_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2177_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__7, &l_Lean_registerTraceClass___auto__1___closed__7_once, _init_l_Lean_registerTraceClass___auto__1___closed__7);
v___x_2178_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_2179_ = lean_box(2);
v___x_2180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v___x_2178_);
lean_ctor_set(v___x_2180_, 2, v___x_2177_);
return v___x_2180_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__8, &l_Lean_registerTraceClass___auto__1___closed__8_once, _init_l_Lean_registerTraceClass___auto__1___closed__8);
v___x_2182_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2183_ = lean_array_push(v___x_2182_, v___x_2181_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2184_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__9, &l_Lean_registerTraceClass___auto__1___closed__9_once, _init_l_Lean_registerTraceClass___auto__1___closed__9);
v___x_2185_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2186_ = lean_box(2);
v___x_2187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v___x_2185_);
lean_ctor_set(v___x_2187_, 2, v___x_2184_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__11(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__10, &l_Lean_registerTraceClass___auto__1___closed__10_once, _init_l_Lean_registerTraceClass___auto__1___closed__10);
v___x_2189_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2190_ = lean_array_push(v___x_2189_, v___x_2188_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2191_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__11, &l_Lean_registerTraceClass___auto__1___closed__11_once, _init_l_Lean_registerTraceClass___auto__1___closed__11);
v___x_2192_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_2193_ = lean_box(2);
v___x_2194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v___x_2192_);
lean_ctor_set(v___x_2194_, 2, v___x_2191_);
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__12, &l_Lean_registerTraceClass___auto__1___closed__12_once, _init_l_Lean_registerTraceClass___auto__1___closed__12);
v___x_2196_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2197_ = lean_array_push(v___x_2196_, v___x_2195_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__13, &l_Lean_registerTraceClass___auto__1___closed__13_once, _init_l_Lean_registerTraceClass___auto__1___closed__13);
v___x_2199_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_2200_ = lean_box(2);
v___x_2201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v___x_2199_);
lean_ctor_set(v___x_2201_, 2, v___x_2198_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1(void){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__14, &l_Lean_registerTraceClass___auto__1___closed__14_once, _init_l_Lean_registerTraceClass___auto__1___closed__14);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
if (lean_obj_tag(v_x_2204_) == 0)
{
return v_x_2203_;
}
else
{
lean_object* v_key_2205_; lean_object* v_value_2206_; lean_object* v_tail_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2233_; 
v_key_2205_ = lean_ctor_get(v_x_2204_, 0);
v_value_2206_ = lean_ctor_get(v_x_2204_, 1);
v_tail_2207_ = lean_ctor_get(v_x_2204_, 2);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_x_2204_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2209_ = v_x_2204_;
v_isShared_2210_ = v_isSharedCheck_2233_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_tail_2207_);
lean_inc(v_value_2206_);
lean_inc(v_key_2205_);
lean_dec(v_x_2204_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2233_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; uint64_t v___y_2213_; 
v___x_2211_ = lean_array_get_size(v_x_2203_);
if (lean_obj_tag(v_key_2205_) == 0)
{
uint64_t v___x_2231_; 
v___x_2231_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2213_ = v___x_2231_;
goto v___jp_2212_;
}
else
{
uint64_t v_hash_2232_; 
v_hash_2232_ = lean_ctor_get_uint64(v_key_2205_, sizeof(void*)*2);
v___y_2213_ = v_hash_2232_;
goto v___jp_2212_;
}
v___jp_2212_:
{
uint64_t v___x_2214_; uint64_t v___x_2215_; uint64_t v_fold_2216_; uint64_t v___x_2217_; uint64_t v___x_2218_; uint64_t v___x_2219_; size_t v___x_2220_; size_t v___x_2221_; size_t v___x_2222_; size_t v___x_2223_; size_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2214_ = 32ULL;
v___x_2215_ = lean_uint64_shift_right(v___y_2213_, v___x_2214_);
v_fold_2216_ = lean_uint64_xor(v___y_2213_, v___x_2215_);
v___x_2217_ = 16ULL;
v___x_2218_ = lean_uint64_shift_right(v_fold_2216_, v___x_2217_);
v___x_2219_ = lean_uint64_xor(v_fold_2216_, v___x_2218_);
v___x_2220_ = lean_uint64_to_usize(v___x_2219_);
v___x_2221_ = lean_usize_of_nat(v___x_2211_);
v___x_2222_ = ((size_t)1ULL);
v___x_2223_ = lean_usize_sub(v___x_2221_, v___x_2222_);
v___x_2224_ = lean_usize_land(v___x_2220_, v___x_2223_);
v___x_2225_ = lean_array_uget_borrowed(v_x_2203_, v___x_2224_);
lean_inc(v___x_2225_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 2, v___x_2225_);
v___x_2227_ = v___x_2209_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_key_2205_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_value_2206_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_array_uset(v_x_2203_, v___x_2224_, v___x_2227_);
v_x_2203_ = v___x_2228_;
v_x_2204_ = v_tail_2207_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object* v_i_2234_, lean_object* v_source_2235_, lean_object* v_target_2236_){
_start:
{
lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = lean_array_get_size(v_source_2235_);
v___x_2238_ = lean_nat_dec_lt(v_i_2234_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_dec_ref(v_source_2235_);
lean_dec(v_i_2234_);
return v_target_2236_;
}
else
{
lean_object* v_es_2239_; lean_object* v___x_2240_; lean_object* v_source_2241_; lean_object* v_target_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_es_2239_ = lean_array_fget(v_source_2235_, v_i_2234_);
v___x_2240_ = lean_box(0);
v_source_2241_ = lean_array_fset(v_source_2235_, v_i_2234_, v___x_2240_);
v_target_2242_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_2236_, v_es_2239_);
v___x_2243_ = lean_unsigned_to_nat(1u);
v___x_2244_ = lean_nat_add(v_i_2234_, v___x_2243_);
lean_dec(v_i_2234_);
v_i_2234_ = v___x_2244_;
v_source_2235_ = v_source_2241_;
v_target_2236_ = v_target_2242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object* v_data_2246_){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_nbuckets_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2247_ = lean_array_get_size(v_data_2246_);
v___x_2248_ = lean_unsigned_to_nat(2u);
v_nbuckets_2249_ = lean_nat_mul(v___x_2247_, v___x_2248_);
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_mk_array(v_nbuckets_2249_, v___x_2251_);
v___x_2253_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_2250_, v_data_2246_, v___x_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object* v_m_2254_, lean_object* v_a_2255_, lean_object* v_b_2256_){
_start:
{
lean_object* v_size_2257_; lean_object* v_buckets_2258_; lean_object* v___x_2259_; uint64_t v___y_2261_; 
v_size_2257_ = lean_ctor_get(v_m_2254_, 0);
v_buckets_2258_ = lean_ctor_get(v_m_2254_, 1);
v___x_2259_ = lean_array_get_size(v_buckets_2258_);
if (lean_obj_tag(v_a_2255_) == 0)
{
uint64_t v___x_2298_; 
v___x_2298_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2261_ = v___x_2298_;
goto v___jp_2260_;
}
else
{
uint64_t v_hash_2299_; 
v_hash_2299_ = lean_ctor_get_uint64(v_a_2255_, sizeof(void*)*2);
v___y_2261_ = v_hash_2299_;
goto v___jp_2260_;
}
v___jp_2260_:
{
uint64_t v___x_2262_; uint64_t v___x_2263_; uint64_t v_fold_2264_; uint64_t v___x_2265_; uint64_t v___x_2266_; uint64_t v___x_2267_; size_t v___x_2268_; size_t v___x_2269_; size_t v___x_2270_; size_t v___x_2271_; size_t v___x_2272_; lean_object* v_bkt_2273_; uint8_t v___x_2274_; 
v___x_2262_ = 32ULL;
v___x_2263_ = lean_uint64_shift_right(v___y_2261_, v___x_2262_);
v_fold_2264_ = lean_uint64_xor(v___y_2261_, v___x_2263_);
v___x_2265_ = 16ULL;
v___x_2266_ = lean_uint64_shift_right(v_fold_2264_, v___x_2265_);
v___x_2267_ = lean_uint64_xor(v_fold_2264_, v___x_2266_);
v___x_2268_ = lean_uint64_to_usize(v___x_2267_);
v___x_2269_ = lean_usize_of_nat(v___x_2259_);
v___x_2270_ = ((size_t)1ULL);
v___x_2271_ = lean_usize_sub(v___x_2269_, v___x_2270_);
v___x_2272_ = lean_usize_land(v___x_2268_, v___x_2271_);
v_bkt_2273_ = lean_array_uget_borrowed(v_buckets_2258_, v___x_2272_);
v___x_2274_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_2255_, v_bkt_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2295_; 
lean_inc_ref(v_buckets_2258_);
lean_inc(v_size_2257_);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_m_2254_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; lean_object* v_unused_2297_; 
v_unused_2296_ = lean_ctor_get(v_m_2254_, 1);
lean_dec(v_unused_2296_);
v_unused_2297_ = lean_ctor_get(v_m_2254_, 0);
lean_dec(v_unused_2297_);
v___x_2276_ = v_m_2254_;
v_isShared_2277_ = v_isSharedCheck_2295_;
goto v_resetjp_2275_;
}
else
{
lean_dec(v_m_2254_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2295_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v_size_x27_2279_; lean_object* v___x_2280_; lean_object* v_buckets_x27_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2278_ = lean_unsigned_to_nat(1u);
v_size_x27_2279_ = lean_nat_add(v_size_2257_, v___x_2278_);
lean_dec(v_size_2257_);
lean_inc(v_bkt_2273_);
v___x_2280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2280_, 0, v_a_2255_);
lean_ctor_set(v___x_2280_, 1, v_b_2256_);
lean_ctor_set(v___x_2280_, 2, v_bkt_2273_);
v_buckets_x27_2281_ = lean_array_uset(v_buckets_2258_, v___x_2272_, v___x_2280_);
v___x_2282_ = lean_unsigned_to_nat(4u);
v___x_2283_ = lean_nat_mul(v_size_x27_2279_, v___x_2282_);
v___x_2284_ = lean_unsigned_to_nat(3u);
v___x_2285_ = lean_nat_div(v___x_2283_, v___x_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_array_get_size(v_buckets_x27_2281_);
v___x_2287_ = lean_nat_dec_le(v___x_2285_, v___x_2286_);
lean_dec(v___x_2285_);
if (v___x_2287_ == 0)
{
lean_object* v_val_2288_; lean_object* v___x_2290_; 
v_val_2288_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_2281_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 1, v_val_2288_);
lean_ctor_set(v___x_2276_, 0, v_size_x27_2279_);
v___x_2290_ = v___x_2276_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_size_x27_2279_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_val_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
else
{
lean_object* v___x_2293_; 
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 1, v_buckets_x27_2281_);
lean_ctor_set(v___x_2276_, 0, v_size_x27_2279_);
v___x_2293_ = v___x_2276_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_size_x27_2279_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_buckets_x27_2281_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_dec(v_b_2256_);
lean_dec(v_a_2255_);
return v_m_2254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object* v_traceClassName_2303_, uint8_t v_inherited_2304_, lean_object* v_ref_2305_){
_start:
{
lean_object* v___x_2307_; lean_object* v_optionName_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2307_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v_optionName_2308_ = l_Lean_Name_append(v___x_2307_, v_traceClassName_2303_);
v___x_2309_ = ((lean_object*)(l_Lean_registerTraceClass___closed__0));
v___x_2310_ = ((lean_object*)(l_Lean_registerTraceClass___closed__1));
v___x_2311_ = lean_box(0);
lean_inc_n(v_optionName_2308_, 2);
v___x_2312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2312_, 0, v_optionName_2308_);
lean_ctor_set(v___x_2312_, 1, v_ref_2305_);
lean_ctor_set(v___x_2312_, 2, v___x_2309_);
lean_ctor_set(v___x_2312_, 3, v___x_2310_);
lean_ctor_set(v___x_2312_, 4, v___x_2311_);
v___x_2313_ = lean_register_option(v_optionName_2308_, v___x_2312_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2329_; 
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v___x_2313_, 0);
lean_dec(v_unused_2330_);
v___x_2315_ = v___x_2313_;
v_isShared_2316_ = v_isSharedCheck_2329_;
goto v_resetjp_2314_;
}
else
{
lean_dec(v___x_2313_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2329_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
if (v_inherited_2304_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
lean_dec(v_optionName_2308_);
v___x_2317_ = lean_box(0);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2317_);
v___x_2319_ = v___x_2315_;
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
else
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2321_ = l_Lean_inheritedTraceOptions;
v___x_2322_ = lean_st_ref_take(v___x_2321_);
v___x_2323_ = lean_box(0);
v___x_2324_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2322_, v_optionName_2308_, v___x_2323_);
v___x_2325_ = lean_st_ref_set(v___x_2321_, v___x_2324_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2325_);
v___x_2327_ = v___x_2315_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_dec(v_optionName_2308_);
return v___x_2313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object* v_traceClassName_2331_, lean_object* v_inherited_2332_, lean_object* v_ref_2333_, lean_object* v_a_2334_){
_start:
{
uint8_t v_inherited_boxed_2335_; lean_object* v_res_2336_; 
v_inherited_boxed_2335_ = lean_unbox(v_inherited_2332_);
v_res_2336_ = l_Lean_registerTraceClass(v_traceClassName_2331_, v_inherited_boxed_2335_, v_ref_2333_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(lean_object* v_00_u03b2_2337_, lean_object* v_m_2338_, lean_object* v_a_2339_, lean_object* v_b_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v_m_2338_, v_a_2339_, v_b_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object* v_00_u03b2_2342_, lean_object* v_data_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_data_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2345_, lean_object* v_i_2346_, lean_object* v_source_2347_, lean_object* v_target_2348_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_i_2346_, v_source_2347_, v_target_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2351_, v_x_2352_);
return v___x_2353_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_2364_ = l_String_toRawSubstring_x27(v___x_2363_);
return v___x_2364_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12));
v___x_2370_ = l_String_toRawSubstring_x27(v___x_2369_);
return v___x_2370_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18));
v___x_2377_ = l_String_toRawSubstring_x27(v___x_2376_);
return v___x_2377_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31(void){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Array_mkArray0(lean_box(0));
return v___x_2405_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40));
v___x_2432_ = l_String_toRawSubstring_x27(v___x_2431_);
return v___x_2432_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57));
v___x_2468_ = l_String_toRawSubstring_x27(v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object* v_id_2490_, lean_object* v_s_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v_msg_2590_; lean_object* v_quotContext_2591_; lean_object* v_currMacroScope_2592_; lean_object* v_ref_2593_; lean_object* v___y_2594_; lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
lean_inc(v_s_2491_);
v___x_2640_ = l_Lean_Syntax_getKind(v_s_2491_);
v___x_2641_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49));
v___x_2642_ = lean_name_eq(v___x_2640_, v___x_2641_);
lean_dec(v___x_2640_);
if (v___x_2642_ == 0)
{
lean_object* v_quotContext_2643_; lean_object* v_currMacroScope_2644_; lean_object* v_ref_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v_quotContext_2643_ = lean_ctor_get(v_a_2492_, 1);
v_currMacroScope_2644_ = lean_ctor_get(v_a_2492_, 2);
v_ref_2645_ = lean_ctor_get(v_a_2492_, 5);
v___x_2646_ = l_Lean_SourceInfo_fromRef(v_ref_2645_, v___x_2642_);
v___x_2647_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51));
v___x_2648_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52));
v___x_2649_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
lean_inc_n(v___x_2646_, 8);
v___x_2650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2646_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2652_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2653_ = lean_box(0);
lean_inc_n(v_currMacroScope_2644_, 3);
lean_inc_n(v_quotContext_2643_, 3);
v___x_2654_ = l_Lean_addMacroScope(v_quotContext_2643_, v___x_2653_, v_currMacroScope_2644_);
v___x_2655_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55));
v___x_2656_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2646_);
lean_ctor_set(v___x_2656_, 1, v___x_2652_);
lean_ctor_set(v___x_2656_, 2, v___x_2654_);
lean_ctor_set(v___x_2656_, 3, v___x_2655_);
v___x_2657_ = l_Lean_Syntax_node1(v___x_2646_, v___x_2651_, v___x_2656_);
v___x_2658_ = l_Lean_Syntax_node2(v___x_2646_, v___x_2648_, v___x_2650_, v___x_2657_);
v___x_2659_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56));
v___x_2660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2646_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
v___x_2661_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2662_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58);
v___x_2663_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59));
v___x_2664_ = l_Lean_addMacroScope(v_quotContext_2643_, v___x_2663_, v_currMacroScope_2644_);
v___x_2665_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64));
v___x_2666_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2646_);
lean_ctor_set(v___x_2666_, 1, v___x_2662_);
lean_ctor_set(v___x_2666_, 2, v___x_2664_);
lean_ctor_set(v___x_2666_, 3, v___x_2665_);
v___x_2667_ = l_Lean_Syntax_node1(v___x_2646_, v___x_2661_, v___x_2666_);
v___x_2668_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2646_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = l_Lean_Syntax_node5(v___x_2646_, v___x_2647_, v___x_2658_, v_s_2491_, v___x_2660_, v___x_2667_, v___x_2669_);
v_msg_2590_ = v___x_2670_;
v_quotContext_2591_ = v_quotContext_2643_;
v_currMacroScope_2592_ = v_currMacroScope_2644_;
v_ref_2593_ = v_ref_2645_;
v___y_2594_ = v_a_2493_;
goto v___jp_2589_;
}
else
{
lean_object* v_quotContext_2671_; lean_object* v_currMacroScope_2672_; lean_object* v_ref_2673_; uint8_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v_quotContext_2671_ = lean_ctor_get(v_a_2492_, 1);
v_currMacroScope_2672_ = lean_ctor_get(v_a_2492_, 2);
v_ref_2673_ = lean_ctor_get(v_a_2492_, 5);
v___x_2674_ = 0;
v___x_2675_ = l_Lean_SourceInfo_fromRef(v_ref_2673_, v___x_2674_);
v___x_2676_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66));
v___x_2677_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67));
lean_inc(v___x_2675_);
v___x_2678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2675_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = l_Lean_Syntax_node2(v___x_2675_, v___x_2676_, v___x_2678_, v_s_2491_);
lean_inc(v_currMacroScope_2672_);
lean_inc(v_quotContext_2671_);
v_msg_2590_ = v___x_2679_;
v_quotContext_2591_ = v_quotContext_2671_;
v_currMacroScope_2592_ = v_currMacroScope_2672_;
v_ref_2593_ = v_ref_2673_;
v___y_2594_ = v_a_2493_;
goto v___jp_2589_;
}
v___jp_2494_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_inc_n(v___y_2505_, 8);
lean_inc(v___y_2496_);
lean_inc_n(v___y_2500_, 29);
v___x_2519_ = l_Lean_Syntax_node5(v___y_2500_, v___y_2496_, v___y_2497_, v___y_2505_, v___y_2505_, v___y_2512_, v___y_2518_);
lean_inc(v___y_2501_);
v___x_2520_ = l_Lean_Syntax_node1(v___y_2500_, v___y_2501_, v___x_2519_);
lean_inc(v___y_2502_);
v___x_2521_ = l_Lean_Syntax_node4(v___y_2500_, v___y_2502_, v___y_2514_, v___y_2505_, v___y_2515_, v___x_2520_);
lean_inc_n(v___y_2516_, 3);
v___x_2522_ = l_Lean_Syntax_node2(v___y_2500_, v___y_2516_, v___x_2521_, v___y_2505_);
v___x_2523_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0));
lean_inc_ref_n(v___y_2503_, 7);
lean_inc_ref_n(v___y_2513_, 7);
lean_inc_ref_n(v___y_2504_, 10);
v___x_2524_ = l_Lean_Name_mkStr4(v___y_2504_, v___y_2513_, v___y_2503_, v___x_2523_);
v___x_2525_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1));
v___x_2526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___y_2500_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2));
v___x_2528_ = l_Lean_Name_mkStr4(v___y_2504_, v___y_2513_, v___y_2503_, v___x_2527_);
v___x_2529_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3));
v___x_2530_ = l_Lean_Name_mkStr4(v___y_2504_, v___y_2513_, v___y_2503_, v___x_2529_);
v___x_2531_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4));
v___x_2532_ = l_Lean_Name_mkStr4(v___y_2504_, v___y_2513_, v___y_2503_, v___x_2531_);
v___x_2533_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
v___x_2534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___y_2500_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2536_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2537_ = lean_box(0);
lean_inc_n(v___y_2510_, 2);
lean_inc_n(v___y_2498_, 2);
v___x_2538_ = l_Lean_addMacroScope(v___y_2498_, v___x_2537_, v___y_2510_);
v___x_2539_ = l_Lean_Name_mkStr1(v___y_2504_);
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
lean_inc_n(v___y_2511_, 2);
v___x_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v___y_2511_);
v___x_2542_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2542_, 0, v___y_2500_);
lean_ctor_set(v___x_2542_, 1, v___x_2536_);
lean_ctor_set(v___x_2542_, 2, v___x_2538_);
lean_ctor_set(v___x_2542_, 3, v___x_2541_);
v___x_2543_ = l_Lean_Syntax_node1(v___y_2500_, v___x_2535_, v___x_2542_);
v___x_2544_ = l_Lean_Syntax_node2(v___y_2500_, v___x_2532_, v___x_2534_, v___x_2543_);
v___x_2545_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9));
v___x_2546_ = l_Lean_Name_mkStr4(v___y_2504_, v___y_2513_, v___y_2503_, v___x_2545_);
v___x_2547_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10));
v___x_2548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___y_2500_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11));
v___x_2550_ = l_Lean_Name_mkStr4(v___y_2504_, v___y_2513_, v___y_2503_, v___x_2549_);
v___x_2551_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13);
v___x_2552_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14));
v___x_2553_ = l_Lean_Name_mkStr2(v___y_2504_, v___x_2552_);
lean_inc(v___x_2553_);
v___x_2554_ = l_Lean_addMacroScope(v___y_2498_, v___x_2553_, v___y_2510_);
v___x_2555_ = lean_box(0);
v___x_2556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2553_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v___y_2511_);
v___x_2558_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2558_, 0, v___y_2500_);
lean_ctor_set(v___x_2558_, 1, v___x_2551_);
lean_ctor_set(v___x_2558_, 2, v___x_2554_);
lean_ctor_set(v___x_2558_, 3, v___x_2557_);
lean_inc(v___y_2499_);
lean_inc_n(v___y_2495_, 4);
v___x_2559_ = l_Lean_Syntax_node1(v___y_2500_, v___y_2495_, v___y_2499_);
lean_inc(v___x_2550_);
v___x_2560_ = l_Lean_Syntax_node2(v___y_2500_, v___x_2550_, v___x_2558_, v___x_2559_);
v___x_2561_ = l_Lean_Syntax_node2(v___y_2500_, v___x_2546_, v___x_2548_, v___x_2560_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___y_2500_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = l_Lean_Syntax_node3(v___y_2500_, v___x_2530_, v___x_2544_, v___x_2561_, v___x_2563_);
v___x_2565_ = l_Lean_Syntax_node2(v___y_2500_, v___x_2528_, v___y_2505_, v___x_2564_);
v___x_2566_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___y_2500_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17));
v___x_2569_ = l_Lean_Name_mkStr4(v___y_2504_, v___y_2513_, v___y_2503_, v___x_2568_);
v___x_2570_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19);
v___x_2571_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20));
v___x_2572_ = l_Lean_Name_mkStr2(v___y_2504_, v___x_2571_);
lean_inc(v___x_2572_);
v___x_2573_ = l_Lean_addMacroScope(v___y_2498_, v___x_2572_, v___y_2510_);
v___x_2574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2555_);
v___x_2575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___y_2511_);
v___x_2576_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2576_, 0, v___y_2500_);
lean_ctor_set(v___x_2576_, 1, v___x_2570_);
lean_ctor_set(v___x_2576_, 2, v___x_2573_);
lean_ctor_set(v___x_2576_, 3, v___x_2575_);
v___x_2577_ = l_Lean_Syntax_node2(v___y_2500_, v___y_2495_, v___y_2499_, v___y_2508_);
v___x_2578_ = l_Lean_Syntax_node2(v___y_2500_, v___x_2550_, v___x_2576_, v___x_2577_);
v___x_2579_ = l_Lean_Syntax_node1(v___y_2500_, v___x_2569_, v___x_2578_);
v___x_2580_ = l_Lean_Syntax_node2(v___y_2500_, v___y_2516_, v___x_2579_, v___y_2505_);
v___x_2581_ = l_Lean_Syntax_node1(v___y_2500_, v___y_2495_, v___x_2580_);
lean_inc_n(v___y_2507_, 2);
v___x_2582_ = l_Lean_Syntax_node1(v___y_2500_, v___y_2507_, v___x_2581_);
v___x_2583_ = l_Lean_Syntax_node6(v___y_2500_, v___x_2524_, v___x_2526_, v___x_2565_, v___x_2567_, v___x_2582_, v___y_2505_, v___y_2505_);
v___x_2584_ = l_Lean_Syntax_node2(v___y_2500_, v___y_2516_, v___x_2583_, v___y_2505_);
v___x_2585_ = l_Lean_Syntax_node2(v___y_2500_, v___y_2495_, v___x_2522_, v___x_2584_);
v___x_2586_ = l_Lean_Syntax_node1(v___y_2500_, v___y_2507_, v___x_2585_);
lean_inc(v___y_2517_);
v___x_2587_ = l_Lean_Syntax_node2(v___y_2500_, v___y_2517_, v___y_2509_, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___y_2506_);
return v___x_2588_;
}
v___jp_2589_:
{
uint8_t v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2595_ = 0;
v___x_2596_ = l_Lean_SourceInfo_fromRef(v_ref_2593_, v___x_2595_);
v___x_2597_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0));
v___x_2598_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1));
v___x_2599_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__0));
v___x_2600_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22));
v___x_2601_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23));
lean_inc_n(v___x_2596_, 7);
v___x_2602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2596_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25));
v___x_2604_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2605_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27));
v___x_2606_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2607_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
v___x_2608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2596_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31);
v___x_2610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2596_);
lean_ctor_set(v___x_2610_, 1, v___x_2604_);
lean_ctor_set(v___x_2610_, 2, v___x_2609_);
v___x_2611_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33));
lean_inc_ref(v___x_2610_);
v___x_2612_ = l_Lean_Syntax_node1(v___x_2596_, v___x_2611_, v___x_2610_);
v___x_2613_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35));
v___x_2614_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37));
v___x_2615_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39));
v___x_2616_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41);
v___x_2617_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42));
lean_inc(v_currMacroScope_2592_);
lean_inc(v_quotContext_2591_);
v___x_2618_ = l_Lean_addMacroScope(v_quotContext_2591_, v___x_2617_, v_currMacroScope_2592_);
v___x_2619_ = lean_box(0);
v___x_2620_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2596_);
lean_ctor_set(v___x_2620_, 1, v___x_2616_);
lean_ctor_set(v___x_2620_, 2, v___x_2618_);
lean_ctor_set(v___x_2620_, 3, v___x_2619_);
lean_inc_ref(v___x_2620_);
v___x_2621_ = l_Lean_Syntax_node1(v___x_2596_, v___x_2615_, v___x_2620_);
v___x_2622_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43));
v___x_2623_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2596_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = l_Lean_Syntax_getId(v_id_2490_);
v___x_2625_ = lean_erase_macro_scopes(v___x_2624_);
lean_inc(v___x_2625_);
v___x_2626_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2619_, v___x_2625_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_quoteNameMk(v___x_2625_);
v___y_2495_ = v___x_2604_;
v___y_2496_ = v___x_2614_;
v___y_2497_ = v___x_2621_;
v___y_2498_ = v_quotContext_2591_;
v___y_2499_ = v___x_2620_;
v___y_2500_ = v___x_2596_;
v___y_2501_ = v___x_2613_;
v___y_2502_ = v___x_2606_;
v___y_2503_ = v___x_2599_;
v___y_2504_ = v___x_2597_;
v___y_2505_ = v___x_2610_;
v___y_2506_ = v___y_2594_;
v___y_2507_ = v___x_2603_;
v___y_2508_ = v_msg_2590_;
v___y_2509_ = v___x_2602_;
v___y_2510_ = v_currMacroScope_2592_;
v___y_2511_ = v___x_2619_;
v___y_2512_ = v___x_2623_;
v___y_2513_ = v___x_2598_;
v___y_2514_ = v___x_2608_;
v___y_2515_ = v___x_2612_;
v___y_2516_ = v___x_2605_;
v___y_2517_ = v___x_2600_;
v___y_2518_ = v___x_2627_;
goto v___jp_2494_;
}
else
{
lean_object* v_val_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_dec(v___x_2625_);
v_val_2628_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_val_2628_);
lean_dec_ref(v___x_2626_);
v___x_2629_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45));
v___x_2630_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46));
v___x_2631_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47));
v___x_2632_ = lean_string_intercalate(v___x_2631_, v_val_2628_);
v___x_2633_ = lean_string_append(v___x_2630_, v___x_2632_);
lean_dec_ref(v___x_2632_);
v___x_2634_ = lean_box(2);
v___x_2635_ = l_Lean_Syntax_mkNameLit(v___x_2633_, v___x_2634_);
v___x_2636_ = lean_unsigned_to_nat(1u);
v___x_2637_ = lean_mk_empty_array_with_capacity(v___x_2636_);
v___x_2638_ = lean_array_push(v___x_2637_, v___x_2635_);
v___x_2639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2634_);
lean_ctor_set(v___x_2639_, 1, v___x_2629_);
lean_ctor_set(v___x_2639_, 2, v___x_2638_);
v___y_2495_ = v___x_2604_;
v___y_2496_ = v___x_2614_;
v___y_2497_ = v___x_2621_;
v___y_2498_ = v_quotContext_2591_;
v___y_2499_ = v___x_2620_;
v___y_2500_ = v___x_2596_;
v___y_2501_ = v___x_2613_;
v___y_2502_ = v___x_2606_;
v___y_2503_ = v___x_2599_;
v___y_2504_ = v___x_2597_;
v___y_2505_ = v___x_2610_;
v___y_2506_ = v___y_2594_;
v___y_2507_ = v___x_2603_;
v___y_2508_ = v_msg_2590_;
v___y_2509_ = v___x_2602_;
v___y_2510_ = v_currMacroScope_2592_;
v___y_2511_ = v___x_2619_;
v___y_2512_ = v___x_2623_;
v___y_2513_ = v___x_2598_;
v___y_2514_ = v___x_2608_;
v___y_2515_ = v___x_2612_;
v___y_2516_ = v___x_2605_;
v___y_2517_ = v___x_2600_;
v___y_2518_ = v___x_2639_;
goto v___jp_2494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object* v_id_2680_, lean_object* v_s_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v_id_2680_, v_s_2681_, v_a_2682_, v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_id_2680_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object* v_x_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = ((lean_object*)(l_Lean_doElemTrace_x5b___x5d_____00__closed__1));
lean_inc(v_x_2739_);
v___x_2743_ = l_Lean_Syntax_isOfKind(v_x_2739_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec(v_x_2739_);
v___x_2744_ = lean_box(1);
v___x_2745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
lean_ctor_set(v___x_2745_, 1, v_a_2741_);
return v___x_2745_;
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v_a_2751_; lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
v___x_2746_ = lean_unsigned_to_nat(1u);
v___x_2747_ = l_Lean_Syntax_getArg(v_x_2739_, v___x_2746_);
v___x_2748_ = lean_unsigned_to_nat(3u);
v___x_2749_ = l_Lean_Syntax_getArg(v_x_2739_, v___x_2748_);
lean_dec(v_x_2739_);
v___x_2750_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v___x_2747_, v___x_2749_, v_a_2740_, v_a_2741_);
lean_dec(v___x_2747_);
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_a_2752_ = lean_ctor_get(v___x_2750_, 1);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2750_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2751_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object* v_x_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(v_x_2760_, v_a_2761_, v_a_2762_);
lean_dec_ref(v_a_2761_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object* v_inst_2764_, lean_object* v_inst_2765_, lean_object* v_inst_2766_, lean_object* v_inst_2767_, lean_object* v_always_2768_, lean_object* v_inst_2769_, lean_object* v_cls_2770_, uint8_t v_collapsed_2771_, lean_object* v_tag_2772_, lean_object* v_opts_2773_, uint8_t v_clsEnabled_2774_, lean_object* v_oldTraces_2775_, lean_object* v_ref_2776_, lean_object* v_msg_2777_, lean_object* v_resStartStop_2778_){
_start:
{
lean_object* v___x_2779_; lean_object* v_snd_2780_; lean_object* v_fst_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2847_; 
v___x_2779_ = l_Lean_KVMap_instValueBool;
v_snd_2780_ = lean_ctor_get(v_resStartStop_2778_, 1);
v_fst_2781_ = lean_ctor_get(v_resStartStop_2778_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_resStartStop_2778_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2783_ = v_resStartStop_2778_;
v_isShared_2784_ = v_isSharedCheck_2847_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_snd_2780_);
lean_inc(v_fst_2781_);
lean_dec(v_resStartStop_2778_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2847_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v_fst_2785_; lean_object* v_snd_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2846_; 
v_fst_2785_ = lean_ctor_get(v_snd_2780_, 0);
v_snd_2786_ = lean_ctor_get(v_snd_2780_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_snd_2780_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2788_ = v_snd_2780_;
v_isShared_2789_ = v_isSharedCheck_2846_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_snd_2786_);
lean_inc(v_fst_2785_);
lean_dec(v_snd_2780_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2846_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___f_2790_; lean_object* v___f_2791_; lean_object* v___y_2793_; lean_object* v_data_2794_; lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___y_2820_; double v___y_2826_; uint8_t v___x_2831_; 
lean_inc_ref(v_oldTraces_2775_);
v___f_2790_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2790_, 0, v_oldTraces_2775_);
lean_inc(v_fst_2781_);
lean_inc_ref(v_inst_2764_);
v___f_2791_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2791_, 0, v_always_2768_);
lean_closure_set(v___f_2791_, 1, v_inst_2764_);
lean_closure_set(v___f_2791_, 2, v_fst_2781_);
v___x_2798_ = l_Lean_trace_profiler;
v___x_2799_ = l_Lean_Option_get___redArg(v___x_2779_, v_opts_2773_, v___x_2798_);
v___x_2831_ = lean_unbox(v___x_2799_);
if (v___x_2831_ == 0)
{
uint8_t v___x_2832_; 
v___x_2832_ = lean_unbox(v___x_2799_);
v___y_2820_ = v___x_2832_;
goto v___jp_2819_;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2833_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2834_ = l_Lean_Option_get___redArg(v___x_2779_, v_opts_2773_, v___x_2833_);
v___x_2835_ = lean_unbox(v___x_2834_);
lean_dec(v___x_2834_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; double v___x_2839_; double v___x_2840_; double v___x_2841_; 
v___x_2836_ = l_Lean_KVMap_instValueNat;
v___x_2837_ = l_Lean_trace_profiler_threshold;
v___x_2838_ = l_Lean_Option_get___redArg(v___x_2836_, v_opts_2773_, v___x_2837_);
v___x_2839_ = lean_float_of_nat(v___x_2838_);
v___x_2840_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_2841_ = lean_float_div(v___x_2839_, v___x_2840_);
v___y_2826_ = v___x_2841_;
goto v___jp_2825_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; double v___x_2845_; 
v___x_2842_ = l_Lean_KVMap_instValueNat;
v___x_2843_ = l_Lean_trace_profiler_threshold;
v___x_2844_ = l_Lean_Option_get___redArg(v___x_2842_, v_opts_2773_, v___x_2843_);
v___x_2845_ = lean_float_of_nat(v___x_2844_);
v___y_2826_ = v___x_2845_;
goto v___jp_2825_;
}
}
v___jp_2792_:
{
lean_object* v_toBind_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_toBind_2795_ = lean_ctor_get(v_inst_2764_, 1);
lean_inc(v_toBind_2795_);
v___x_2796_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_2764_, v_inst_2765_, v_inst_2766_, v_inst_2767_, v_oldTraces_2775_, v_data_2794_, v_ref_2776_, v___y_2793_);
v___x_2797_ = lean_apply_4(v_toBind_2795_, lean_box(0), lean_box(0), v___x_2796_, v___f_2791_);
return v___x_2797_;
}
v___jp_2800_:
{
lean_object* v_result_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
v_result_2801_ = lean_apply_1(v_inst_2769_, v_fst_2781_);
v___x_2802_ = lean_unbox(v_result_2801_);
v___x_2803_ = l_Lean_TraceResult_toEmoji(v___x_2802_);
v___x_2804_ = l_Lean_stringToMessageData(v___x_2803_);
v___x_2805_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
if (v_isShared_2789_ == 0)
{
lean_ctor_set_tag(v___x_2788_, 7);
lean_ctor_set(v___x_2788_, 1, v___x_2805_);
lean_ctor_set(v___x_2788_, 0, v___x_2804_);
v___x_2807_ = v___x_2788_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v_msg_2809_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set_tag(v___x_2783_, 7);
lean_ctor_set(v___x_2783_, 1, v_msg_2777_);
lean_ctor_set(v___x_2783_, 0, v___x_2807_);
v_msg_2809_ = v___x_2783_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_msg_2777_);
v_msg_2809_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; double v___x_2811_; lean_object* v_data_2812_; uint8_t v___x_2813_; 
v___x_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_result_2801_);
v___x_2811_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_2772_);
lean_inc_ref(v___x_2810_);
lean_inc(v_cls_2770_);
v_data_2812_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2812_, 0, v_cls_2770_);
lean_ctor_set(v_data_2812_, 1, v___x_2810_);
lean_ctor_set(v_data_2812_, 2, v_tag_2772_);
lean_ctor_set_float(v_data_2812_, sizeof(void*)*3, v___x_2811_);
lean_ctor_set_float(v_data_2812_, sizeof(void*)*3 + 8, v___x_2811_);
lean_ctor_set_uint8(v_data_2812_, sizeof(void*)*3 + 16, v_collapsed_2771_);
v___x_2813_ = lean_unbox(v___x_2799_);
lean_dec(v___x_2799_);
if (v___x_2813_ == 0)
{
lean_dec_ref(v___x_2810_);
lean_dec(v_snd_2786_);
lean_dec(v_fst_2785_);
lean_dec_ref(v_tag_2772_);
lean_dec(v_cls_2770_);
v___y_2793_ = v_msg_2809_;
v_data_2794_ = v_data_2812_;
goto v___jp_2792_;
}
else
{
lean_object* v_data_2814_; double v___x_2815_; double v___x_2816_; 
lean_dec_ref(v_data_2812_);
v_data_2814_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2814_, 0, v_cls_2770_);
lean_ctor_set(v_data_2814_, 1, v___x_2810_);
lean_ctor_set(v_data_2814_, 2, v_tag_2772_);
v___x_2815_ = lean_unbox_float(v_fst_2785_);
lean_dec(v_fst_2785_);
lean_ctor_set_float(v_data_2814_, sizeof(void*)*3, v___x_2815_);
v___x_2816_ = lean_unbox_float(v_snd_2786_);
lean_dec(v_snd_2786_);
lean_ctor_set_float(v_data_2814_, sizeof(void*)*3 + 8, v___x_2816_);
lean_ctor_set_uint8(v_data_2814_, sizeof(void*)*3 + 16, v_collapsed_2771_);
v___y_2793_ = v_msg_2809_;
v_data_2794_ = v_data_2814_;
goto v___jp_2792_;
}
}
}
}
v___jp_2819_:
{
if (v_clsEnabled_2774_ == 0)
{
if (v___y_2820_ == 0)
{
lean_object* v_toBind_2821_; lean_object* v_modifyTraceState_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec(v___x_2799_);
lean_del_object(v___x_2788_);
lean_dec(v_snd_2786_);
lean_dec(v_fst_2785_);
lean_del_object(v___x_2783_);
lean_dec(v_fst_2781_);
lean_dec_ref(v_msg_2777_);
lean_dec(v_ref_2776_);
lean_dec_ref(v_oldTraces_2775_);
lean_dec_ref(v_tag_2772_);
lean_dec(v_cls_2770_);
lean_dec_ref(v_inst_2769_);
lean_dec(v_inst_2767_);
lean_dec_ref(v_inst_2766_);
v_toBind_2821_ = lean_ctor_get(v_inst_2764_, 1);
lean_inc(v_toBind_2821_);
lean_dec_ref(v_inst_2764_);
v_modifyTraceState_2822_ = lean_ctor_get(v_inst_2765_, 0);
lean_inc(v_modifyTraceState_2822_);
lean_dec_ref(v_inst_2765_);
v___x_2823_ = lean_apply_1(v_modifyTraceState_2822_, v___f_2790_);
v___x_2824_ = lean_apply_4(v_toBind_2821_, lean_box(0), lean_box(0), v___x_2823_, v___f_2791_);
return v___x_2824_;
}
else
{
lean_dec_ref(v___f_2790_);
goto v___jp_2800_;
}
}
else
{
lean_dec_ref(v___f_2790_);
goto v___jp_2800_;
}
}
v___jp_2825_:
{
double v___x_2827_; double v___x_2828_; double v___x_2829_; uint8_t v___x_2830_; 
v___x_2827_ = lean_unbox_float(v_snd_2786_);
v___x_2828_ = lean_unbox_float(v_fst_2785_);
v___x_2829_ = lean_float_sub(v___x_2827_, v___x_2828_);
v___x_2830_ = lean_float_decLt(v___y_2826_, v___x_2829_);
v___y_2820_ = v___x_2830_;
goto v___jp_2819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_, lean_object* v_always_2852_, lean_object* v_inst_2853_, lean_object* v_cls_2854_, lean_object* v_collapsed_2855_, lean_object* v_tag_2856_, lean_object* v_opts_2857_, lean_object* v_clsEnabled_2858_, lean_object* v_oldTraces_2859_, lean_object* v_ref_2860_, lean_object* v_msg_2861_, lean_object* v_resStartStop_2862_){
_start:
{
uint8_t v_collapsed_boxed_2863_; uint8_t v_clsEnabled_boxed_2864_; lean_object* v_res_2865_; 
v_collapsed_boxed_2863_ = lean_unbox(v_collapsed_2855_);
v_clsEnabled_boxed_2864_ = lean_unbox(v_clsEnabled_2858_);
v_res_2865_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2848_, v_inst_2849_, v_inst_2850_, v_inst_2851_, v_always_2852_, v_inst_2853_, v_cls_2854_, v_collapsed_boxed_2863_, v_tag_2856_, v_opts_2857_, v_clsEnabled_boxed_2864_, v_oldTraces_2859_, v_ref_2860_, v_msg_2861_, v_resStartStop_2862_);
lean_dec_ref(v_opts_2857_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object* v_00_u03b1_2866_, lean_object* v_m_2867_, lean_object* v_inst_2868_, lean_object* v_inst_2869_, lean_object* v_00_u03b5_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_always_2873_, lean_object* v_inst_2874_, lean_object* v_cls_2875_, uint8_t v_collapsed_2876_, lean_object* v_tag_2877_, lean_object* v_opts_2878_, uint8_t v_clsEnabled_2879_, lean_object* v_oldTraces_2880_, lean_object* v_ref_2881_, lean_object* v_msg_2882_, lean_object* v_resStartStop_2883_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2868_, v_inst_2869_, v_inst_2871_, v_inst_2872_, v_always_2873_, v_inst_2874_, v_cls_2875_, v_collapsed_2876_, v_tag_2877_, v_opts_2878_, v_clsEnabled_2879_, v_oldTraces_2880_, v_ref_2881_, v_msg_2882_, v_resStartStop_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_2885_ = _args[0];
lean_object* v_m_2886_ = _args[1];
lean_object* v_inst_2887_ = _args[2];
lean_object* v_inst_2888_ = _args[3];
lean_object* v_00_u03b5_2889_ = _args[4];
lean_object* v_inst_2890_ = _args[5];
lean_object* v_inst_2891_ = _args[6];
lean_object* v_always_2892_ = _args[7];
lean_object* v_inst_2893_ = _args[8];
lean_object* v_cls_2894_ = _args[9];
lean_object* v_collapsed_2895_ = _args[10];
lean_object* v_tag_2896_ = _args[11];
lean_object* v_opts_2897_ = _args[12];
lean_object* v_clsEnabled_2898_ = _args[13];
lean_object* v_oldTraces_2899_ = _args[14];
lean_object* v_ref_2900_ = _args[15];
lean_object* v_msg_2901_ = _args[16];
lean_object* v_resStartStop_2902_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2903_; uint8_t v_clsEnabled_boxed_2904_; lean_object* v_res_2905_; 
v_collapsed_boxed_2903_ = lean_unbox(v_collapsed_2895_);
v_clsEnabled_boxed_2904_ = lean_unbox(v_clsEnabled_2898_);
v_res_2905_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(v_00_u03b1_2885_, v_m_2886_, v_inst_2887_, v_inst_2888_, v_00_u03b5_2889_, v_inst_2890_, v_inst_2891_, v_always_2892_, v_inst_2893_, v_cls_2894_, v_collapsed_boxed_2903_, v_tag_2896_, v_opts_2897_, v_clsEnabled_boxed_2904_, v_oldTraces_2899_, v_ref_2900_, v_msg_2901_, v_resStartStop_2902_);
lean_dec_ref(v_opts_2897_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object* v_inst_2906_, lean_object* v_____do__lift_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = lean_apply_1(v_inst_2906_, v_____do__lift_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_always_2913_, lean_object* v_inst_2914_, lean_object* v_cls_2915_, uint8_t v_collapsed_2916_, lean_object* v_tag_2917_, lean_object* v_opts_2918_, uint8_t v_clsEnabled_2919_, lean_object* v_oldTraces_2920_, lean_object* v_ref_2921_, lean_object* v_msg_2922_, lean_object* v_resStartStop_2923_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2909_, v_inst_2910_, v_inst_2911_, v_inst_2912_, v_always_2913_, v_inst_2914_, v_cls_2915_, v_collapsed_2916_, v_tag_2917_, v_opts_2918_, v_clsEnabled_2919_, v_oldTraces_2920_, v_ref_2921_, v_msg_2922_, v_resStartStop_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object* v_inst_2925_, lean_object* v_inst_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_always_2929_, lean_object* v_inst_2930_, lean_object* v_cls_2931_, lean_object* v_collapsed_2932_, lean_object* v_tag_2933_, lean_object* v_opts_2934_, lean_object* v_clsEnabled_2935_, lean_object* v_oldTraces_2936_, lean_object* v_ref_2937_, lean_object* v_msg_2938_, lean_object* v_resStartStop_2939_){
_start:
{
uint8_t v_collapsed_boxed_2940_; uint8_t v_clsEnabled_boxed_2941_; lean_object* v_res_2942_; 
v_collapsed_boxed_2940_ = lean_unbox(v_collapsed_2932_);
v_clsEnabled_boxed_2941_ = lean_unbox(v_clsEnabled_2935_);
v_res_2942_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_2925_, v_inst_2926_, v_inst_2927_, v_inst_2928_, v_always_2929_, v_inst_2930_, v_cls_2931_, v_collapsed_boxed_2940_, v_tag_2933_, v_opts_2934_, v_clsEnabled_boxed_2941_, v_oldTraces_2936_, v_ref_2937_, v_msg_2938_, v_resStartStop_2939_);
lean_dec_ref(v_opts_2934_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object* v_always_2943_, lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_cls_2949_, uint8_t v_collapsed_2950_, lean_object* v_tag_2951_, lean_object* v_opts_2952_, uint8_t v_clsEnabled_2953_, lean_object* v_oldTraces_2954_, lean_object* v_ref_2955_, lean_object* v_toPure_2956_, lean_object* v_toBind_2957_, lean_object* v_k_2958_, lean_object* v_inst_2959_, lean_object* v_msg_2960_){
_start:
{
lean_object* v_tryCatch_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___f_2964_; lean_object* v___f_2965_; lean_object* v___f_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_tryCatch_2961_ = lean_ctor_get(v_always_2943_, 1);
lean_inc(v_tryCatch_2961_);
v___x_2962_ = lean_box(v_collapsed_2950_);
v___x_2963_ = lean_box(v_clsEnabled_2953_);
lean_inc_ref(v_opts_2952_);
v___f_2964_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__1___boxed), 15, 14);
lean_closure_set(v___f_2964_, 0, v_inst_2944_);
lean_closure_set(v___f_2964_, 1, v_inst_2945_);
lean_closure_set(v___f_2964_, 2, v_inst_2946_);
lean_closure_set(v___f_2964_, 3, v_inst_2947_);
lean_closure_set(v___f_2964_, 4, v_always_2943_);
lean_closure_set(v___f_2964_, 5, v_inst_2948_);
lean_closure_set(v___f_2964_, 6, v_cls_2949_);
lean_closure_set(v___f_2964_, 7, v___x_2962_);
lean_closure_set(v___f_2964_, 8, v_tag_2951_);
lean_closure_set(v___f_2964_, 9, v_opts_2952_);
lean_closure_set(v___f_2964_, 10, v___x_2963_);
lean_closure_set(v___f_2964_, 11, v_oldTraces_2954_);
lean_closure_set(v___f_2964_, 12, v_ref_2955_);
lean_closure_set(v___f_2964_, 13, v_msg_2960_);
lean_inc_n(v_toPure_2956_, 2);
v___f_2965_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2965_, 0, v_toPure_2956_);
v___f_2966_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2966_, 0, v_toPure_2956_);
lean_inc(v_toBind_2957_);
v___x_2967_ = lean_apply_4(v_toBind_2957_, lean_box(0), lean_box(0), v_k_2958_, v___f_2966_);
v___x_2968_ = lean_apply_3(v_tryCatch_2961_, lean_box(0), v___x_2967_, v___f_2965_);
v___x_2969_ = l_Lean_KVMap_instValueBool;
v___x_2970_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2971_ = l_Lean_Option_get___redArg(v___x_2969_, v_opts_2952_, v___x_2970_);
lean_dec_ref(v_opts_2952_);
v___x_2972_ = lean_unbox(v___x_2971_);
lean_dec(v___x_2971_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___f_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2973_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_2974_ = lean_apply_2(v_inst_2959_, lean_box(0), v___x_2973_);
lean_inc(v___x_2974_);
lean_inc_n(v_toBind_2957_, 2);
v___f_2975_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_2975_, 0, v_toPure_2956_);
lean_closure_set(v___f_2975_, 1, v_toBind_2957_);
lean_closure_set(v___f_2975_, 2, v___x_2974_);
lean_closure_set(v___f_2975_, 3, v___x_2968_);
v___x_2976_ = lean_apply_4(v_toBind_2957_, lean_box(0), lean_box(0), v___x_2974_, v___f_2975_);
v___x_2977_ = lean_apply_4(v_toBind_2957_, lean_box(0), lean_box(0), v___x_2976_, v___f_2964_);
return v___x_2977_;
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___f_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2978_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_2979_ = lean_apply_2(v_inst_2959_, lean_box(0), v___x_2978_);
lean_inc(v___x_2979_);
lean_inc_n(v_toBind_2957_, 2);
v___f_2980_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_2980_, 0, v_toPure_2956_);
lean_closure_set(v___f_2980_, 1, v_toBind_2957_);
lean_closure_set(v___f_2980_, 2, v___x_2979_);
lean_closure_set(v___f_2980_, 3, v___x_2968_);
v___x_2981_ = lean_apply_4(v_toBind_2957_, lean_box(0), lean_box(0), v___x_2979_, v___f_2980_);
v___x_2982_ = lean_apply_4(v_toBind_2957_, lean_box(0), lean_box(0), v___x_2981_, v___f_2964_);
return v___x_2982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_2983_ = _args[0];
lean_object* v_inst_2984_ = _args[1];
lean_object* v_inst_2985_ = _args[2];
lean_object* v_inst_2986_ = _args[3];
lean_object* v_inst_2987_ = _args[4];
lean_object* v_inst_2988_ = _args[5];
lean_object* v_cls_2989_ = _args[6];
lean_object* v_collapsed_2990_ = _args[7];
lean_object* v_tag_2991_ = _args[8];
lean_object* v_opts_2992_ = _args[9];
lean_object* v_clsEnabled_2993_ = _args[10];
lean_object* v_oldTraces_2994_ = _args[11];
lean_object* v_ref_2995_ = _args[12];
lean_object* v_toPure_2996_ = _args[13];
lean_object* v_toBind_2997_ = _args[14];
lean_object* v_k_2998_ = _args[15];
lean_object* v_inst_2999_ = _args[16];
lean_object* v_msg_3000_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3001_; uint8_t v_clsEnabled_boxed_3002_; lean_object* v_res_3003_; 
v_collapsed_boxed_3001_ = lean_unbox(v_collapsed_2990_);
v_clsEnabled_boxed_3002_ = lean_unbox(v_clsEnabled_2993_);
v_res_3003_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_always_2983_, v_inst_2984_, v_inst_2985_, v_inst_2986_, v_inst_2987_, v_inst_2988_, v_cls_2989_, v_collapsed_boxed_3001_, v_tag_2991_, v_opts_2992_, v_clsEnabled_boxed_3002_, v_oldTraces_2994_, v_ref_2995_, v_toPure_2996_, v_toBind_2997_, v_k_2998_, v_inst_2999_, v_msg_3000_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object* v_always_3004_, lean_object* v_inst_3005_, lean_object* v_inst_3006_, lean_object* v_inst_3007_, lean_object* v_inst_3008_, lean_object* v_inst_3009_, lean_object* v_cls_3010_, uint8_t v_collapsed_3011_, lean_object* v_tag_3012_, lean_object* v_opts_3013_, uint8_t v_clsEnabled_3014_, lean_object* v_oldTraces_3015_, lean_object* v_toPure_3016_, lean_object* v_toBind_3017_, lean_object* v_k_3018_, lean_object* v_inst_3019_, lean_object* v_msg_3020_, lean_object* v___f_3021_, lean_object* v_withRef_3022_, lean_object* v_getRef_3023_, lean_object* v_ref_3024_){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___f_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___f_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3025_ = lean_box(v_collapsed_3011_);
v___x_3026_ = lean_box(v_clsEnabled_3014_);
lean_inc_n(v_toBind_3017_, 3);
lean_inc(v_ref_3024_);
v___f_3027_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__10___boxed), 18, 17);
lean_closure_set(v___f_3027_, 0, v_always_3004_);
lean_closure_set(v___f_3027_, 1, v_inst_3005_);
lean_closure_set(v___f_3027_, 2, v_inst_3006_);
lean_closure_set(v___f_3027_, 3, v_inst_3007_);
lean_closure_set(v___f_3027_, 4, v_inst_3008_);
lean_closure_set(v___f_3027_, 5, v_inst_3009_);
lean_closure_set(v___f_3027_, 6, v_cls_3010_);
lean_closure_set(v___f_3027_, 7, v___x_3025_);
lean_closure_set(v___f_3027_, 8, v_tag_3012_);
lean_closure_set(v___f_3027_, 9, v_opts_3013_);
lean_closure_set(v___f_3027_, 10, v___x_3026_);
lean_closure_set(v___f_3027_, 11, v_oldTraces_3015_);
lean_closure_set(v___f_3027_, 12, v_ref_3024_);
lean_closure_set(v___f_3027_, 13, v_toPure_3016_);
lean_closure_set(v___f_3027_, 14, v_toBind_3017_);
lean_closure_set(v___f_3027_, 15, v_k_3018_);
lean_closure_set(v___f_3027_, 16, v_inst_3019_);
v___x_3028_ = lean_box(0);
v___x_3029_ = lean_apply_1(v_msg_3020_, v___x_3028_);
v___x_3030_ = lean_apply_4(v_toBind_3017_, lean_box(0), lean_box(0), v___x_3029_, v___f_3021_);
v___f_3031_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3031_, 0, v_ref_3024_);
lean_closure_set(v___f_3031_, 1, v_withRef_3022_);
lean_closure_set(v___f_3031_, 2, v___x_3030_);
v___x_3032_ = lean_apply_4(v_toBind_3017_, lean_box(0), lean_box(0), v_getRef_3023_, v___f_3031_);
v___x_3033_ = lean_apply_4(v_toBind_3017_, lean_box(0), lean_box(0), v___x_3032_, v___f_3027_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_3034_ = _args[0];
lean_object* v_inst_3035_ = _args[1];
lean_object* v_inst_3036_ = _args[2];
lean_object* v_inst_3037_ = _args[3];
lean_object* v_inst_3038_ = _args[4];
lean_object* v_inst_3039_ = _args[5];
lean_object* v_cls_3040_ = _args[6];
lean_object* v_collapsed_3041_ = _args[7];
lean_object* v_tag_3042_ = _args[8];
lean_object* v_opts_3043_ = _args[9];
lean_object* v_clsEnabled_3044_ = _args[10];
lean_object* v_oldTraces_3045_ = _args[11];
lean_object* v_toPure_3046_ = _args[12];
lean_object* v_toBind_3047_ = _args[13];
lean_object* v_k_3048_ = _args[14];
lean_object* v_inst_3049_ = _args[15];
lean_object* v_msg_3050_ = _args[16];
lean_object* v___f_3051_ = _args[17];
lean_object* v_withRef_3052_ = _args[18];
lean_object* v_getRef_3053_ = _args[19];
lean_object* v_ref_3054_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_3055_; uint8_t v_clsEnabled_boxed_3056_; lean_object* v_res_3057_; 
v_collapsed_boxed_3055_ = lean_unbox(v_collapsed_3041_);
v_clsEnabled_boxed_3056_ = lean_unbox(v_clsEnabled_3044_);
v_res_3057_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_always_3034_, v_inst_3035_, v_inst_3036_, v_inst_3037_, v_inst_3038_, v_inst_3039_, v_cls_3040_, v_collapsed_boxed_3055_, v_tag_3042_, v_opts_3043_, v_clsEnabled_boxed_3056_, v_oldTraces_3045_, v_toPure_3046_, v_toBind_3047_, v_k_3048_, v_inst_3049_, v_msg_3050_, v___f_3051_, v_withRef_3052_, v_getRef_3053_, v_ref_3054_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object* v_inst_3058_, lean_object* v_always_3059_, lean_object* v_inst_3060_, lean_object* v_inst_3061_, lean_object* v_inst_3062_, lean_object* v_inst_3063_, lean_object* v_cls_3064_, uint8_t v_collapsed_3065_, lean_object* v_tag_3066_, lean_object* v_opts_3067_, uint8_t v_clsEnabled_3068_, lean_object* v_toPure_3069_, lean_object* v_toBind_3070_, lean_object* v_k_3071_, lean_object* v_inst_3072_, lean_object* v_msg_3073_, lean_object* v___f_3074_, lean_object* v_oldTraces_3075_){
_start:
{
lean_object* v_getRef_3076_; lean_object* v_withRef_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___f_3080_; lean_object* v___x_3081_; 
v_getRef_3076_ = lean_ctor_get(v_inst_3058_, 0);
lean_inc_n(v_getRef_3076_, 2);
v_withRef_3077_ = lean_ctor_get(v_inst_3058_, 1);
lean_inc(v_withRef_3077_);
v___x_3078_ = lean_box(v_collapsed_3065_);
v___x_3079_ = lean_box(v_clsEnabled_3068_);
lean_inc(v_toBind_3070_);
v___f_3080_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__3___boxed), 21, 20);
lean_closure_set(v___f_3080_, 0, v_always_3059_);
lean_closure_set(v___f_3080_, 1, v_inst_3060_);
lean_closure_set(v___f_3080_, 2, v_inst_3061_);
lean_closure_set(v___f_3080_, 3, v_inst_3058_);
lean_closure_set(v___f_3080_, 4, v_inst_3062_);
lean_closure_set(v___f_3080_, 5, v_inst_3063_);
lean_closure_set(v___f_3080_, 6, v_cls_3064_);
lean_closure_set(v___f_3080_, 7, v___x_3078_);
lean_closure_set(v___f_3080_, 8, v_tag_3066_);
lean_closure_set(v___f_3080_, 9, v_opts_3067_);
lean_closure_set(v___f_3080_, 10, v___x_3079_);
lean_closure_set(v___f_3080_, 11, v_oldTraces_3075_);
lean_closure_set(v___f_3080_, 12, v_toPure_3069_);
lean_closure_set(v___f_3080_, 13, v_toBind_3070_);
lean_closure_set(v___f_3080_, 14, v_k_3071_);
lean_closure_set(v___f_3080_, 15, v_inst_3072_);
lean_closure_set(v___f_3080_, 16, v_msg_3073_);
lean_closure_set(v___f_3080_, 17, v___f_3074_);
lean_closure_set(v___f_3080_, 18, v_withRef_3077_);
lean_closure_set(v___f_3080_, 19, v_getRef_3076_);
v___x_3081_ = lean_apply_4(v_toBind_3070_, lean_box(0), lean_box(0), v_getRef_3076_, v___f_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_3082_ = _args[0];
lean_object* v_always_3083_ = _args[1];
lean_object* v_inst_3084_ = _args[2];
lean_object* v_inst_3085_ = _args[3];
lean_object* v_inst_3086_ = _args[4];
lean_object* v_inst_3087_ = _args[5];
lean_object* v_cls_3088_ = _args[6];
lean_object* v_collapsed_3089_ = _args[7];
lean_object* v_tag_3090_ = _args[8];
lean_object* v_opts_3091_ = _args[9];
lean_object* v_clsEnabled_3092_ = _args[10];
lean_object* v_toPure_3093_ = _args[11];
lean_object* v_toBind_3094_ = _args[12];
lean_object* v_k_3095_ = _args[13];
lean_object* v_inst_3096_ = _args[14];
lean_object* v_msg_3097_ = _args[15];
lean_object* v___f_3098_ = _args[16];
lean_object* v_oldTraces_3099_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3100_; uint8_t v_clsEnabled_boxed_3101_; lean_object* v_res_3102_; 
v_collapsed_boxed_3100_ = lean_unbox(v_collapsed_3089_);
v_clsEnabled_boxed_3101_ = lean_unbox(v_clsEnabled_3092_);
v_res_3102_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3082_, v_always_3083_, v_inst_3084_, v_inst_3085_, v_inst_3086_, v_inst_3087_, v_cls_3088_, v_collapsed_boxed_3100_, v_tag_3090_, v_opts_3091_, v_clsEnabled_boxed_3101_, v_toPure_3093_, v_toBind_3094_, v_k_3095_, v_inst_3096_, v_msg_3097_, v___f_3098_, v_oldTraces_3099_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object* v_inst_3103_, lean_object* v_always_3104_, lean_object* v_inst_3105_, lean_object* v_inst_3106_, lean_object* v_inst_3107_, lean_object* v_inst_3108_, lean_object* v_cls_3109_, uint8_t v_collapsed_3110_, lean_object* v_tag_3111_, lean_object* v_opts_3112_, lean_object* v_toPure_3113_, lean_object* v_toBind_3114_, lean_object* v_k_3115_, lean_object* v_inst_3116_, lean_object* v_msg_3117_, lean_object* v___f_3118_, uint8_t v_clsEnabled_3119_){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___f_3122_; 
v___x_3120_ = lean_box(v_collapsed_3110_);
v___x_3121_ = lean_box(v_clsEnabled_3119_);
lean_inc(v_k_3115_);
lean_inc(v_toBind_3114_);
lean_inc_ref(v_opts_3112_);
lean_inc_ref(v_inst_3106_);
lean_inc_ref(v_inst_3105_);
v___f_3122_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__2___boxed), 18, 17);
lean_closure_set(v___f_3122_, 0, v_inst_3103_);
lean_closure_set(v___f_3122_, 1, v_always_3104_);
lean_closure_set(v___f_3122_, 2, v_inst_3105_);
lean_closure_set(v___f_3122_, 3, v_inst_3106_);
lean_closure_set(v___f_3122_, 4, v_inst_3107_);
lean_closure_set(v___f_3122_, 5, v_inst_3108_);
lean_closure_set(v___f_3122_, 6, v_cls_3109_);
lean_closure_set(v___f_3122_, 7, v___x_3120_);
lean_closure_set(v___f_3122_, 8, v_tag_3111_);
lean_closure_set(v___f_3122_, 9, v_opts_3112_);
lean_closure_set(v___f_3122_, 10, v___x_3121_);
lean_closure_set(v___f_3122_, 11, v_toPure_3113_);
lean_closure_set(v___f_3122_, 12, v_toBind_3114_);
lean_closure_set(v___f_3122_, 13, v_k_3115_);
lean_closure_set(v___f_3122_, 14, v_inst_3116_);
lean_closure_set(v___f_3122_, 15, v_msg_3117_);
lean_closure_set(v___f_3122_, 16, v___f_3118_);
if (v_clsEnabled_3119_ == 0)
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3126_ = l_Lean_KVMap_instValueBool;
v___x_3127_ = l_Lean_trace_profiler;
v___x_3128_ = l_Lean_Option_get___redArg(v___x_3126_, v_opts_3112_, v___x_3127_);
lean_dec_ref(v_opts_3112_);
v___x_3129_ = lean_unbox(v___x_3128_);
lean_dec(v___x_3128_);
if (v___x_3129_ == 0)
{
lean_dec_ref(v___f_3122_);
lean_dec(v_toBind_3114_);
lean_dec_ref(v_inst_3106_);
lean_dec_ref(v_inst_3105_);
return v_k_3115_;
}
else
{
lean_dec(v_k_3115_);
goto v___jp_3123_;
}
}
else
{
lean_dec(v_k_3115_);
lean_dec_ref(v_opts_3112_);
goto v___jp_3123_;
}
v___jp_3123_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3105_, v_inst_3106_);
v___x_3125_ = lean_apply_4(v_toBind_3114_, lean_box(0), lean_box(0), v___x_3124_, v___f_3122_);
return v___x_3125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_3130_ = _args[0];
lean_object* v_always_3131_ = _args[1];
lean_object* v_inst_3132_ = _args[2];
lean_object* v_inst_3133_ = _args[3];
lean_object* v_inst_3134_ = _args[4];
lean_object* v_inst_3135_ = _args[5];
lean_object* v_cls_3136_ = _args[6];
lean_object* v_collapsed_3137_ = _args[7];
lean_object* v_tag_3138_ = _args[8];
lean_object* v_opts_3139_ = _args[9];
lean_object* v_toPure_3140_ = _args[10];
lean_object* v_toBind_3141_ = _args[11];
lean_object* v_k_3142_ = _args[12];
lean_object* v_inst_3143_ = _args[13];
lean_object* v_msg_3144_ = _args[14];
lean_object* v___f_3145_ = _args[15];
lean_object* v_clsEnabled_3146_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3147_; uint8_t v_clsEnabled_boxed_3148_; lean_object* v_res_3149_; 
v_collapsed_boxed_3147_ = lean_unbox(v_collapsed_3137_);
v_clsEnabled_boxed_3148_ = lean_unbox(v_clsEnabled_3146_);
v_res_3149_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3130_, v_always_3131_, v_inst_3132_, v_inst_3133_, v_inst_3134_, v_inst_3135_, v_cls_3136_, v_collapsed_boxed_3147_, v_tag_3138_, v_opts_3139_, v_toPure_3140_, v_toBind_3141_, v_k_3142_, v_inst_3143_, v_msg_3144_, v___f_3145_, v_clsEnabled_boxed_3148_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object* v_k_3150_, lean_object* v_inst_3151_, lean_object* v_toApplicative_3152_, lean_object* v_inst_3153_, lean_object* v_always_3154_, lean_object* v_inst_3155_, lean_object* v_inst_3156_, lean_object* v_inst_3157_, lean_object* v_cls_3158_, uint8_t v_collapsed_3159_, lean_object* v_tag_3160_, lean_object* v_toBind_3161_, lean_object* v_inst_3162_, lean_object* v_msg_3163_, lean_object* v___f_3164_, lean_object* v_inst_3165_, lean_object* v_opts_3166_){
_start:
{
uint8_t v_hasTrace_3167_; 
v_hasTrace_3167_ = lean_ctor_get_uint8(v_opts_3166_, sizeof(void*)*1);
if (v_hasTrace_3167_ == 0)
{
lean_dec_ref(v_opts_3166_);
lean_dec(v_inst_3165_);
lean_dec(v___f_3164_);
lean_dec(v_msg_3163_);
lean_dec(v_inst_3162_);
lean_dec(v_toBind_3161_);
lean_dec_ref(v_tag_3160_);
lean_dec(v_cls_3158_);
lean_dec_ref(v_inst_3157_);
lean_dec(v_inst_3156_);
lean_dec_ref(v_inst_3155_);
lean_dec_ref(v_always_3154_);
lean_dec_ref(v_inst_3153_);
lean_dec_ref(v_toApplicative_3152_);
lean_dec_ref(v_inst_3151_);
return v_k_3150_;
}
else
{
lean_object* v_getInheritedTraceOptions_3168_; lean_object* v_toPure_3169_; lean_object* v___x_3170_; lean_object* v___f_3171_; lean_object* v___f_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_getInheritedTraceOptions_3168_ = lean_ctor_get(v_inst_3151_, 2);
lean_inc(v_getInheritedTraceOptions_3168_);
v_toPure_3169_ = lean_ctor_get(v_toApplicative_3152_, 1);
lean_inc_n(v_toPure_3169_, 2);
lean_dec_ref(v_toApplicative_3152_);
v___x_3170_ = lean_box(v_collapsed_3159_);
lean_inc_n(v_toBind_3161_, 3);
lean_inc(v_cls_3158_);
v___f_3171_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_3171_, 0, v_inst_3153_);
lean_closure_set(v___f_3171_, 1, v_always_3154_);
lean_closure_set(v___f_3171_, 2, v_inst_3155_);
lean_closure_set(v___f_3171_, 3, v_inst_3151_);
lean_closure_set(v___f_3171_, 4, v_inst_3156_);
lean_closure_set(v___f_3171_, 5, v_inst_3157_);
lean_closure_set(v___f_3171_, 6, v_cls_3158_);
lean_closure_set(v___f_3171_, 7, v___x_3170_);
lean_closure_set(v___f_3171_, 8, v_tag_3160_);
lean_closure_set(v___f_3171_, 9, v_opts_3166_);
lean_closure_set(v___f_3171_, 10, v_toPure_3169_);
lean_closure_set(v___f_3171_, 11, v_toBind_3161_);
lean_closure_set(v___f_3171_, 12, v_k_3150_);
lean_closure_set(v___f_3171_, 13, v_inst_3162_);
lean_closure_set(v___f_3171_, 14, v_msg_3163_);
lean_closure_set(v___f_3171_, 15, v___f_3164_);
v___f_3172_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3172_, 0, v_toPure_3169_);
lean_closure_set(v___f_3172_, 1, v_cls_3158_);
lean_closure_set(v___f_3172_, 2, v_toBind_3161_);
lean_closure_set(v___f_3172_, 3, v_inst_3165_);
v___x_3173_ = lean_apply_4(v_toBind_3161_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3168_, v___f_3172_);
v___x_3174_ = lean_apply_4(v_toBind_3161_, lean_box(0), lean_box(0), v___x_3173_, v___f_3171_);
return v___x_3174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_k_3175_ = _args[0];
lean_object* v_inst_3176_ = _args[1];
lean_object* v_toApplicative_3177_ = _args[2];
lean_object* v_inst_3178_ = _args[3];
lean_object* v_always_3179_ = _args[4];
lean_object* v_inst_3180_ = _args[5];
lean_object* v_inst_3181_ = _args[6];
lean_object* v_inst_3182_ = _args[7];
lean_object* v_cls_3183_ = _args[8];
lean_object* v_collapsed_3184_ = _args[9];
lean_object* v_tag_3185_ = _args[10];
lean_object* v_toBind_3186_ = _args[11];
lean_object* v_inst_3187_ = _args[12];
lean_object* v_msg_3188_ = _args[13];
lean_object* v___f_3189_ = _args[14];
lean_object* v_inst_3190_ = _args[15];
lean_object* v_opts_3191_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3192_; lean_object* v_res_3193_; 
v_collapsed_boxed_3192_ = lean_unbox(v_collapsed_3184_);
v_res_3193_ = l_Lean_withTraceNodeBefore___redArg___lam__7(v_k_3175_, v_inst_3176_, v_toApplicative_3177_, v_inst_3178_, v_always_3179_, v_inst_3180_, v_inst_3181_, v_inst_3182_, v_cls_3183_, v_collapsed_boxed_3192_, v_tag_3185_, v_toBind_3186_, v_inst_3187_, v_msg_3188_, v___f_3189_, v_inst_3190_, v_opts_3191_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object* v_inst_3194_, lean_object* v_inst_3195_, lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_always_3199_, lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_cls_3202_, lean_object* v_msg_3203_, lean_object* v_k_3204_, uint8_t v_collapsed_3205_, lean_object* v_tag_3206_){
_start:
{
lean_object* v_toApplicative_3207_; lean_object* v_toBind_3208_; lean_object* v___f_3209_; lean_object* v___x_3210_; lean_object* v___f_3211_; lean_object* v___x_3212_; 
v_toApplicative_3207_ = lean_ctor_get(v_inst_3194_, 0);
lean_inc_ref(v_toApplicative_3207_);
v_toBind_3208_ = lean_ctor_get(v_inst_3194_, 1);
lean_inc_n(v_toBind_3208_, 2);
lean_inc(v_inst_3197_);
v___f_3209_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3209_, 0, v_inst_3197_);
v___x_3210_ = lean_box(v_collapsed_3205_);
lean_inc(v_inst_3198_);
v___f_3211_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3211_, 0, v_k_3204_);
lean_closure_set(v___f_3211_, 1, v_inst_3195_);
lean_closure_set(v___f_3211_, 2, v_toApplicative_3207_);
lean_closure_set(v___f_3211_, 3, v_inst_3196_);
lean_closure_set(v___f_3211_, 4, v_always_3199_);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_inst_3217_, lean_object* v_always_3218_, lean_object* v_inst_3219_, lean_object* v_inst_3220_, lean_object* v_cls_3221_, lean_object* v_msg_3222_, lean_object* v_k_3223_, lean_object* v_collapsed_3224_, lean_object* v_tag_3225_){
_start:
{
uint8_t v_collapsed_boxed_3226_; lean_object* v_res_3227_; 
v_collapsed_boxed_3226_ = lean_unbox(v_collapsed_3224_);
v_res_3227_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3213_, v_inst_3214_, v_inst_3215_, v_inst_3216_, v_inst_3217_, v_always_3218_, v_inst_3219_, v_inst_3220_, v_cls_3221_, v_msg_3222_, v_k_3223_, v_collapsed_boxed_3226_, v_tag_3225_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object* v_00_u03b1_3228_, lean_object* v_m_3229_, lean_object* v_inst_3230_, lean_object* v_inst_3231_, lean_object* v_00_u03b5_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_always_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_cls_3239_, lean_object* v_msg_3240_, lean_object* v_k_3241_, uint8_t v_collapsed_3242_, lean_object* v_tag_3243_){
_start:
{
lean_object* v_toApplicative_3244_; lean_object* v_toBind_3245_; lean_object* v___f_3246_; lean_object* v___x_3247_; lean_object* v___f_3248_; lean_object* v___x_3249_; 
v_toApplicative_3244_ = lean_ctor_get(v_inst_3230_, 0);
lean_inc_ref(v_toApplicative_3244_);
v_toBind_3245_ = lean_ctor_get(v_inst_3230_, 1);
lean_inc_n(v_toBind_3245_, 2);
lean_inc(v_inst_3234_);
v___f_3246_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3246_, 0, v_inst_3234_);
v___x_3247_ = lean_box(v_collapsed_3242_);
lean_inc(v_inst_3235_);
v___f_3248_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3248_, 0, v_k_3241_);
lean_closure_set(v___f_3248_, 1, v_inst_3231_);
lean_closure_set(v___f_3248_, 2, v_toApplicative_3244_);
lean_closure_set(v___f_3248_, 3, v_inst_3233_);
lean_closure_set(v___f_3248_, 4, v_always_3236_);
lean_closure_set(v___f_3248_, 5, v_inst_3230_);
lean_closure_set(v___f_3248_, 6, v_inst_3234_);
lean_closure_set(v___f_3248_, 7, v_inst_3238_);
lean_closure_set(v___f_3248_, 8, v_cls_3239_);
lean_closure_set(v___f_3248_, 9, v___x_3247_);
lean_closure_set(v___f_3248_, 10, v_tag_3243_);
lean_closure_set(v___f_3248_, 11, v_toBind_3245_);
lean_closure_set(v___f_3248_, 12, v_inst_3237_);
lean_closure_set(v___f_3248_, 13, v_msg_3240_);
lean_closure_set(v___f_3248_, 14, v___f_3246_);
lean_closure_set(v___f_3248_, 15, v_inst_3235_);
v___x_3249_ = lean_apply_4(v_toBind_3245_, lean_box(0), lean_box(0), v_inst_3235_, v___f_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object* v_00_u03b1_3250_, lean_object* v_m_3251_, lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_00_u03b5_3254_, lean_object* v_inst_3255_, lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_always_3258_, lean_object* v_inst_3259_, lean_object* v_inst_3260_, lean_object* v_cls_3261_, lean_object* v_msg_3262_, lean_object* v_k_3263_, lean_object* v_collapsed_3264_, lean_object* v_tag_3265_){
_start:
{
uint8_t v_collapsed_boxed_3266_; lean_object* v_res_3267_; 
v_collapsed_boxed_3266_ = lean_unbox(v_collapsed_3264_);
v_res_3267_ = l_Lean_withTraceNodeBefore(v_00_u03b1_3250_, v_m_3251_, v_inst_3252_, v_inst_3253_, v_00_u03b5_3254_, v_inst_3255_, v_inst_3256_, v_inst_3257_, v_always_3258_, v_inst_3259_, v_inst_3260_, v_cls_3261_, v_msg_3262_, v_k_3263_, v_collapsed_boxed_3266_, v_tag_3265_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0(lean_object* v_toApplicative_3268_, lean_object* v_____s_3269_){
_start:
{
lean_object* v_toPure_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v_toPure_3270_ = lean_ctor_get(v_toApplicative_3268_, 1);
lean_inc(v_toPure_3270_);
lean_dec_ref(v_toApplicative_3268_);
v___x_3271_ = lean_box(0);
v___x_3272_ = lean_apply_2(v_toPure_3270_, lean_box(0), v___x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__1(lean_object* v_x_3273_, lean_object* v_x_3274_){
_start:
{
lean_object* v_fst_3275_; lean_object* v_fst_3276_; lean_object* v_fst_3277_; lean_object* v_fst_3278_; uint8_t v___x_3279_; 
v_fst_3275_ = lean_ctor_get(v_x_3273_, 0);
v_fst_3276_ = lean_ctor_get(v_x_3274_, 0);
v_fst_3277_ = lean_ctor_get(v_fst_3275_, 0);
v_fst_3278_ = lean_ctor_get(v_fst_3276_, 0);
v___x_3279_ = lean_nat_dec_lt(v_fst_3277_, v_fst_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1___boxed(lean_object* v_x_3280_, lean_object* v_x_3281_){
_start:
{
uint8_t v_res_3282_; lean_object* v_r_3283_; 
v_res_3282_ = l_Lean_addTraceAsMessages___redArg___lam__1(v_x_3280_, v_x_3281_);
lean_dec_ref(v_x_3281_);
lean_dec_ref(v_x_3280_);
v_r_3283_ = lean_box(v_res_3282_);
return v_r_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object* v_x1_3284_, lean_object* v_x2_3285_, lean_object* v_x3_3286_){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3287_, 0, v_x2_3285_);
lean_ctor_set(v___x_3287_, 1, v_x3_3286_);
v___x_3288_ = lean_array_push(v_x1_3284_, v___x_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object* v_toApplicative_3289_, lean_object* v___x_3290_, lean_object* v_r_3291_){
_start:
{
lean_object* v_toPure_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v_toPure_3292_ = lean_ctor_get(v_toApplicative_3289_, 1);
lean_inc(v_toPure_3292_);
lean_dec_ref(v_toApplicative_3289_);
v___x_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3290_);
v___x_3294_ = lean_apply_2(v_toPure_3292_, lean_box(0), v___x_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object* v_____do__lift_3295_, lean_object* v___x_3296_, lean_object* v_fst_3297_, lean_object* v_snd_3298_, lean_object* v_logMessage_3299_, lean_object* v_toBind_3300_, lean_object* v___f_3301_, lean_object* v_____do__lift_3302_){
_start:
{
uint8_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3303_ = 0;
v___x_3304_ = l_Lean_Elab_mkMessageCore(v_____do__lift_3295_, v_____do__lift_3302_, v___x_3296_, v___x_3303_, v_fst_3297_, v_snd_3298_);
v___x_3305_ = lean_apply_1(v_logMessage_3299_, v___x_3304_);
v___x_3306_ = lean_apply_4(v_toBind_3300_, lean_box(0), lean_box(0), v___x_3305_, v___f_3301_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object* v_____do__lift_3307_, lean_object* v___x_3308_, lean_object* v_fst_3309_, lean_object* v_snd_3310_, lean_object* v_logMessage_3311_, lean_object* v_toBind_3312_, lean_object* v___f_3313_, lean_object* v_____do__lift_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_addTraceAsMessages___redArg___lam__4(v_____do__lift_3307_, v___x_3308_, v_fst_3309_, v_snd_3310_, v_logMessage_3311_, v_toBind_3312_, v___f_3313_, v_____do__lift_3314_);
lean_dec(v_snd_3310_);
lean_dec(v_fst_3309_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object* v___x_3316_, lean_object* v_fst_3317_, lean_object* v_snd_3318_, lean_object* v_logMessage_3319_, lean_object* v_toBind_3320_, lean_object* v___f_3321_, lean_object* v_toMonadFileMap_3322_, lean_object* v_____do__lift_3323_){
_start:
{
lean_object* v___f_3324_; lean_object* v___x_3325_; 
lean_inc(v_toBind_3320_);
v___f_3324_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_3324_, 0, v_____do__lift_3323_);
lean_closure_set(v___f_3324_, 1, v___x_3316_);
lean_closure_set(v___f_3324_, 2, v_fst_3317_);
lean_closure_set(v___f_3324_, 3, v_snd_3318_);
lean_closure_set(v___f_3324_, 4, v_logMessage_3319_);
lean_closure_set(v___f_3324_, 5, v_toBind_3320_);
lean_closure_set(v___f_3324_, 6, v___f_3321_);
v___x_3325_ = lean_apply_4(v_toBind_3320_, lean_box(0), lean_box(0), v_toMonadFileMap_3322_, v___f_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object* v___x_3326_, uint8_t v___x_3327_, lean_object* v_inst_3328_, lean_object* v_toBind_3329_, lean_object* v___f_3330_, lean_object* v_a_3331_, lean_object* v_x_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_fst_3334_; lean_object* v_snd_3335_; lean_object* v_fst_3336_; lean_object* v_snd_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3357_; 
v_fst_3334_ = lean_ctor_get(v_a_3331_, 0);
lean_inc(v_fst_3334_);
v_snd_3335_ = lean_ctor_get(v_a_3331_, 1);
lean_inc(v_snd_3335_);
lean_dec_ref(v_a_3331_);
v_fst_3336_ = lean_ctor_get(v_fst_3334_, 0);
v_snd_3337_ = lean_ctor_get(v_fst_3334_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_fst_3334_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3339_ = v_fst_3334_;
v_isShared_3340_ = v_isSharedCheck_3357_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_snd_3337_);
lean_inc(v_fst_3336_);
lean_dec(v_fst_3334_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3357_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; double v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v_toMonadFileMap_3346_; lean_object* v_getFileName_3347_; lean_object* v_logMessage_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3341_ = lean_box(0);
v___x_3342_ = lean_box(0);
v___x_3343_ = lean_float_of_nat(v___x_3326_);
v___x_3344_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_3345_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3345_, 0, v___x_3341_);
lean_ctor_set(v___x_3345_, 1, v___x_3342_);
lean_ctor_set(v___x_3345_, 2, v___x_3344_);
lean_ctor_set_float(v___x_3345_, sizeof(void*)*3, v___x_3343_);
lean_ctor_set_float(v___x_3345_, sizeof(void*)*3 + 8, v___x_3343_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*3 + 16, v___x_3327_);
v_toMonadFileMap_3346_ = lean_ctor_get(v_inst_3328_, 0);
lean_inc(v_toMonadFileMap_3346_);
v_getFileName_3347_ = lean_ctor_get(v_inst_3328_, 2);
lean_inc(v_getFileName_3347_);
v_logMessage_3348_ = lean_ctor_get(v_inst_3328_, 4);
lean_inc(v_logMessage_3348_);
lean_dec_ref(v_inst_3328_);
v___x_3349_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_3350_ = l_Lean_MessageData_nil;
v___x_3351_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3345_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
lean_ctor_set(v___x_3351_, 2, v_snd_3335_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set_tag(v___x_3339_, 8);
lean_ctor_set(v___x_3339_, 1, v___x_3351_);
lean_ctor_set(v___x_3339_, 0, v___x_3349_);
v___x_3353_ = v___x_3339_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___f_3354_; lean_object* v___x_3355_; 
lean_inc(v_toBind_3329_);
v___f_3354_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__5), 8, 7);
lean_closure_set(v___f_3354_, 0, v___x_3353_);
lean_closure_set(v___f_3354_, 1, v_fst_3336_);
lean_closure_set(v___f_3354_, 2, v_snd_3337_);
lean_closure_set(v___f_3354_, 3, v_logMessage_3348_);
lean_closure_set(v___f_3354_, 4, v_toBind_3329_);
lean_closure_set(v___f_3354_, 5, v___f_3330_);
lean_closure_set(v___f_3354_, 6, v_toMonadFileMap_3346_);
v___x_3355_ = lean_apply_4(v_toBind_3329_, lean_box(0), lean_box(0), v_getFileName_3347_, v___f_3354_);
return v___x_3355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object* v___x_3358_, lean_object* v___x_3359_, lean_object* v_inst_3360_, lean_object* v_toBind_3361_, lean_object* v___f_3362_, lean_object* v_a_3363_, lean_object* v_x_3364_, lean_object* v___y_3365_){
_start:
{
uint8_t v___x_1915__boxed_3366_; lean_object* v_res_3367_; 
v___x_1915__boxed_3366_ = lean_unbox(v___x_3359_);
v_res_3367_ = l_Lean_addTraceAsMessages___redArg___lam__6(v___x_3358_, v___x_1915__boxed_3366_, v_inst_3360_, v_toBind_3361_, v___f_3362_, v_a_3363_, v_x_3364_, v___y_3365_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object* v___x_3368_, lean_object* v___f_3369_, lean_object* v_acc_3370_, lean_object* v_l_3371_){
_start:
{
lean_object* v___x_3372_; 
v___x_3372_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_3368_, v___f_3369_, v_acc_3370_, v_l_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object* v_toApplicative_3373_, uint8_t v___x_3374_, lean_object* v_inst_3375_, lean_object* v_toBind_3376_, lean_object* v_inst_3377_, lean_object* v___f_3378_, lean_object* v___f_3379_, lean_object* v___f_3380_, lean_object* v_____s_3381_){
_start:
{
lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3408_; lean_object* v_size_3415_; lean_object* v_buckets_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
v_size_3415_ = lean_ctor_get(v_____s_3381_, 0);
lean_inc(v_size_3415_);
v_buckets_3416_ = lean_ctor_get(v_____s_3381_, 1);
lean_inc_ref(v_buckets_3416_);
lean_dec_ref(v_____s_3381_);
v___x_3417_ = lean_mk_empty_array_with_capacity(v_size_3415_);
lean_dec(v_size_3415_);
v___x_3418_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v___x_3419_ = lean_unsigned_to_nat(0u);
v___x_3420_ = lean_array_get_size(v_buckets_3416_);
v___x_3421_ = lean_nat_dec_lt(v___x_3419_, v___x_3420_);
if (v___x_3421_ == 0)
{
lean_dec_ref(v_buckets_3416_);
lean_dec_ref(v___f_3380_);
v___y_3408_ = v___x_3417_;
goto v___jp_3407_;
}
else
{
lean_object* v___f_3422_; uint8_t v___x_3423_; 
v___f_3422_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__7), 4, 2);
lean_closure_set(v___f_3422_, 0, v___x_3418_);
lean_closure_set(v___f_3422_, 1, v___f_3380_);
v___x_3423_ = lean_nat_dec_le(v___x_3420_, v___x_3420_);
if (v___x_3423_ == 0)
{
if (v___x_3421_ == 0)
{
lean_dec_ref(v___f_3422_);
lean_dec_ref(v_buckets_3416_);
v___y_3408_ = v___x_3417_;
goto v___jp_3407_;
}
else
{
size_t v___x_3424_; size_t v___x_3425_; lean_object* v___x_3426_; 
v___x_3424_ = ((size_t)0ULL);
v___x_3425_ = lean_usize_of_nat(v___x_3420_);
v___x_3426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3418_, v___f_3422_, v_buckets_3416_, v___x_3424_, v___x_3425_, v___x_3417_);
v___y_3408_ = v___x_3426_;
goto v___jp_3407_;
}
}
else
{
size_t v___x_3427_; size_t v___x_3428_; lean_object* v___x_3429_; 
v___x_3427_ = ((size_t)0ULL);
v___x_3428_ = lean_usize_of_nat(v___x_3420_);
v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3418_, v___f_3422_, v_buckets_3416_, v___x_3427_, v___x_3428_, v___x_3417_);
v___y_3408_ = v___x_3429_;
goto v___jp_3407_;
}
}
v___jp_3382_:
{
lean_object* v___x_3385_; lean_object* v___f_3386_; lean_object* v___x_3387_; lean_object* v___f_3388_; size_t v_sz_3389_; size_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3385_ = lean_box(0);
v___f_3386_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3386_, 0, v_toApplicative_3373_);
lean_closure_set(v___f_3386_, 1, v___x_3385_);
v___x_3387_ = lean_box(v___x_3374_);
lean_inc(v_toBind_3376_);
v___f_3388_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__6___boxed), 8, 5);
lean_closure_set(v___f_3388_, 0, v___y_3383_);
lean_closure_set(v___f_3388_, 1, v___x_3387_);
lean_closure_set(v___f_3388_, 2, v_inst_3375_);
lean_closure_set(v___f_3388_, 3, v_toBind_3376_);
lean_closure_set(v___f_3388_, 4, v___f_3386_);
v_sz_3389_ = lean_array_size(v___y_3384_);
v___x_3390_ = ((size_t)0ULL);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3377_, v___y_3384_, v___f_3388_, v_sz_3389_, v___x_3390_, v___x_3385_);
v___x_3392_ = lean_apply_4(v_toBind_3376_, lean_box(0), lean_box(0), v___x_3391_, v___f_3378_);
return v___x_3392_;
}
v___jp_3393_:
{
lean_object* v___x_3399_; 
v___x_3399_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_3379_, v___y_3397_, v___y_3395_, v___y_3396_, v___y_3398_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_3398_);
lean_dec(v___y_3397_);
v___y_3383_ = v___y_3394_;
v___y_3384_ = v___x_3399_;
goto v___jp_3382_;
}
v___jp_3400_:
{
uint8_t v___x_3406_; 
v___x_3406_ = lean_nat_dec_le(v___y_3405_, v___y_3403_);
if (v___x_3406_ == 0)
{
lean_dec(v___y_3403_);
lean_inc(v___y_3405_);
v___y_3394_ = v___y_3401_;
v___y_3395_ = v___y_3402_;
v___y_3396_ = v___y_3405_;
v___y_3397_ = v___y_3404_;
v___y_3398_ = v___y_3405_;
goto v___jp_3393_;
}
else
{
v___y_3394_ = v___y_3401_;
v___y_3395_ = v___y_3402_;
v___y_3396_ = v___y_3405_;
v___y_3397_ = v___y_3404_;
v___y_3398_ = v___y_3403_;
goto v___jp_3393_;
}
}
v___jp_3407_:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3409_ = lean_unsigned_to_nat(0u);
v___x_3410_ = lean_array_get_size(v___y_3408_);
v___x_3411_ = lean_nat_dec_eq(v___x_3410_, v___x_3409_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3412_ = lean_unsigned_to_nat(1u);
v___x_3413_ = lean_nat_sub(v___x_3410_, v___x_3412_);
v___x_3414_ = lean_nat_dec_le(v___x_3409_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_inc(v___x_3413_);
v___y_3401_ = v___x_3409_;
v___y_3402_ = v___y_3408_;
v___y_3403_ = v___x_3413_;
v___y_3404_ = v___x_3410_;
v___y_3405_ = v___x_3413_;
goto v___jp_3400_;
}
else
{
v___y_3401_ = v___x_3409_;
v___y_3402_ = v___y_3408_;
v___y_3403_ = v___x_3413_;
v___y_3404_ = v___x_3410_;
v___y_3405_ = v___x_3409_;
goto v___jp_3400_;
}
}
else
{
lean_dec_ref(v___f_3379_);
v___y_3383_ = v___x_3409_;
v___y_3384_ = v___y_3408_;
goto v___jp_3382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object* v_toApplicative_3430_, lean_object* v___x_3431_, lean_object* v_inst_3432_, lean_object* v_toBind_3433_, lean_object* v_inst_3434_, lean_object* v___f_3435_, lean_object* v___f_3436_, lean_object* v___f_3437_, lean_object* v_____s_3438_){
_start:
{
uint8_t v___x_2003__boxed_3439_; lean_object* v_res_3440_; 
v___x_2003__boxed_3439_ = lean_unbox(v___x_3431_);
v_res_3440_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_toApplicative_3430_, v___x_2003__boxed_3439_, v_inst_3432_, v_toBind_3433_, v_inst_3434_, v___f_3435_, v___f_3436_, v___f_3437_, v_____s_3438_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object* v_traceElem_3441_, lean_object* v_toApplicative_3442_, lean_object* v___f_3443_, lean_object* v___f_3444_, lean_object* v_____s_3445_, uint8_t v___x_3446_, lean_object* v_____do__lift_3447_){
_start:
{
lean_object* v_ref_3448_; lean_object* v_msg_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3474_; 
v_ref_3448_ = lean_ctor_get(v_traceElem_3441_, 0);
v_msg_3449_ = lean_ctor_get(v_traceElem_3441_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_traceElem_3441_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3451_ = v_traceElem_3441_;
v_isShared_3452_ = v_isSharedCheck_3474_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_msg_3449_);
lean_inc(v_ref_3448_);
lean_dec(v_traceElem_3441_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3474_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v_ref_3466_; lean_object* v___y_3468_; lean_object* v___x_3471_; 
v_ref_3466_ = l_Lean_replaceRef(v_ref_3448_, v_____do__lift_3447_);
lean_dec(v_ref_3448_);
v___x_3471_ = l_Lean_Syntax_getPos_x3f(v_ref_3466_, v___x_3446_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v___x_3472_; 
v___x_3472_ = lean_unsigned_to_nat(0u);
v___y_3468_ = v___x_3472_;
goto v___jp_3467_;
}
else
{
lean_object* v_val_3473_; 
v_val_3473_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_val_3473_);
lean_dec_ref(v___x_3471_);
v___y_3468_ = v_val_3473_;
goto v___jp_3467_;
}
v___jp_3453_:
{
lean_object* v_toPure_3456_; lean_object* v___x_3458_; 
v_toPure_3456_ = lean_ctor_get(v_toApplicative_3442_, 1);
lean_inc(v_toPure_3456_);
lean_dec_ref(v_toApplicative_3442_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 1, v___y_3455_);
lean_ctor_set(v___x_3451_, 0, v___y_3454_);
v___x_3458_ = v___x_3451_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___y_3454_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v___y_3455_);
v___x_3458_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v_pos2traces_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3459_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
lean_inc_ref(v___x_3458_);
lean_inc_ref(v___f_3444_);
lean_inc_ref(v___f_3443_);
v___x_3460_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_3443_, v___f_3444_, v_____s_3445_, v___x_3458_, v___x_3459_);
v___x_3461_ = lean_array_push(v___x_3460_, v_msg_3449_);
v_pos2traces_3462_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3443_, v___f_3444_, v_____s_3445_, v___x_3458_, v___x_3461_);
v___x_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3463_, 0, v_pos2traces_3462_);
v___x_3464_ = lean_apply_2(v_toPure_3456_, lean_box(0), v___x_3463_);
return v___x_3464_;
}
}
v___jp_3467_:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_Syntax_getTailPos_x3f(v_ref_3466_, v___x_3446_);
lean_dec(v_ref_3466_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_inc(v___y_3468_);
v___y_3454_ = v___y_3468_;
v___y_3455_ = v___y_3468_;
goto v___jp_3453_;
}
else
{
lean_object* v_val_3470_; 
v_val_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_val_3470_);
lean_dec_ref(v___x_3469_);
v___y_3454_ = v___y_3468_;
v___y_3455_ = v_val_3470_;
goto v___jp_3453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object* v_traceElem_3475_, lean_object* v_toApplicative_3476_, lean_object* v___f_3477_, lean_object* v___f_3478_, lean_object* v_____s_3479_, lean_object* v___x_3480_, lean_object* v_____do__lift_3481_){
_start:
{
uint8_t v___x_2128__boxed_3482_; lean_object* v_res_3483_; 
v___x_2128__boxed_3482_ = lean_unbox(v___x_3480_);
v_res_3483_ = l_Lean_addTraceAsMessages___redArg___lam__9(v_traceElem_3475_, v_toApplicative_3476_, v___f_3477_, v___f_3478_, v_____s_3479_, v___x_2128__boxed_3482_, v_____do__lift_3481_);
lean_dec(v_____do__lift_3481_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object* v_inst_3484_, lean_object* v_toApplicative_3485_, lean_object* v___f_3486_, lean_object* v___f_3487_, uint8_t v___x_3488_, lean_object* v_toBind_3489_, lean_object* v_traceElem_3490_, lean_object* v_____s_3491_){
_start:
{
lean_object* v_getRef_3492_; lean_object* v___x_3493_; lean_object* v___f_3494_; lean_object* v___x_3495_; 
v_getRef_3492_ = lean_ctor_get(v_inst_3484_, 0);
lean_inc(v_getRef_3492_);
lean_dec_ref(v_inst_3484_);
v___x_3493_ = lean_box(v___x_3488_);
v___f_3494_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_3494_, 0, v_traceElem_3490_);
lean_closure_set(v___f_3494_, 1, v_toApplicative_3485_);
lean_closure_set(v___f_3494_, 2, v___f_3486_);
lean_closure_set(v___f_3494_, 3, v___f_3487_);
lean_closure_set(v___f_3494_, 4, v_____s_3491_);
lean_closure_set(v___f_3494_, 5, v___x_3493_);
v___x_3495_ = lean_apply_4(v_toBind_3489_, lean_box(0), lean_box(0), v_getRef_3492_, v___f_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object* v_inst_3496_, lean_object* v_toApplicative_3497_, lean_object* v___f_3498_, lean_object* v___f_3499_, lean_object* v___x_3500_, lean_object* v_toBind_3501_, lean_object* v_traceElem_3502_, lean_object* v_____s_3503_){
_start:
{
uint8_t v___x_2188__boxed_3504_; lean_object* v_res_3505_; 
v___x_2188__boxed_3504_ = lean_unbox(v___x_3500_);
v_res_3505_ = l_Lean_addTraceAsMessages___redArg___lam__10(v_inst_3496_, v_toApplicative_3497_, v___f_3498_, v___f_3499_, v___x_2188__boxed_3504_, v_toBind_3501_, v_traceElem_3502_, v_____s_3503_);
return v_res_3505_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0(void){
_start:
{
lean_object* v___x_3506_; lean_object* v___f_3507_; 
v___x_3506_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_3507_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3507_, 0, v___x_3506_);
return v___f_3507_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___f_3508_; lean_object* v___f_3509_; 
v___f_3508_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__0, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0);
v___f_3509_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3509_, 0, v___f_3508_);
lean_closure_set(v___f_3509_, 1, v___f_3508_);
return v___f_3509_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = lean_box(0);
v___x_3514_ = lean_unsigned_to_nat(16u);
v___x_3515_ = lean_mk_array(v___x_3514_, v___x_3513_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v_pos2traces_3518_; 
v___x_3516_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__4, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4);
v___x_3517_ = lean_unsigned_to_nat(0u);
v_pos2traces_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_3518_, 0, v___x_3517_);
lean_ctor_set(v_pos2traces_3518_, 1, v___x_3516_);
return v_pos2traces_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11(lean_object* v_inst_3519_, lean_object* v_toApplicative_3520_, lean_object* v_toBind_3521_, lean_object* v_inst_3522_, lean_object* v___f_3523_, lean_object* v_traces_3524_){
_start:
{
uint8_t v___x_3525_; 
v___x_3525_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___f_3526_; lean_object* v___f_3527_; lean_object* v___x_3528_; lean_object* v___f_3529_; lean_object* v_pos2traces_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___f_3526_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__1, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1);
v___f_3527_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___lam__11___closed__3));
v___x_3528_ = lean_box(v___x_3525_);
lean_inc(v_toBind_3521_);
v___f_3529_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3529_, 0, v_inst_3519_);
lean_closure_set(v___f_3529_, 1, v_toApplicative_3520_);
lean_closure_set(v___f_3529_, 2, v___f_3526_);
lean_closure_set(v___f_3529_, 3, v___f_3527_);
lean_closure_set(v___f_3529_, 4, v___x_3528_);
lean_closure_set(v___f_3529_, 5, v_toBind_3521_);
v_pos2traces_3530_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__5, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5);
v___x_3531_ = l_Lean_PersistentArray_forIn___redArg(v_inst_3522_, v_traces_3524_, v_pos2traces_3530_, v___f_3529_);
v___x_3532_ = lean_apply_4(v_toBind_3521_, lean_box(0), lean_box(0), v___x_3531_, v___f_3523_);
return v___x_3532_;
}
else
{
lean_object* v_toPure_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_dec(v___f_3523_);
lean_dec_ref(v_inst_3522_);
lean_dec(v_toBind_3521_);
lean_dec_ref(v_inst_3519_);
v_toPure_3533_ = lean_ctor_get(v_toApplicative_3520_, 1);
lean_inc(v_toPure_3533_);
lean_dec_ref(v_toApplicative_3520_);
v___x_3534_ = lean_box(0);
v___x_3535_ = lean_apply_2(v_toPure_3533_, lean_box(0), v___x_3534_);
return v___x_3535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___boxed(lean_object* v_inst_3536_, lean_object* v_toApplicative_3537_, lean_object* v_toBind_3538_, lean_object* v_inst_3539_, lean_object* v___f_3540_, lean_object* v_traces_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lean_addTraceAsMessages___redArg___lam__11(v_inst_3536_, v_toApplicative_3537_, v_toBind_3538_, v_inst_3539_, v___f_3540_, v_traces_3541_);
lean_dec_ref(v_traces_3541_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12(lean_object* v___x_3543_, lean_object* v_toApplicative_3544_, lean_object* v_inst_3545_, lean_object* v_toBind_3546_, lean_object* v_inst_3547_, lean_object* v___f_3548_, lean_object* v___f_3549_, lean_object* v___f_3550_, lean_object* v_inst_3551_, lean_object* v_inst_3552_, lean_object* v_____do__lift_3553_){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = l_Lean_trace_profiler_output;
v___x_3555_ = l_Lean_Option_get_x3f___redArg(v___x_3543_, v_____do__lift_3553_, v___x_3554_);
if (lean_obj_tag(v___x_3555_) == 0)
{
uint8_t v___x_3556_; lean_object* v___x_3557_; lean_object* v___f_3558_; lean_object* v___f_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3556_ = 1;
v___x_3557_ = lean_box(v___x_3556_);
lean_inc_ref_n(v_inst_3547_, 2);
lean_inc_n(v_toBind_3546_, 2);
lean_inc_ref(v_toApplicative_3544_);
v___f_3558_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__8___boxed), 9, 8);
lean_closure_set(v___f_3558_, 0, v_toApplicative_3544_);
lean_closure_set(v___f_3558_, 1, v___x_3557_);
lean_closure_set(v___f_3558_, 2, v_inst_3545_);
lean_closure_set(v___f_3558_, 3, v_toBind_3546_);
lean_closure_set(v___f_3558_, 4, v_inst_3547_);
lean_closure_set(v___f_3558_, 5, v___f_3548_);
lean_closure_set(v___f_3558_, 6, v___f_3549_);
lean_closure_set(v___f_3558_, 7, v___f_3550_);
v___f_3559_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__11___boxed), 6, 5);
lean_closure_set(v___f_3559_, 0, v_inst_3551_);
lean_closure_set(v___f_3559_, 1, v_toApplicative_3544_);
lean_closure_set(v___f_3559_, 2, v_toBind_3546_);
lean_closure_set(v___f_3559_, 3, v_inst_3547_);
lean_closure_set(v___f_3559_, 4, v___f_3558_);
v___x_3560_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3547_, v_inst_3552_);
v___x_3561_ = lean_apply_4(v_toBind_3546_, lean_box(0), lean_box(0), v___x_3560_, v___f_3559_);
return v___x_3561_;
}
else
{
lean_object* v_toPure_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
lean_dec_ref(v___x_3555_);
lean_dec_ref(v_inst_3552_);
lean_dec_ref(v_inst_3551_);
lean_dec_ref(v___f_3550_);
lean_dec_ref(v___f_3549_);
lean_dec(v___f_3548_);
lean_dec_ref(v_inst_3547_);
lean_dec(v_toBind_3546_);
lean_dec_ref(v_inst_3545_);
v_toPure_3562_ = lean_ctor_get(v_toApplicative_3544_, 1);
lean_inc(v_toPure_3562_);
lean_dec_ref(v_toApplicative_3544_);
v___x_3563_ = lean_box(0);
v___x_3564_ = lean_apply_2(v_toPure_3562_, lean_box(0), v___x_3563_);
return v___x_3564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12___boxed(lean_object* v___x_3565_, lean_object* v_toApplicative_3566_, lean_object* v_inst_3567_, lean_object* v_toBind_3568_, lean_object* v_inst_3569_, lean_object* v___f_3570_, lean_object* v___f_3571_, lean_object* v___f_3572_, lean_object* v_inst_3573_, lean_object* v_inst_3574_, lean_object* v_____do__lift_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_addTraceAsMessages___redArg___lam__12(v___x_3565_, v_toApplicative_3566_, v_inst_3567_, v_toBind_3568_, v_inst_3569_, v___f_3570_, v___f_3571_, v___f_3572_, v_inst_3573_, v_inst_3574_, v_____do__lift_3575_);
lean_dec_ref(v_____do__lift_3575_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object* v_inst_3579_, lean_object* v_inst_3580_, lean_object* v_inst_3581_, lean_object* v_inst_3582_, lean_object* v_inst_3583_){
_start:
{
lean_object* v___x_3584_; lean_object* v_toApplicative_3585_; lean_object* v_toBind_3586_; lean_object* v___f_3587_; lean_object* v___f_3588_; lean_object* v___f_3589_; lean_object* v___f_3590_; lean_object* v___x_3591_; 
v___x_3584_ = l_Lean_KVMap_instValueString;
v_toApplicative_3585_ = lean_ctor_get(v_inst_3580_, 0);
lean_inc_ref_n(v_toApplicative_3585_, 2);
v_toBind_3586_ = lean_ctor_get(v_inst_3580_, 1);
lean_inc_n(v_toBind_3586_, 2);
v___f_3587_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3587_, 0, v_toApplicative_3585_);
v___f_3588_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__0));
v___f_3589_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__1));
v___f_3590_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3590_, 0, v___x_3584_);
lean_closure_set(v___f_3590_, 1, v_toApplicative_3585_);
lean_closure_set(v___f_3590_, 2, v_inst_3582_);
lean_closure_set(v___f_3590_, 3, v_toBind_3586_);
lean_closure_set(v___f_3590_, 4, v_inst_3580_);
lean_closure_set(v___f_3590_, 5, v___f_3587_);
lean_closure_set(v___f_3590_, 6, v___f_3588_);
lean_closure_set(v___f_3590_, 7, v___f_3589_);
lean_closure_set(v___f_3590_, 8, v_inst_3581_);
lean_closure_set(v___f_3590_, 9, v_inst_3583_);
v___x_3591_ = lean_apply_4(v_toBind_3586_, lean_box(0), lean_box(0), v_inst_3579_, v___f_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object* v_m_3592_, lean_object* v_inst_3593_, lean_object* v_inst_3594_, lean_object* v_inst_3595_, lean_object* v_inst_3596_, lean_object* v_inst_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_addTraceAsMessages___redArg(v_inst_3593_, v_inst_3594_, v_inst_3595_, v_inst_3596_, v_inst_3597_);
return v___x_3598_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = lean_unsigned_to_nat(2826257906u);
v___x_3641_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3642_ = l_Lean_Name_num___override(v___x_3641_, v___x_3640_);
return v___x_3642_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3645_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3646_ = l_Lean_Name_str___override(v___x_3645_, v___x_3644_);
return v___x_3646_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3649_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3650_ = l_Lean_Name_str___override(v___x_3649_, v___x_3648_);
return v___x_3650_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = lean_unsigned_to_nat(2u);
v___x_3652_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3653_ = l_Lean_Name_num___override(v___x_3652_, v___x_3651_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3655_; uint8_t v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3655_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3656_ = 0;
v___x_3657_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3658_ = l_Lean_registerTraceClass(v___x_3655_, v___x_3656_, v___x_3657_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object* v_a_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
return v_res_3660_;
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
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_inheritedTraceOptions = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_inheritedTraceOptions);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_threshold = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_threshold);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_useHeartbeats = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_useHeartbeats);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_output = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_output);
lean_dec_ref(res);
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
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
