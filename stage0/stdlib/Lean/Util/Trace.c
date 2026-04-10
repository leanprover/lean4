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
lean_inc_ref(v_traces_169_);
lean_dec_ref(v_____do__lift_168_);
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
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg(lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_inst_179_){
_start:
{
lean_object* v_toApplicative_180_; lean_object* v_toBind_181_; lean_object* v_getTraceState_182_; lean_object* v_toPure_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___f_186_; lean_object* v___x_187_; 
v_toApplicative_180_ = lean_ctor_get(v_inst_177_, 0);
v_toBind_181_ = lean_ctor_get(v_inst_177_, 1);
lean_inc_n(v_toBind_181_, 2);
v_getTraceState_182_ = lean_ctor_get(v_inst_178_, 1);
lean_inc(v_getTraceState_182_);
lean_dec_ref(v_inst_178_);
v_toPure_183_ = lean_ctor_get(v_toApplicative_180_, 1);
lean_inc_n(v_toPure_183_, 2);
v___f_184_ = ((lean_object*)(l_Lean_printTraces___redArg___closed__0));
v___f_185_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_185_, 0, v_toPure_183_);
v___f_186_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__4), 7, 6);
lean_closure_set(v___f_186_, 0, v_toPure_183_);
lean_closure_set(v___f_186_, 1, v___f_184_);
lean_closure_set(v___f_186_, 2, v_inst_179_);
lean_closure_set(v___f_186_, 3, v_toBind_181_);
lean_closure_set(v___f_186_, 4, v_inst_177_);
lean_closure_set(v___f_186_, 5, v___f_185_);
v___x_187_ = lean_apply_4(v_toBind_181_, lean_box(0), lean_box(0), v_getTraceState_182_, v___f_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces(lean_object* v_m_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_inst_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_printTraces___redArg(v_inst_189_, v_inst_190_, v_inst_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0(lean_object* v_x_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_unsigned_to_nat(32u);
v___x_195_ = lean_mk_empty_array_with_capacity(v___x_194_);
lean_dec_ref(v___x_195_);
v___x_196_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__2, &l_Lean_instInhabitedTraceState_default___closed__2_once, _init_l_Lean_instInhabitedTraceState_default___closed__2);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0___boxed(lean_object* v_x_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_resetTraceState___redArg___lam__0(v_x_197_);
lean_dec_ref(v_x_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg(lean_object* v_inst_200_){
_start:
{
lean_object* v_modifyTraceState_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v_modifyTraceState_201_ = lean_ctor_get(v_inst_200_, 0);
lean_inc(v_modifyTraceState_201_);
lean_dec_ref(v_inst_200_);
v___f_202_ = ((lean_object*)(l_Lean_resetTraceState___redArg___closed__0));
v___x_203_ = lean_apply_1(v_modifyTraceState_201_, v___f_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState(lean_object* v_m_204_, lean_object* v_inst_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_resetTraceState___redArg(v_inst_205_);
return v___x_206_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(lean_object* v_a_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
uint8_t v___x_209_; 
v___x_209_ = 0;
return v___x_209_;
}
else
{
lean_object* v_key_210_; lean_object* v_tail_211_; uint8_t v___x_212_; 
v_key_210_ = lean_ctor_get(v_x_208_, 0);
v_tail_211_ = lean_ctor_get(v_x_208_, 2);
v___x_212_ = lean_name_eq(v_key_210_, v_a_207_);
if (v___x_212_ == 0)
{
v_x_208_ = v_tail_211_;
goto _start;
}
else
{
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_214_, lean_object* v_x_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_214_, v_x_215_);
lean_dec(v_x_215_);
lean_dec(v_a_214_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_218_; uint64_t v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(1723u);
v___x_219_ = lean_uint64_of_nat(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(lean_object* v_m_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_buckets_222_; lean_object* v___x_223_; uint64_t v___y_225_; 
v_buckets_222_ = lean_ctor_get(v_m_220_, 1);
v___x_223_ = lean_array_get_size(v_buckets_222_);
if (lean_obj_tag(v_a_221_) == 0)
{
uint64_t v___x_239_; 
v___x_239_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_225_ = v___x_239_;
goto v___jp_224_;
}
else
{
uint64_t v_hash_240_; 
v_hash_240_ = lean_ctor_get_uint64(v_a_221_, sizeof(void*)*2);
v___y_225_ = v_hash_240_;
goto v___jp_224_;
}
v___jp_224_:
{
uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v_fold_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_226_ = 32ULL;
v___x_227_ = lean_uint64_shift_right(v___y_225_, v___x_226_);
v_fold_228_ = lean_uint64_xor(v___y_225_, v___x_227_);
v___x_229_ = 16ULL;
v___x_230_ = lean_uint64_shift_right(v_fold_228_, v___x_229_);
v___x_231_ = lean_uint64_xor(v_fold_228_, v___x_230_);
v___x_232_ = lean_uint64_to_usize(v___x_231_);
v___x_233_ = lean_usize_of_nat(v___x_223_);
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_sub(v___x_233_, v___x_234_);
v___x_236_ = lean_usize_land(v___x_232_, v___x_235_);
v___x_237_ = lean_array_uget_borrowed(v_buckets_222_, v___x_236_);
v___x_238_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_221_, v___x_237_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___boxed(lean_object* v_m_241_, lean_object* v_a_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_241_, v_a_242_);
lean_dec(v_a_242_);
lean_dec_ref(v_m_241_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object* v_inherited_245_, lean_object* v_opts_246_, lean_object* v_opt_247_){
_start:
{
lean_object* v_map_253_; lean_object* v___x_254_; 
v_map_253_ = lean_ctor_get(v_opts_246_, 0);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_253_, v_opt_247_);
if (lean_obj_tag(v___x_254_) == 0)
{
goto v___jp_248_;
}
else
{
lean_object* v_val_255_; 
v_val_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_val_255_);
lean_dec_ref(v___x_254_);
if (lean_obj_tag(v_val_255_) == 1)
{
uint8_t v_v_256_; 
v_v_256_ = lean_ctor_get_uint8(v_val_255_, 0);
lean_dec_ref(v_val_255_);
return v_v_256_;
}
else
{
lean_dec(v_val_255_);
goto v___jp_248_;
}
}
v___jp_248_:
{
if (lean_obj_tag(v_opt_247_) == 1)
{
lean_object* v_pre_249_; uint8_t v___x_250_; 
v_pre_249_ = lean_ctor_get(v_opt_247_, 0);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_inherited_245_, v_opt_247_);
if (v___x_250_ == 0)
{
return v___x_250_;
}
else
{
v_opt_247_ = v_pre_249_;
goto _start;
}
}
else
{
uint8_t v___x_252_; 
v___x_252_ = 0;
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go___boxed(lean_object* v_inherited_257_, lean_object* v_opts_258_, lean_object* v_opt_259_){
_start:
{
uint8_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_257_, v_opts_258_, v_opt_259_);
lean_dec(v_opt_259_);
lean_dec_ref(v_opts_258_);
lean_dec_ref(v_inherited_257_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(lean_object* v_00_u03b2_262_, lean_object* v_m_263_, lean_object* v_a_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_263_, v_a_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(lean_object* v_00_u03b2_266_, lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(v_00_u03b2_266_, v_m_267_, v_a_268_);
lean_dec(v_a_268_);
lean_dec_ref(v_m_267_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(lean_object* v_00_u03b2_271_, lean_object* v_a_272_, lean_object* v_x_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_272_, v_x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_275_, lean_object* v_a_276_, lean_object* v_x_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(v_00_u03b2_275_, v_a_276_, v_x_277_);
lean_dec(v_x_277_);
lean_dec(v_a_276_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT uint8_t l_Lean_checkTraceOption(lean_object* v_inherited_283_, lean_object* v_opts_284_, lean_object* v_cls_285_){
_start:
{
uint8_t v_hasTrace_286_; 
v_hasTrace_286_ = lean_ctor_get_uint8(v_opts_284_, sizeof(void*)*1);
if (v_hasTrace_286_ == 0)
{
lean_dec(v_cls_285_);
return v_hasTrace_286_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_287_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_288_ = l_Lean_Name_append(v___x_287_, v_cls_285_);
v___x_289_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_283_, v_opts_284_, v___x_288_);
lean_dec(v___x_288_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkTraceOption___boxed(lean_object* v_inherited_290_, lean_object* v_opts_291_, lean_object* v_cls_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Lean_checkTraceOption(v_inherited_290_, v_opts_291_, v_cls_292_);
lean_dec_ref(v_opts_291_);
lean_dec_ref(v_inherited_290_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0(lean_object* v_toPure_295_, lean_object* v_cls_296_, lean_object* v_____do__lift_297_, lean_object* v_____do__lift_298_){
_start:
{
uint8_t v_hasTrace_299_; 
v_hasTrace_299_ = lean_ctor_get_uint8(v_____do__lift_298_, sizeof(void*)*1);
if (v_hasTrace_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_cls_296_);
v___x_300_ = lean_box(v_hasTrace_299_);
v___x_301_ = lean_apply_2(v_toPure_295_, lean_box(0), v___x_300_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_302_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_303_ = l_Lean_Name_append(v___x_302_, v_cls_296_);
v___x_304_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_297_, v_____do__lift_298_, v___x_303_);
lean_dec(v___x_303_);
v___x_305_ = lean_box(v___x_304_);
v___x_306_ = lean_apply_2(v_toPure_295_, lean_box(0), v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0___boxed(lean_object* v_toPure_307_, lean_object* v_cls_308_, lean_object* v_____do__lift_309_, lean_object* v_____do__lift_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_isTracingEnabledFor___redArg___lam__0(v_toPure_307_, v_cls_308_, v_____do__lift_309_, v_____do__lift_310_);
lean_dec_ref(v_____do__lift_310_);
lean_dec_ref(v_____do__lift_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__1(lean_object* v_toPure_312_, lean_object* v_cls_313_, lean_object* v_toBind_314_, lean_object* v_inst_315_, lean_object* v_____do__lift_316_){
_start:
{
lean_object* v___f_317_; lean_object* v___x_318_; 
v___f_317_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_317_, 0, v_toPure_312_);
lean_closure_set(v___f_317_, 1, v_cls_313_);
lean_closure_set(v___f_317_, 2, v_____do__lift_316_);
v___x_318_ = lean_apply_4(v_toBind_314_, lean_box(0), lean_box(0), v_inst_315_, v___f_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_cls_322_){
_start:
{
lean_object* v_toApplicative_323_; lean_object* v_toBind_324_; lean_object* v_getInheritedTraceOptions_325_; lean_object* v_toPure_326_; lean_object* v___f_327_; lean_object* v___x_328_; 
v_toApplicative_323_ = lean_ctor_get(v_inst_319_, 0);
lean_inc_ref(v_toApplicative_323_);
v_toBind_324_ = lean_ctor_get(v_inst_319_, 1);
lean_inc_n(v_toBind_324_, 2);
lean_dec_ref(v_inst_319_);
v_getInheritedTraceOptions_325_ = lean_ctor_get(v_inst_320_, 2);
lean_inc(v_getInheritedTraceOptions_325_);
lean_dec_ref(v_inst_320_);
v_toPure_326_ = lean_ctor_get(v_toApplicative_323_, 1);
lean_inc(v_toPure_326_);
lean_dec_ref(v_toApplicative_323_);
v___f_327_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_327_, 0, v_toPure_326_);
lean_closure_set(v___f_327_, 1, v_cls_322_);
lean_closure_set(v___f_327_, 2, v_toBind_324_);
lean_closure_set(v___f_327_, 3, v_inst_321_);
v___x_328_ = lean_apply_4(v_toBind_324_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_325_, v___f_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor(lean_object* v_m_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_cls_333_){
_start:
{
lean_object* v_toApplicative_334_; lean_object* v_toBind_335_; lean_object* v_getInheritedTraceOptions_336_; lean_object* v_toPure_337_; lean_object* v___f_338_; lean_object* v___x_339_; 
v_toApplicative_334_ = lean_ctor_get(v_inst_330_, 0);
lean_inc_ref(v_toApplicative_334_);
v_toBind_335_ = lean_ctor_get(v_inst_330_, 1);
lean_inc_n(v_toBind_335_, 2);
lean_dec_ref(v_inst_330_);
v_getInheritedTraceOptions_336_ = lean_ctor_get(v_inst_331_, 2);
lean_inc(v_getInheritedTraceOptions_336_);
lean_dec_ref(v_inst_331_);
v_toPure_337_ = lean_ctor_get(v_toApplicative_334_, 1);
lean_inc(v_toPure_337_);
lean_dec_ref(v_toApplicative_334_);
v___f_338_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_338_, 0, v_toPure_337_);
lean_closure_set(v___f_338_, 1, v_cls_333_);
lean_closure_set(v___f_338_, 2, v_toBind_335_);
lean_closure_set(v___f_338_, 3, v_inst_332_);
v___x_339_ = lean_apply_4(v_toBind_335_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_336_, v___f_338_);
return v___x_339_;
}
}
LEAN_EXPORT uint8_t lean_is_trace_class_enabled(lean_object* v_opts_340_, lean_object* v_cls_341_){
_start:
{
uint8_t v_hasTrace_343_; 
v_hasTrace_343_ = lean_ctor_get_uint8(v_opts_340_, sizeof(void*)*1);
if (v_hasTrace_343_ == 0)
{
lean_dec(v_cls_341_);
lean_dec_ref(v_opts_340_);
return v_hasTrace_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_344_ = l_Lean_inheritedTraceOptions;
v___x_345_ = lean_st_ref_get(v___x_344_);
v___x_346_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_347_ = l_Lean_Name_append(v___x_346_, v_cls_341_);
v___x_348_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_345_, v_opts_340_, v___x_347_);
lean_dec(v___x_347_);
lean_dec_ref(v_opts_340_);
lean_dec(v___x_345_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object* v_opts_349_, lean_object* v_cls_350_, lean_object* v_a_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = lean_is_trace_class_enabled(v_opts_349_, v_cls_350_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object* v_toPure_354_, lean_object* v_s_355_){
_start:
{
lean_object* v_traces_356_; lean_object* v___x_357_; 
v_traces_356_ = lean_ctor_get(v_s_355_, 0);
lean_inc_ref(v_traces_356_);
lean_dec_ref(v_s_355_);
v___x_357_ = lean_apply_2(v_toPure_354_, lean_box(0), v_traces_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object* v_inst_358_, lean_object* v_inst_359_){
_start:
{
lean_object* v_toApplicative_360_; lean_object* v_toBind_361_; lean_object* v_getTraceState_362_; lean_object* v_toPure_363_; lean_object* v___f_364_; lean_object* v___x_365_; 
v_toApplicative_360_ = lean_ctor_get(v_inst_358_, 0);
lean_inc_ref(v_toApplicative_360_);
v_toBind_361_ = lean_ctor_get(v_inst_358_, 1);
lean_inc(v_toBind_361_);
lean_dec_ref(v_inst_358_);
v_getTraceState_362_ = lean_ctor_get(v_inst_359_, 1);
lean_inc(v_getTraceState_362_);
lean_dec_ref(v_inst_359_);
v_toPure_363_ = lean_ctor_get(v_toApplicative_360_, 1);
lean_inc(v_toPure_363_);
lean_dec_ref(v_toApplicative_360_);
v___f_364_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_364_, 0, v_toPure_363_);
v___x_365_ = lean_apply_4(v_toBind_361_, lean_box(0), lean_box(0), v_getTraceState_362_, v___f_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object* v_m_366_, lean_object* v_inst_367_, lean_object* v_inst_368_){
_start:
{
lean_object* v_toApplicative_369_; lean_object* v_toBind_370_; lean_object* v_getTraceState_371_; lean_object* v_toPure_372_; lean_object* v___f_373_; lean_object* v___x_374_; 
v_toApplicative_369_ = lean_ctor_get(v_inst_367_, 0);
lean_inc_ref(v_toApplicative_369_);
v_toBind_370_ = lean_ctor_get(v_inst_367_, 1);
lean_inc(v_toBind_370_);
lean_dec_ref(v_inst_367_);
v_getTraceState_371_ = lean_ctor_get(v_inst_368_, 1);
lean_inc(v_getTraceState_371_);
lean_dec_ref(v_inst_368_);
v_toPure_372_ = lean_ctor_get(v_toApplicative_369_, 1);
lean_inc(v_toPure_372_);
lean_dec_ref(v_toApplicative_369_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_373_, 0, v_toPure_372_);
v___x_374_ = lean_apply_4(v_toBind_370_, lean_box(0), lean_box(0), v_getTraceState_371_, v___f_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object* v_f_375_, lean_object* v_s_376_){
_start:
{
uint64_t v_tid_377_; lean_object* v_traces_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_386_; 
v_tid_377_ = lean_ctor_get_uint64(v_s_376_, sizeof(void*)*1);
v_traces_378_ = lean_ctor_get(v_s_376_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v_s_376_);
if (v_isSharedCheck_386_ == 0)
{
v___x_380_ = v_s_376_;
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_traces_378_);
lean_dec(v_s_376_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = lean_apply_1(v_f_375_, v_traces_378_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
lean_ctor_set_uint64(v_reuseFailAlloc_385_, sizeof(void*)*1, v_tid_377_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object* v_inst_387_, lean_object* v_f_388_){
_start:
{
lean_object* v_modifyTraceState_389_; lean_object* v___f_390_; lean_object* v___x_391_; 
v_modifyTraceState_389_ = lean_ctor_get(v_inst_387_, 0);
lean_inc(v_modifyTraceState_389_);
lean_dec_ref(v_inst_387_);
v___f_390_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_390_, 0, v_f_388_);
v___x_391_ = lean_apply_1(v_modifyTraceState_389_, v___f_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object* v_m_392_, lean_object* v_inst_393_, lean_object* v_f_394_){
_start:
{
lean_object* v_modifyTraceState_395_; lean_object* v___f_396_; lean_object* v___x_397_; 
v_modifyTraceState_395_ = lean_ctor_get(v_inst_393_, 0);
lean_inc(v_modifyTraceState_395_);
lean_dec_ref(v_inst_393_);
v___f_396_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_396_, 0, v_f_394_);
v___x_397_ = lean_apply_1(v_modifyTraceState_395_, v___f_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object* v_s_398_, lean_object* v_x_399_){
_start:
{
lean_inc_ref(v_s_398_);
return v_s_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object* v_s_400_, lean_object* v_x_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_setTraceState___redArg___lam__0(v_s_400_, v_x_401_);
lean_dec_ref(v_x_401_);
lean_dec_ref(v_s_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object* v_inst_403_, lean_object* v_s_404_){
_start:
{
lean_object* v_modifyTraceState_405_; lean_object* v___f_406_; lean_object* v___x_407_; 
v_modifyTraceState_405_ = lean_ctor_get(v_inst_403_, 0);
lean_inc(v_modifyTraceState_405_);
lean_dec_ref(v_inst_403_);
v___f_406_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_406_, 0, v_s_404_);
v___x_407_ = lean_apply_1(v_modifyTraceState_405_, v___f_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object* v_m_408_, lean_object* v_inst_409_, lean_object* v_s_410_){
_start:
{
lean_object* v_modifyTraceState_411_; lean_object* v___f_412_; lean_object* v___x_413_; 
v_modifyTraceState_411_ = lean_ctor_get(v_inst_409_, 0);
lean_inc(v_modifyTraceState_411_);
lean_dec_ref(v_inst_409_);
v___f_412_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_412_, 0, v_s_410_);
v___x_413_ = lean_apply_1(v_modifyTraceState_411_, v___f_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object* v_s_414_){
_start:
{
uint64_t v_tid_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_425_; 
v_tid_415_ = lean_ctor_get_uint64(v_s_414_, sizeof(void*)*1);
v_isSharedCheck_425_ = !lean_is_exclusive(v_s_414_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_s_414_, 0);
lean_dec(v_unused_426_);
v___x_417_ = v_s_414_;
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
else
{
lean_dec(v_s_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_419_ = lean_unsigned_to_nat(32u);
v___x_420_ = lean_mk_empty_array_with_capacity(v___x_419_);
lean_dec_ref(v___x_420_);
v___x_421_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__1, &l_Lean_instInhabitedTraceState_default___closed__1_once, _init_l_Lean_instInhabitedTraceState_default___closed__1);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_421_);
v___x_423_ = v___x_417_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
lean_ctor_set_uint64(v_reuseFailAlloc_424_, sizeof(void*)*1, v_tid_415_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object* v_toPure_427_, lean_object* v_oldTraces_428_, lean_object* v_____r_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_apply_2(v_toPure_427_, lean_box(0), v_oldTraces_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object* v_toPure_431_, lean_object* v_modifyTraceState_432_, lean_object* v___f_433_, lean_object* v_toBind_434_, lean_object* v_oldTraces_435_){
_start:
{
lean_object* v___f_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___f_436_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_436_, 0, v_toPure_431_);
lean_closure_set(v___f_436_, 1, v_oldTraces_435_);
v___x_437_ = lean_apply_1(v_modifyTraceState_432_, v___f_433_);
v___x_438_ = lean_apply_4(v_toBind_434_, lean_box(0), lean_box(0), v___x_437_, v___f_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object* v_inst_440_, lean_object* v_inst_441_){
_start:
{
lean_object* v_toApplicative_442_; lean_object* v_toBind_443_; lean_object* v_modifyTraceState_444_; lean_object* v_getTraceState_445_; lean_object* v_toPure_446_; lean_object* v___f_447_; lean_object* v___f_448_; lean_object* v___f_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_toApplicative_442_ = lean_ctor_get(v_inst_440_, 0);
lean_inc_ref(v_toApplicative_442_);
v_toBind_443_ = lean_ctor_get(v_inst_440_, 1);
lean_inc_n(v_toBind_443_, 3);
lean_dec_ref(v_inst_440_);
v_modifyTraceState_444_ = lean_ctor_get(v_inst_441_, 0);
lean_inc(v_modifyTraceState_444_);
v_getTraceState_445_ = lean_ctor_get(v_inst_441_, 1);
lean_inc(v_getTraceState_445_);
lean_dec_ref(v_inst_441_);
v_toPure_446_ = lean_ctor_get(v_toApplicative_442_, 1);
lean_inc_n(v_toPure_446_, 2);
lean_dec_ref(v_toApplicative_442_);
v___f_447_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0));
v___f_448_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_448_, 0, v_toPure_446_);
lean_closure_set(v___f_448_, 1, v_modifyTraceState_444_);
lean_closure_set(v___f_448_, 2, v___f_447_);
lean_closure_set(v___f_448_, 3, v_toBind_443_);
v___f_449_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_449_, 0, v_toPure_446_);
v___x_450_ = lean_apply_4(v_toBind_443_, lean_box(0), lean_box(0), v_getTraceState_445_, v___f_449_);
v___x_451_ = lean_apply_4(v_toBind_443_, lean_box(0), lean_box(0), v___x_450_, v___f_448_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object* v_m_452_, lean_object* v_inst_453_, lean_object* v_inst_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_453_, v_inst_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object* v_ref_456_, lean_object* v_msg_457_, lean_object* v_s_458_){
_start:
{
uint64_t v_tid_459_; lean_object* v_traces_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_469_; 
v_tid_459_ = lean_ctor_get_uint64(v_s_458_, sizeof(void*)*1);
v_traces_460_ = lean_ctor_get(v_s_458_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v_s_458_);
if (v_isSharedCheck_469_ == 0)
{
v___x_462_ = v_s_458_;
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_traces_460_);
lean_dec(v_s_458_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_ref_456_);
lean_ctor_set(v___x_464_, 1, v_msg_457_);
v___x_465_ = l_Lean_PersistentArray_push___redArg(v_traces_460_, v___x_464_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_465_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set_uint64(v_reuseFailAlloc_468_, sizeof(void*)*1, v_tid_459_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object* v_inst_470_, lean_object* v_ref_471_, lean_object* v_msg_472_){
_start:
{
lean_object* v_modifyTraceState_473_; lean_object* v___f_474_; lean_object* v___x_475_; 
v_modifyTraceState_473_ = lean_ctor_get(v_inst_470_, 0);
lean_inc(v_modifyTraceState_473_);
lean_dec_ref(v_inst_470_);
v___f_474_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__0), 3, 2);
lean_closure_set(v___f_474_, 0, v_ref_471_);
lean_closure_set(v___f_474_, 1, v_msg_472_);
v___x_475_ = lean_apply_1(v_modifyTraceState_473_, v___f_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_msg_478_, lean_object* v_toBind_479_, lean_object* v_ref_480_){
_start:
{
lean_object* v___f_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___f_481_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__1), 3, 2);
lean_closure_set(v___f_481_, 0, v_inst_476_);
lean_closure_set(v___f_481_, 1, v_ref_480_);
v___x_482_ = lean_apply_1(v_inst_477_, v_msg_478_);
v___x_483_ = lean_apply_4(v_toBind_479_, lean_box(0), lean_box(0), v___x_482_, v___f_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_msg_488_){
_start:
{
lean_object* v_toBind_489_; lean_object* v_getRef_490_; lean_object* v___f_491_; lean_object* v___x_492_; 
v_toBind_489_ = lean_ctor_get(v_inst_484_, 1);
lean_inc_n(v_toBind_489_, 2);
lean_dec_ref(v_inst_484_);
v_getRef_490_ = lean_ctor_get(v_inst_486_, 0);
lean_inc(v_getRef_490_);
lean_dec_ref(v_inst_486_);
v___f_491_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__2), 5, 4);
lean_closure_set(v___f_491_, 0, v_inst_485_);
lean_closure_set(v___f_491_, 1, v_inst_487_);
lean_closure_set(v___f_491_, 2, v_msg_488_);
lean_closure_set(v___f_491_, 3, v_toBind_489_);
v___x_492_ = lean_apply_4(v_toBind_489_, lean_box(0), lean_box(0), v_getRef_490_, v___f_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object* v_m_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_msg_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_addRawTrace___redArg(v_inst_494_, v_inst_495_, v_inst_496_, v_inst_497_, v_msg_498_);
return v___x_499_;
}
}
static double _init_l_Lean_addTrace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_500_; double v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_float_of_nat(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object* v_cls_505_, lean_object* v_msg_506_, lean_object* v_ref_507_, lean_object* v_s_508_){
_start:
{
uint64_t v_tid_509_; lean_object* v_traces_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_526_; 
v_tid_509_ = lean_ctor_get_uint64(v_s_508_, sizeof(void*)*1);
v_traces_510_ = lean_ctor_get(v_s_508_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v_s_508_);
if (v_isSharedCheck_526_ == 0)
{
v___x_512_ = v_s_508_;
v_isShared_513_ = v_isSharedCheck_526_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_traces_510_);
lean_dec(v_s_508_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_526_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; double v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_514_ = lean_box(0);
v___x_515_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
v___x_516_ = 0;
v___x_517_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_518_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_518_, 0, v_cls_505_);
lean_ctor_set(v___x_518_, 1, v___x_514_);
lean_ctor_set(v___x_518_, 2, v___x_517_);
lean_ctor_set_float(v___x_518_, sizeof(void*)*3, v___x_515_);
lean_ctor_set_float(v___x_518_, sizeof(void*)*3 + 8, v___x_515_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*3 + 16, v___x_516_);
v___x_519_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
v___x_520_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v_msg_506_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v_ref_507_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l_Lean_PersistentArray_push___redArg(v_traces_510_, v___x_521_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_522_);
v___x_524_ = v___x_512_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
lean_ctor_set_uint64(v_reuseFailAlloc_525_, sizeof(void*)*1, v_tid_509_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object* v_inst_527_, lean_object* v_cls_528_, lean_object* v_ref_529_, lean_object* v_msg_530_){
_start:
{
lean_object* v_modifyTraceState_531_; lean_object* v___f_532_; lean_object* v___x_533_; 
v_modifyTraceState_531_ = lean_ctor_get(v_inst_527_, 0);
lean_inc(v_modifyTraceState_531_);
lean_dec_ref(v_inst_527_);
v___f_532_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_532_, 0, v_cls_528_);
lean_closure_set(v___f_532_, 1, v_msg_530_);
lean_closure_set(v___f_532_, 2, v_ref_529_);
v___x_533_ = lean_apply_1(v_modifyTraceState_531_, v___f_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object* v_inst_534_, lean_object* v_cls_535_, lean_object* v_inst_536_, lean_object* v_msg_537_, lean_object* v_toBind_538_, lean_object* v_ref_539_){
_start:
{
lean_object* v___f_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___f_540_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__1), 4, 3);
lean_closure_set(v___f_540_, 0, v_inst_534_);
lean_closure_set(v___f_540_, 1, v_cls_535_);
lean_closure_set(v___f_540_, 2, v_ref_539_);
v___x_541_ = lean_apply_1(v_inst_536_, v_msg_537_);
v___x_542_ = lean_apply_4(v_toBind_538_, lean_box(0), lean_box(0), v___x_541_, v___f_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_cls_547_, lean_object* v_msg_548_){
_start:
{
lean_object* v_toBind_549_; lean_object* v_getRef_550_; lean_object* v___f_551_; lean_object* v___x_552_; 
v_toBind_549_ = lean_ctor_get(v_inst_543_, 1);
lean_inc_n(v_toBind_549_, 2);
lean_dec_ref(v_inst_543_);
v_getRef_550_ = lean_ctor_get(v_inst_545_, 0);
lean_inc(v_getRef_550_);
lean_dec_ref(v_inst_545_);
v___f_551_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__2), 6, 5);
lean_closure_set(v___f_551_, 0, v_inst_544_);
lean_closure_set(v___f_551_, 1, v_cls_547_);
lean_closure_set(v___f_551_, 2, v_inst_546_);
lean_closure_set(v___f_551_, 3, v_msg_548_);
lean_closure_set(v___f_551_, 4, v_toBind_549_);
v___x_552_ = lean_apply_4(v_toBind_549_, lean_box(0), lean_box(0), v_getRef_550_, v___f_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object* v_m_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_cls_558_, lean_object* v_msg_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_addTrace___redArg(v_inst_554_, v_inst_555_, v_inst_556_, v_inst_557_, v_cls_558_, v_msg_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0(lean_object* v_toPure_561_, lean_object* v_msg_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_cls_567_, uint8_t v_____do__lift_568_){
_start:
{
if (v_____do__lift_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v_cls_567_);
lean_dec(v_inst_566_);
lean_dec_ref(v_inst_565_);
lean_dec_ref(v_inst_564_);
lean_dec_ref(v_inst_563_);
lean_dec_ref(v_msg_562_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_apply_2(v_toPure_561_, lean_box(0), v___x_569_);
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_toPure_561_);
v___x_571_ = lean_box(0);
v___x_572_ = lean_apply_1(v_msg_562_, v___x_571_);
v___x_573_ = l_Lean_addTrace___redArg(v_inst_563_, v_inst_564_, v_inst_565_, v_inst_566_, v_cls_567_, v___x_572_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object* v_toPure_574_, lean_object* v_msg_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_cls_580_, lean_object* v_____do__lift_581_){
_start:
{
uint8_t v_____do__lift_147__boxed_582_; lean_object* v_res_583_; 
v_____do__lift_147__boxed_582_ = lean_unbox(v_____do__lift_581_);
v_res_583_ = l_Lean_trace___redArg___lam__0(v_toPure_574_, v_msg_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_inst_579_, v_cls_580_, v_____do__lift_147__boxed_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_cls_589_, lean_object* v_msg_590_){
_start:
{
lean_object* v_toApplicative_591_; lean_object* v_toBind_592_; lean_object* v_getInheritedTraceOptions_593_; lean_object* v_toPure_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_toApplicative_591_ = lean_ctor_get(v_inst_584_, 0);
v_toBind_592_ = lean_ctor_get(v_inst_584_, 1);
lean_inc_n(v_toBind_592_, 3);
v_getInheritedTraceOptions_593_ = lean_ctor_get(v_inst_585_, 2);
lean_inc(v_getInheritedTraceOptions_593_);
v_toPure_594_ = lean_ctor_get(v_toApplicative_591_, 1);
lean_inc_n(v_toPure_594_, 2);
lean_inc(v_cls_589_);
v___f_595_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_595_, 0, v_toPure_594_);
lean_closure_set(v___f_595_, 1, v_msg_590_);
lean_closure_set(v___f_595_, 2, v_inst_584_);
lean_closure_set(v___f_595_, 3, v_inst_585_);
lean_closure_set(v___f_595_, 4, v_inst_586_);
lean_closure_set(v___f_595_, 5, v_inst_587_);
lean_closure_set(v___f_595_, 6, v_cls_589_);
v___f_596_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_596_, 0, v_toPure_594_);
lean_closure_set(v___f_596_, 1, v_cls_589_);
lean_closure_set(v___f_596_, 2, v_toBind_592_);
lean_closure_set(v___f_596_, 3, v_inst_588_);
v___x_597_ = lean_apply_4(v_toBind_592_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_593_, v___f_596_);
v___x_598_ = lean_apply_4(v_toBind_592_, lean_box(0), lean_box(0), v___x_597_, v___f_595_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace(lean_object* v_m_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_cls_605_, lean_object* v_msg_606_){
_start:
{
lean_object* v_toApplicative_607_; lean_object* v_toBind_608_; lean_object* v_getInheritedTraceOptions_609_; lean_object* v_toPure_610_; lean_object* v___f_611_; lean_object* v___f_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_toApplicative_607_ = lean_ctor_get(v_inst_600_, 0);
v_toBind_608_ = lean_ctor_get(v_inst_600_, 1);
lean_inc_n(v_toBind_608_, 3);
v_getInheritedTraceOptions_609_ = lean_ctor_get(v_inst_601_, 2);
lean_inc(v_getInheritedTraceOptions_609_);
v_toPure_610_ = lean_ctor_get(v_toApplicative_607_, 1);
lean_inc_n(v_toPure_610_, 2);
lean_inc(v_cls_605_);
v___f_611_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_611_, 0, v_toPure_610_);
lean_closure_set(v___f_611_, 1, v_msg_606_);
lean_closure_set(v___f_611_, 2, v_inst_600_);
lean_closure_set(v___f_611_, 3, v_inst_601_);
lean_closure_set(v___f_611_, 4, v_inst_602_);
lean_closure_set(v___f_611_, 5, v_inst_603_);
lean_closure_set(v___f_611_, 6, v_cls_605_);
v___f_612_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_612_, 0, v_toPure_610_);
lean_closure_set(v___f_612_, 1, v_cls_605_);
lean_closure_set(v___f_612_, 2, v_toBind_608_);
lean_closure_set(v___f_612_, 3, v_inst_604_);
v___x_613_ = lean_apply_4(v_toBind_608_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_609_, v___f_612_);
v___x_614_ = lean_apply_4(v_toBind_608_, lean_box(0), lean_box(0), v___x_613_, v___f_611_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_cls_619_, lean_object* v_msg_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_addTrace___redArg(v_inst_615_, v_inst_616_, v_inst_617_, v_inst_618_, v_cls_619_, v_msg_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1(lean_object* v_toPure_622_, lean_object* v_toBind_623_, lean_object* v_mkMsg_624_, lean_object* v___f_625_, uint8_t v_____do__lift_626_){
_start:
{
if (v_____do__lift_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v___f_625_);
lean_dec(v_mkMsg_624_);
lean_dec(v_toBind_623_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_apply_2(v_toPure_622_, lean_box(0), v___x_627_);
return v___x_628_;
}
else
{
lean_object* v___x_629_; 
lean_dec(v_toPure_622_);
v___x_629_ = lean_apply_4(v_toBind_623_, lean_box(0), lean_box(0), v_mkMsg_624_, v___f_625_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object* v_toPure_630_, lean_object* v_toBind_631_, lean_object* v_mkMsg_632_, lean_object* v___f_633_, lean_object* v_____do__lift_634_){
_start:
{
uint8_t v_____do__lift_153__boxed_635_; lean_object* v_res_636_; 
v_____do__lift_153__boxed_635_ = lean_unbox(v_____do__lift_634_);
v_res_636_ = l_Lean_traceM___redArg___lam__1(v_toPure_630_, v_toBind_631_, v_mkMsg_632_, v___f_633_, v_____do__lift_153__boxed_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_cls_642_, lean_object* v_mkMsg_643_){
_start:
{
lean_object* v_toApplicative_644_; lean_object* v_toBind_645_; lean_object* v_getInheritedTraceOptions_646_; lean_object* v_toPure_647_; lean_object* v___f_648_; lean_object* v___f_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_toApplicative_644_ = lean_ctor_get(v_inst_637_, 0);
v_toBind_645_ = lean_ctor_get(v_inst_637_, 1);
lean_inc_n(v_toBind_645_, 4);
v_getInheritedTraceOptions_646_ = lean_ctor_get(v_inst_638_, 2);
lean_inc(v_getInheritedTraceOptions_646_);
v_toPure_647_ = lean_ctor_get(v_toApplicative_644_, 1);
lean_inc_n(v_toPure_647_, 2);
lean_inc(v_cls_642_);
v___f_648_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_648_, 0, v_inst_637_);
lean_closure_set(v___f_648_, 1, v_inst_638_);
lean_closure_set(v___f_648_, 2, v_inst_639_);
lean_closure_set(v___f_648_, 3, v_inst_640_);
lean_closure_set(v___f_648_, 4, v_cls_642_);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_649_, 0, v_toPure_647_);
lean_closure_set(v___f_649_, 1, v_toBind_645_);
lean_closure_set(v___f_649_, 2, v_mkMsg_643_);
lean_closure_set(v___f_649_, 3, v___f_648_);
v___f_650_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_650_, 0, v_toPure_647_);
lean_closure_set(v___f_650_, 1, v_cls_642_);
lean_closure_set(v___f_650_, 2, v_toBind_645_);
lean_closure_set(v___f_650_, 3, v_inst_641_);
v___x_651_ = lean_apply_4(v_toBind_645_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_646_, v___f_650_);
v___x_652_ = lean_apply_4(v_toBind_645_, lean_box(0), lean_box(0), v___x_651_, v___f_649_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object* v_m_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_cls_659_, lean_object* v_mkMsg_660_){
_start:
{
lean_object* v_toApplicative_661_; lean_object* v_toBind_662_; lean_object* v_getInheritedTraceOptions_663_; lean_object* v_toPure_664_; lean_object* v___f_665_; lean_object* v___f_666_; lean_object* v___f_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_toApplicative_661_ = lean_ctor_get(v_inst_654_, 0);
v_toBind_662_ = lean_ctor_get(v_inst_654_, 1);
lean_inc_n(v_toBind_662_, 4);
v_getInheritedTraceOptions_663_ = lean_ctor_get(v_inst_655_, 2);
lean_inc(v_getInheritedTraceOptions_663_);
v_toPure_664_ = lean_ctor_get(v_toApplicative_661_, 1);
lean_inc_n(v_toPure_664_, 2);
lean_inc(v_cls_659_);
v___f_665_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_665_, 0, v_inst_654_);
lean_closure_set(v___f_665_, 1, v_inst_655_);
lean_closure_set(v___f_665_, 2, v_inst_656_);
lean_closure_set(v___f_665_, 3, v_inst_657_);
lean_closure_set(v___f_665_, 4, v_cls_659_);
v___f_666_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_666_, 0, v_toPure_664_);
lean_closure_set(v___f_666_, 1, v_toBind_662_);
lean_closure_set(v___f_666_, 2, v_mkMsg_660_);
lean_closure_set(v___f_666_, 3, v___f_665_);
v___f_667_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_667_, 0, v_toPure_664_);
lean_closure_set(v___f_667_, 1, v_cls_659_);
lean_closure_set(v___f_667_, 2, v_toBind_662_);
lean_closure_set(v___f_667_, 3, v_inst_658_);
v___x_668_ = lean_apply_4(v_toBind_662_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_663_, v___f_667_);
v___x_669_ = lean_apply_4(v_toBind_662_, lean_box(0), lean_box(0), v___x_668_, v___f_666_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object* v_x_670_){
_start:
{
lean_object* v_msg_671_; 
v_msg_671_ = lean_ctor_get(v_x_670_, 1);
lean_inc_ref(v_msg_671_);
return v_msg_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_672_);
lean_dec_ref(v_x_672_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object* v_ref_674_, lean_object* v_msg_675_, lean_object* v_oldTraces_676_, lean_object* v_s_677_){
_start:
{
uint64_t v_tid_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_687_; 
v_tid_678_ = lean_ctor_get_uint64(v_s_677_, sizeof(void*)*1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_s_677_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_s_677_, 0);
lean_dec(v_unused_688_);
v___x_680_ = v_s_677_;
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
else
{
lean_dec(v_s_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_ref_674_);
lean_ctor_set(v___x_682_, 1, v_msg_675_);
v___x_683_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_676_, v___x_682_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_683_);
v___x_685_ = v___x_680_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
lean_ctor_set_uint64(v_reuseFailAlloc_686_, sizeof(void*)*1, v_tid_678_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object* v_ref_689_, lean_object* v_oldTraces_690_, lean_object* v_modifyTraceState_691_, lean_object* v_msg_692_){
_start:
{
lean_object* v___f_693_; lean_object* v___x_694_; 
v___f_693_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0), 4, 3);
lean_closure_set(v___f_693_, 0, v_ref_689_);
lean_closure_set(v___f_693_, 1, v_msg_692_);
lean_closure_set(v___f_693_, 2, v_oldTraces_690_);
v___x_694_ = lean_apply_1(v_modifyTraceState_691_, v___f_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object* v___f_714_, lean_object* v_data_715_, lean_object* v_msg_716_, lean_object* v_inst_717_, lean_object* v_toBind_718_, lean_object* v___f_719_, lean_object* v_____do__lift_720_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; size_t v_sz_723_; size_t v___x_724_; lean_object* v___x_725_; lean_object* v_msg_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_721_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_720_);
v___x_722_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v_sz_723_ = lean_array_size(v___x_721_);
v___x_724_ = ((size_t)0ULL);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_722_, v___f_714_, v_sz_723_, v___x_724_, v___x_721_);
v_msg_726_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_726_, 0, v_data_715_);
lean_ctor_set(v_msg_726_, 1, v_msg_716_);
lean_ctor_set(v_msg_726_, 2, v___x_725_);
v___x_727_ = lean_apply_1(v_inst_717_, v_msg_726_);
v___x_728_ = lean_apply_4(v_toBind_718_, lean_box(0), lean_box(0), v___x_727_, v___f_719_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object* v___f_729_, lean_object* v_data_730_, lean_object* v_msg_731_, lean_object* v_inst_732_, lean_object* v_toBind_733_, lean_object* v___f_734_, lean_object* v_____do__lift_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(v___f_729_, v_data_730_, v_msg_731_, v_inst_732_, v_toBind_733_, v___f_734_, v_____do__lift_735_);
lean_dec_ref(v_____do__lift_735_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object* v_ref_737_, lean_object* v_withRef_738_, lean_object* v___x_739_, lean_object* v_oldRef_740_){
_start:
{
lean_object* v_ref_741_; lean_object* v___x_742_; 
v_ref_741_ = l_Lean_replaceRef(v_ref_737_, v_oldRef_740_);
v___x_742_ = lean_apply_3(v_withRef_738_, lean_box(0), v_ref_741_, v___x_739_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object* v_ref_743_, lean_object* v_withRef_744_, lean_object* v___x_745_, lean_object* v_oldRef_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(v_ref_743_, v_withRef_744_, v___x_745_, v_oldRef_746_);
lean_dec(v_oldRef_746_);
lean_dec(v_ref_743_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_oldTraces_753_, lean_object* v_data_754_, lean_object* v_ref_755_, lean_object* v_msg_756_){
_start:
{
lean_object* v_toApplicative_757_; lean_object* v_toBind_758_; lean_object* v_modifyTraceState_759_; lean_object* v_getTraceState_760_; lean_object* v_toPure_761_; lean_object* v_getRef_762_; lean_object* v_withRef_763_; lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___f_770_; lean_object* v___x_771_; 
v_toApplicative_757_ = lean_ctor_get(v_inst_749_, 0);
lean_inc_ref(v_toApplicative_757_);
v_toBind_758_ = lean_ctor_get(v_inst_749_, 1);
lean_inc_n(v_toBind_758_, 4);
lean_dec_ref(v_inst_749_);
v_modifyTraceState_759_ = lean_ctor_get(v_inst_750_, 0);
lean_inc(v_modifyTraceState_759_);
v_getTraceState_760_ = lean_ctor_get(v_inst_750_, 1);
lean_inc(v_getTraceState_760_);
lean_dec_ref(v_inst_750_);
v_toPure_761_ = lean_ctor_get(v_toApplicative_757_, 1);
lean_inc(v_toPure_761_);
lean_dec_ref(v_toApplicative_757_);
v_getRef_762_ = lean_ctor_get(v_inst_751_, 0);
lean_inc(v_getRef_762_);
v_withRef_763_ = lean_ctor_get(v_inst_751_, 1);
lean_inc(v_withRef_763_);
lean_dec_ref(v_inst_751_);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_764_, 0, v_toPure_761_);
v___x_765_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v_getTraceState_760_, v___f_764_);
v___f_766_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0));
lean_inc(v_ref_755_);
v___f_767_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2), 4, 3);
lean_closure_set(v___f_767_, 0, v_ref_755_);
lean_closure_set(v___f_767_, 1, v_oldTraces_753_);
lean_closure_set(v___f_767_, 2, v_modifyTraceState_759_);
v___f_768_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_768_, 0, v___f_766_);
lean_closure_set(v___f_768_, 1, v_data_754_);
lean_closure_set(v___f_768_, 2, v_msg_756_);
lean_closure_set(v___f_768_, 3, v_inst_752_);
lean_closure_set(v___f_768_, 4, v_toBind_758_);
lean_closure_set(v___f_768_, 5, v___f_767_);
v___x_769_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_765_, v___f_768_);
v___f_770_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_770_, 0, v_ref_755_);
lean_closure_set(v___f_770_, 1, v_withRef_763_);
lean_closure_set(v___f_770_, 2, v___x_769_);
v___x_771_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v_getRef_762_, v___f_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object* v_m_772_, lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_oldTraces_777_, lean_object* v_data_778_, lean_object* v_ref_779_, lean_object* v_msg_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_773_, v_inst_774_, v_inst_775_, v_inst_776_, v_oldTraces_777_, v_data_778_, v_ref_779_, v_msg_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object* v_name_782_, lean_object* v_decl_783_, lean_object* v_ref_784_){
_start:
{
lean_object* v_defValue_786_; lean_object* v_descr_787_; lean_object* v_deprecation_x3f_788_; lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_defValue_786_ = lean_ctor_get(v_decl_783_, 0);
v_descr_787_ = lean_ctor_get(v_decl_783_, 1);
v_deprecation_x3f_788_ = lean_ctor_get(v_decl_783_, 2);
v___x_789_ = lean_alloc_ctor(1, 0, 1);
v___x_790_ = lean_unbox(v_defValue_786_);
lean_ctor_set_uint8(v___x_789_, 0, v___x_790_);
lean_inc(v_deprecation_x3f_788_);
lean_inc_ref(v_descr_787_);
lean_inc_n(v_name_782_, 2);
v___x_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_791_, 0, v_name_782_);
lean_ctor_set(v___x_791_, 1, v_ref_784_);
lean_ctor_set(v___x_791_, 2, v___x_789_);
lean_ctor_set(v___x_791_, 3, v_descr_787_);
lean_ctor_set(v___x_791_, 4, v_deprecation_x3f_788_);
v___x_792_ = lean_register_option(v_name_782_, v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v___x_792_, 0);
lean_dec(v_unused_801_);
v___x_794_ = v___x_792_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_dec(v___x_792_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
lean_inc(v_defValue_786_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_name_782_);
lean_ctor_set(v___x_796_, 1, v_defValue_786_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec(v_name_782_);
v_a_802_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_792_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_792_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_810_, lean_object* v_decl_811_, lean_object* v_ref_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_810_, v_decl_811_, v_ref_812_);
lean_dec_ref(v_decl_811_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_830_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_831_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_832_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_833_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_830_, v___x_831_, v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object* v_name_836_, lean_object* v_decl_837_, lean_object* v_ref_838_){
_start:
{
lean_object* v_defValue_840_; lean_object* v_descr_841_; lean_object* v_deprecation_x3f_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_defValue_840_ = lean_ctor_get(v_decl_837_, 0);
v_descr_841_ = lean_ctor_get(v_decl_837_, 1);
v_deprecation_x3f_842_ = lean_ctor_get(v_decl_837_, 2);
lean_inc(v_defValue_840_);
v___x_843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_843_, 0, v_defValue_840_);
lean_inc(v_deprecation_x3f_842_);
lean_inc_ref(v_descr_841_);
lean_inc_n(v_name_836_, 2);
v___x_844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_844_, 0, v_name_836_);
lean_ctor_set(v___x_844_, 1, v_ref_838_);
lean_ctor_set(v___x_844_, 2, v___x_843_);
lean_ctor_set(v___x_844_, 3, v_descr_841_);
lean_ctor_set(v___x_844_, 4, v_deprecation_x3f_842_);
v___x_845_ = lean_register_option(v_name_836_, v___x_844_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v___x_845_, 0);
lean_dec(v_unused_854_);
v___x_847_ = v___x_845_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_dec(v___x_845_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
lean_inc(v_defValue_840_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_name_836_);
lean_ctor_set(v___x_849_, 1, v_defValue_840_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v_name_836_);
v_a_855_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_845_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_845_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_863_, lean_object* v_decl_864_, lean_object* v_ref_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_863_, v_decl_864_, v_ref_865_);
lean_dec_ref(v_decl_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_884_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_885_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_886_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_887_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_884_, v___x_885_, v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_907_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_908_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_909_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_910_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_907_, v___x_908_, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object* v_name_913_, lean_object* v_decl_914_, lean_object* v_ref_915_){
_start:
{
lean_object* v_defValue_917_; lean_object* v_descr_918_; lean_object* v_deprecation_x3f_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_defValue_917_ = lean_ctor_get(v_decl_914_, 0);
v_descr_918_ = lean_ctor_get(v_decl_914_, 1);
v_deprecation_x3f_919_ = lean_ctor_get(v_decl_914_, 2);
lean_inc(v_defValue_917_);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v_defValue_917_);
lean_inc(v_deprecation_x3f_919_);
lean_inc_ref(v_descr_918_);
lean_inc_n(v_name_913_, 2);
v___x_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_921_, 0, v_name_913_);
lean_ctor_set(v___x_921_, 1, v_ref_915_);
lean_ctor_set(v___x_921_, 2, v___x_920_);
lean_ctor_set(v___x_921_, 3, v_descr_918_);
lean_ctor_set(v___x_921_, 4, v_deprecation_x3f_919_);
v___x_922_ = lean_register_option(v_name_913_, v___x_921_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v___x_922_, 0);
lean_dec(v_unused_931_);
v___x_924_ = v___x_922_;
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
else
{
lean_dec(v___x_922_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
lean_inc(v_defValue_917_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_name_913_);
lean_ctor_set(v___x_926_, 1, v_defValue_917_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec(v_name_913_);
v_a_932_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_922_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_922_);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_940_, lean_object* v_decl_941_, lean_object* v_ref_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_940_, v_decl_941_, v_ref_942_);
lean_dec_ref(v_decl_941_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_961_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_962_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_963_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_964_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_961_, v___x_962_, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_986_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_987_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_988_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_989_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_986_, v___x_987_, v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
return v_res_991_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_992_; double v___x_993_; 
v___x_992_ = lean_unsigned_to_nat(1000000000u);
v___x_993_ = lean_float_of_nat(v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object* v_toApplicative_994_, lean_object* v_start_995_, lean_object* v_a_996_, lean_object* v_stop_997_){
_start:
{
lean_object* v_toPure_998_; double v___x_999_; double v___x_1000_; double v___x_1001_; double v___x_1002_; double v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_toPure_998_ = lean_ctor_get(v_toApplicative_994_, 1);
lean_inc(v_toPure_998_);
lean_dec_ref(v_toApplicative_994_);
v___x_999_ = lean_float_of_nat(v_start_995_);
v___x_1000_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1001_ = lean_float_div(v___x_999_, v___x_1000_);
v___x_1002_ = lean_float_of_nat(v_stop_997_);
v___x_1003_ = lean_float_div(v___x_1002_, v___x_1000_);
v___x_1004_ = lean_box_float(v___x_1001_);
v___x_1005_ = lean_box_float(v___x_1003_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_a_996_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_apply_2(v_toPure_998_, lean_box(0), v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object* v_toApplicative_1009_, lean_object* v_start_1010_, lean_object* v_toBind_1011_, lean_object* v___x_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___f_1014_; lean_object* v___x_1015_; 
v___f_1014_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1014_, 0, v_toApplicative_1009_);
lean_closure_set(v___f_1014_, 1, v_start_1010_);
lean_closure_set(v___f_1014_, 2, v_a_1013_);
v___x_1015_ = lean_apply_4(v_toBind_1011_, lean_box(0), lean_box(0), v___x_1012_, v___f_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object* v_toApplicative_1016_, lean_object* v_toBind_1017_, lean_object* v___x_1018_, lean_object* v_act_1019_, lean_object* v_start_1020_){
_start:
{
lean_object* v___f_1021_; lean_object* v___x_1022_; 
lean_inc(v_toBind_1017_);
v___f_1021_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1021_, 0, v_toApplicative_1016_);
lean_closure_set(v___f_1021_, 1, v_start_1020_);
lean_closure_set(v___f_1021_, 2, v_toBind_1017_);
lean_closure_set(v___f_1021_, 3, v___x_1018_);
v___x_1022_ = lean_apply_4(v_toBind_1017_, lean_box(0), lean_box(0), v_act_1019_, v___f_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object* v_toApplicative_1023_, lean_object* v_start_1024_, lean_object* v_a_1025_, lean_object* v_stop_1026_){
_start:
{
lean_object* v_toPure_1027_; double v___x_1028_; double v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_toPure_1027_ = lean_ctor_get(v_toApplicative_1023_, 1);
lean_inc(v_toPure_1027_);
lean_dec_ref(v_toApplicative_1023_);
v___x_1028_ = lean_float_of_nat(v_start_1024_);
v___x_1029_ = lean_float_of_nat(v_stop_1026_);
v___x_1030_ = lean_box_float(v___x_1028_);
v___x_1031_ = lean_box_float(v___x_1029_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_a_1025_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_apply_2(v_toPure_1027_, lean_box(0), v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object* v_toApplicative_1035_, lean_object* v_start_1036_, lean_object* v_toBind_1037_, lean_object* v___x_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___f_1040_; lean_object* v___x_1041_; 
v___f_1040_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1040_, 0, v_toApplicative_1035_);
lean_closure_set(v___f_1040_, 1, v_start_1036_);
lean_closure_set(v___f_1040_, 2, v_a_1039_);
v___x_1041_ = lean_apply_4(v_toBind_1037_, lean_box(0), lean_box(0), v___x_1038_, v___f_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object* v_toApplicative_1042_, lean_object* v_toBind_1043_, lean_object* v___x_1044_, lean_object* v_act_1045_, lean_object* v_start_1046_){
_start:
{
lean_object* v___f_1047_; lean_object* v___x_1048_; 
lean_inc(v_toBind_1043_);
v___f_1047_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1047_, 0, v_toApplicative_1042_);
lean_closure_set(v___f_1047_, 1, v_start_1046_);
lean_closure_set(v___f_1047_, 2, v_toBind_1043_);
lean_closure_set(v___f_1047_, 3, v___x_1044_);
v___x_1048_ = lean_apply_4(v_toBind_1043_, lean_box(0), lean_box(0), v_act_1045_, v___f_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_opts_1053_, lean_object* v_act_1054_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1055_ = l_Lean_KVMap_instValueBool;
v___x_1056_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1057_ = l_Lean_Option_get___redArg(v___x_1055_, v_opts_1053_, v___x_1056_);
v___x_1058_ = lean_unbox(v___x_1057_);
lean_dec(v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v_toApplicative_1059_; lean_object* v_toBind_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; 
v_toApplicative_1059_ = lean_ctor_get(v_inst_1051_, 0);
lean_inc_ref(v_toApplicative_1059_);
v_toBind_1060_ = lean_ctor_get(v_inst_1051_, 1);
lean_inc_n(v_toBind_1060_, 2);
lean_dec_ref(v_inst_1051_);
v___x_1061_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1062_ = lean_apply_2(v_inst_1052_, lean_box(0), v___x_1061_);
lean_inc(v___x_1062_);
v___f_1063_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1063_, 0, v_toApplicative_1059_);
lean_closure_set(v___f_1063_, 1, v_toBind_1060_);
lean_closure_set(v___f_1063_, 2, v___x_1062_);
lean_closure_set(v___f_1063_, 3, v_act_1054_);
v___x_1064_ = lean_apply_4(v_toBind_1060_, lean_box(0), lean_box(0), v___x_1062_, v___f_1063_);
return v___x_1064_;
}
else
{
lean_object* v_toApplicative_1065_; lean_object* v_toBind_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___x_1070_; 
v_toApplicative_1065_ = lean_ctor_get(v_inst_1051_, 0);
lean_inc_ref(v_toApplicative_1065_);
v_toBind_1066_ = lean_ctor_get(v_inst_1051_, 1);
lean_inc_n(v_toBind_1066_, 2);
lean_dec_ref(v_inst_1051_);
v___x_1067_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1068_ = lean_apply_2(v_inst_1052_, lean_box(0), v___x_1067_);
lean_inc(v___x_1068_);
v___f_1069_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1069_, 0, v_toApplicative_1065_);
lean_closure_set(v___f_1069_, 1, v_toBind_1066_);
lean_closure_set(v___f_1069_, 2, v___x_1068_);
lean_closure_set(v___f_1069_, 3, v_act_1054_);
v___x_1070_ = lean_apply_4(v_toBind_1066_, lean_box(0), lean_box(0), v___x_1068_, v___f_1069_);
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_opts_1073_, lean_object* v_act_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(v_inst_1071_, v_inst_1072_, v_opts_1073_, v_act_1074_);
lean_dec_ref(v_opts_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object* v_00_u03b1_1076_, lean_object* v_m_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_opts_1080_, lean_object* v_act_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1082_ = l_Lean_KVMap_instValueBool;
v___x_1083_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1084_ = l_Lean_Option_get___redArg(v___x_1082_, v_opts_1080_, v___x_1083_);
v___x_1085_ = lean_unbox(v___x_1084_);
lean_dec(v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v_toApplicative_1086_; lean_object* v_toBind_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; 
v_toApplicative_1086_ = lean_ctor_get(v_inst_1078_, 0);
lean_inc_ref(v_toApplicative_1086_);
v_toBind_1087_ = lean_ctor_get(v_inst_1078_, 1);
lean_inc_n(v_toBind_1087_, 2);
lean_dec_ref(v_inst_1078_);
v___x_1088_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1089_ = lean_apply_2(v_inst_1079_, lean_box(0), v___x_1088_);
lean_inc(v___x_1089_);
v___f_1090_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1090_, 0, v_toApplicative_1086_);
lean_closure_set(v___f_1090_, 1, v_toBind_1087_);
lean_closure_set(v___f_1090_, 2, v___x_1089_);
lean_closure_set(v___f_1090_, 3, v_act_1081_);
v___x_1091_ = lean_apply_4(v_toBind_1087_, lean_box(0), lean_box(0), v___x_1089_, v___f_1090_);
return v___x_1091_;
}
else
{
lean_object* v_toApplicative_1092_; lean_object* v_toBind_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; 
v_toApplicative_1092_ = lean_ctor_get(v_inst_1078_, 0);
lean_inc_ref(v_toApplicative_1092_);
v_toBind_1093_ = lean_ctor_get(v_inst_1078_, 1);
lean_inc_n(v_toBind_1093_, 2);
lean_dec_ref(v_inst_1078_);
v___x_1094_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1095_ = lean_apply_2(v_inst_1079_, lean_box(0), v___x_1094_);
lean_inc(v___x_1095_);
v___f_1096_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1096_, 0, v_toApplicative_1092_);
lean_closure_set(v___f_1096_, 1, v_toBind_1093_);
lean_closure_set(v___f_1096_, 2, v___x_1095_);
lean_closure_set(v___f_1096_, 3, v_act_1081_);
v___x_1097_ = lean_apply_4(v_toBind_1093_, lean_box(0), lean_box(0), v___x_1095_, v___f_1096_);
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object* v_00_u03b1_1098_, lean_object* v_m_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_opts_1102_, lean_object* v_act_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(v_00_u03b1_1098_, v_m_1099_, v_inst_1100_, v_inst_1101_, v_opts_1102_, v_act_1103_);
lean_dec_ref(v_opts_1102_);
return v_res_1104_;
}
}
static double _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0(void){
_start:
{
lean_object* v___x_1105_; double v___x_1106_; 
v___x_1105_ = lean_unsigned_to_nat(1000u);
v___x_1106_ = lean_float_of_nat(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object* v_o_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1108_ = l_Lean_KVMap_instValueBool;
v___x_1109_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1110_ = l_Lean_Option_get___redArg(v___x_1108_, v_o_1107_, v___x_1109_);
v___x_1111_ = lean_unbox(v___x_1110_);
lean_dec(v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; double v___x_1115_; double v___x_1116_; double v___x_1117_; 
v___x_1112_ = l_Lean_KVMap_instValueNat;
v___x_1113_ = l_Lean_trace_profiler_threshold;
v___x_1114_ = l_Lean_Option_get___redArg(v___x_1112_, v_o_1107_, v___x_1113_);
v___x_1115_ = lean_float_of_nat(v___x_1114_);
v___x_1116_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1117_ = lean_float_div(v___x_1115_, v___x_1116_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; double v___x_1121_; 
v___x_1118_ = l_Lean_KVMap_instValueNat;
v___x_1119_ = l_Lean_trace_profiler_threshold;
v___x_1120_ = l_Lean_Option_get___redArg(v___x_1118_, v_o_1107_, v___x_1119_);
v___x_1121_ = lean_float_of_nat(v___x_1120_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object* v_o_1122_){
_start:
{
double v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1122_);
lean_dec_ref(v_o_1122_);
v_r_1124_ = lean_box_float(v_res_1123_);
return v_r_1124_;
}
}
static lean_object* _init_l_Lean_instMonadAlwaysExceptEIO___closed__0(void){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object* v_00_u03b5_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___closed__0, &l_Lean_instMonadAlwaysExceptEIO___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___closed__0);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object* v_inst_1128_, lean_object* v_always_1129_){
_start:
{
lean_object* v___f_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; 
lean_inc_ref(v_always_1129_);
v___f_1130_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1130_, 0, v_always_1129_);
lean_closure_set(v___f_1130_, 1, v_inst_1128_);
v___f_1131_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_1131_, 0, v_always_1129_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___f_1130_);
lean_ctor_set(v___x_1132_, 1, v___f_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object* v_m_1133_, lean_object* v_inst_1134_, lean_object* v_00_u03b5_1135_, lean_object* v_00_u03c3_1136_, lean_object* v_always_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_1134_, v_always_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object* v_always_1139_){
_start:
{
lean_object* v___f_1140_; lean_object* v___f_1141_; lean_object* v___x_1142_; 
lean_inc_ref(v_always_1139_);
v___f_1140_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1140_, 0, v_always_1139_);
v___f_1141_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1141_, 0, v_always_1139_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___f_1140_);
lean_ctor_set(v___x_1142_, 1, v___f_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object* v_m_1143_, lean_object* v_00_u03b5_1144_, lean_object* v_00_u03c9_1145_, lean_object* v_00_u03c3_1146_, lean_object* v_always_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object* v_always_1149_){
_start:
{
lean_object* v___f_1150_; lean_object* v___f_1151_; lean_object* v___x_1152_; 
lean_inc_ref(v_always_1149_);
v___f_1150_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1150_, 0, v_always_1149_);
v___f_1151_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1151_, 0, v_always_1149_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___f_1150_);
lean_ctor_set(v___x_1152_, 1, v___f_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object* v_m_1153_, lean_object* v_00_u03b5_1154_, lean_object* v_00_u03c1_1155_, lean_object* v_always_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object* v_always_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1159_, v_inst_1160_, v_inst_1161_, v_always_1158_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object* v_00_u03b1_1163_, lean_object* v_m_1164_, lean_object* v_00_u03b5_1165_, lean_object* v_00_u03c9_1166_, lean_object* v_00_u03b2_1167_, lean_object* v_always_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1169_, v_inst_1170_, v_inst_1171_, v_always_1168_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji(uint8_t v_x_1179_){
_start:
{
switch(v_x_1179_)
{
case 0:
{
lean_object* v___x_1180_; 
v___x_1180_ = ((lean_object*)(l_Lean_checkEmoji___closed__0));
return v___x_1180_;
}
case 1:
{
lean_object* v___x_1181_; 
v___x_1181_ = ((lean_object*)(l_Lean_crossEmoji___closed__0));
return v___x_1181_;
}
default: 
{
lean_object* v___x_1182_; 
v___x_1182_ = ((lean_object*)(l_Lean_bombEmoji___closed__0));
return v___x_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object* v_x_1183_){
_start:
{
uint8_t v_x_31__boxed_1184_; lean_object* v_res_1185_; 
v_x_31__boxed_1184_ = lean_unbox(v_x_1183_);
v_res_1185_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_1184_);
return v_res_1185_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___lam__0(lean_object* v_x_1186_){
_start:
{
if (lean_obj_tag(v_x_1186_) == 0)
{
uint8_t v___x_1187_; 
v___x_1187_ = 2;
return v___x_1187_;
}
else
{
lean_object* v_a_1188_; uint8_t v___x_1189_; 
v_a_1188_ = lean_ctor_get(v_x_1186_, 0);
v___x_1189_ = lean_unbox(v_a_1188_);
if (v___x_1189_ == 0)
{
uint8_t v___x_1190_; 
v___x_1190_ = 1;
return v___x_1190_;
}
else
{
uint8_t v___x_1191_; 
v___x_1191_ = 0;
return v___x_1191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object* v_x_1192_){
_start:
{
uint8_t v_res_1193_; lean_object* v_r_1194_; 
v_res_1193_ = l_Lean_instExceptToTraceResultBool___lam__0(v_x_1192_);
lean_dec_ref(v_x_1192_);
v_r_1194_ = lean_box(v_res_1193_);
return v_r_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object* v_00_u03b5_1196_){
_start:
{
lean_object* v___f_1197_; 
v___f_1197_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___closed__0));
return v___f_1197_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___lam__0(lean_object* v_x_1198_){
_start:
{
if (lean_obj_tag(v_x_1198_) == 0)
{
uint8_t v___x_1199_; 
v___x_1199_ = 2;
return v___x_1199_;
}
else
{
lean_object* v_a_1200_; 
v_a_1200_ = lean_ctor_get(v_x_1198_, 0);
if (lean_obj_tag(v_a_1200_) == 0)
{
uint8_t v___x_1201_; 
v___x_1201_ = 1;
return v___x_1201_;
}
else
{
uint8_t v___x_1202_; 
v___x_1202_ = 0;
return v___x_1202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object* v_x_1203_){
_start:
{
uint8_t v_res_1204_; lean_object* v_r_1205_; 
v_res_1204_ = l_Lean_instExceptToTraceResultOption___lam__0(v_x_1203_);
lean_dec_ref(v_x_1203_);
v_r_1205_ = lean_box(v_res_1204_);
return v_r_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object* v_00_u03b1_1207_, lean_object* v_00_u03b5_1208_){
_start:
{
lean_object* v___f_1209_; 
v___f_1209_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___closed__0));
return v___f_1209_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object* v_x_1210_){
_start:
{
if (lean_obj_tag(v_x_1210_) == 0)
{
uint8_t v___x_1211_; 
v___x_1211_ = 2;
return v___x_1211_;
}
else
{
uint8_t v___x_1212_; 
v___x_1212_ = 0;
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object* v_x_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = l_Lean_instExceptToTraceResult___lam__0(v_x_1213_);
lean_dec_ref(v_x_1213_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object* v_00_u03b1_1217_, lean_object* v_00_u03b5_1218_){
_start:
{
lean_object* v___f_1219_; 
v___f_1219_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
return v___f_1219_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___redArg(lean_object* v_inst_1220_, lean_object* v_e_1221_){
_start:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = lean_apply_1(v_inst_1220_, v_e_1221_);
v___x_1223_ = lean_unbox(v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___redArg___boxed(lean_object* v_inst_1224_, lean_object* v_e_1225_){
_start:
{
uint8_t v_res_1226_; lean_object* v_r_1227_; 
v_res_1226_ = l_Except_toTraceResult___redArg(v_inst_1224_, v_e_1225_);
v_r_1227_ = lean_box(v_res_1226_);
return v_r_1227_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult(lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b5_1229_, lean_object* v_inst_1230_, lean_object* v_e_1231_){
_start:
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = lean_apply_1(v_inst_1230_, v_e_1231_);
v___x_1233_ = lean_unbox(v___x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___boxed(lean_object* v_00_u03b1_1234_, lean_object* v_00_u03b5_1235_, lean_object* v_inst_1236_, lean_object* v_e_1237_){
_start:
{
uint8_t v_res_1238_; lean_object* v_r_1239_; 
v_res_1238_ = l_Except_toTraceResult(v_00_u03b1_1234_, v_00_u03b5_1235_, v_inst_1236_, v_e_1237_);
v_r_1239_ = lean_box(v_res_1238_);
return v_r_1239_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0));
v___x_1242_ = l_Lean_stringToMessageData(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object* v_inst_1243_, lean_object* v_x_1244_){
_start:
{
lean_object* v_toApplicative_1245_; lean_object* v_toPure_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_toApplicative_1245_ = lean_ctor_get(v_inst_1243_, 0);
lean_inc_ref(v_toApplicative_1245_);
lean_dec_ref(v_inst_1243_);
v_toPure_1246_ = lean_ctor_get(v_toApplicative_1245_, 1);
lean_inc(v_toPure_1246_);
lean_dec_ref(v_toApplicative_1245_);
v___x_1247_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1);
v___x_1248_ = lean_apply_2(v_toPure_1246_, lean_box(0), v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(lean_object* v_inst_1249_, lean_object* v_x_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(v_inst_1249_, v_x_1250_);
lean_dec(v_x_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object* v_oldTraces_1252_, lean_object* v_s_1253_){
_start:
{
uint64_t v_tid_1254_; lean_object* v_traces_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1263_; 
v_tid_1254_ = lean_ctor_get_uint64(v_s_1253_, sizeof(void*)*1);
v_traces_1255_ = lean_ctor_get(v_s_1253_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_s_1253_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1257_ = v_s_1253_;
v_isShared_1258_ = v_isSharedCheck_1263_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_traces_1255_);
lean_dec(v_s_1253_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1263_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1252_, v_traces_1255_);
lean_dec_ref(v_traces_1255_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1259_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
lean_ctor_set_uint64(v_reuseFailAlloc_1262_, sizeof(void*)*1, v_tid_1254_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object* v_always_1264_, lean_object* v_inst_1265_, lean_object* v_fst_1266_, lean_object* v_____r_1267_){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1264_);
v___x_1269_ = l_MonadExcept_ofExcept___redArg(v_inst_1265_, v___x_1268_, v_fst_1266_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object* v_inst_1270_, lean_object* v___x_1271_, lean_object* v_fst_1272_, lean_object* v_____r_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_MonadExcept_ofExcept___redArg(v_inst_1270_, v___x_1271_, v_fst_1272_);
return v___x_1274_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__0));
v___x_1277_ = l_Lean_stringToMessageData(v___x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object* v_inst_1278_, lean_object* v_fst_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_oldTraces_1284_, lean_object* v_ref_1285_, lean_object* v_toBind_1286_, lean_object* v___f_1287_, lean_object* v_cls_1288_, uint8_t v_collapsed_1289_, lean_object* v_tag_1290_, uint8_t v___x_1291_, double v_fst_1292_, double v_snd_1293_, lean_object* v_m_1294_){
_start:
{
lean_object* v_result_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_m_1301_; lean_object* v_data_1303_; lean_object* v___x_1306_; double v___x_1307_; lean_object* v_data_1308_; 
v_result_1295_ = lean_apply_1(v_inst_1278_, v_fst_1279_);
v___x_1296_ = lean_unbox(v_result_1295_);
v___x_1297_ = l_Lean_TraceResult_toEmoji(v___x_1296_);
v___x_1298_ = l_Lean_stringToMessageData(v___x_1297_);
v___x_1299_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
v___x_1300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v_m_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_m_1301_, 0, v___x_1300_);
lean_ctor_set(v_m_1301_, 1, v_m_1294_);
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v_result_1295_);
v___x_1307_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_1290_);
lean_inc_ref(v___x_1306_);
lean_inc(v_cls_1288_);
v_data_1308_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1308_, 0, v_cls_1288_);
lean_ctor_set(v_data_1308_, 1, v___x_1306_);
lean_ctor_set(v_data_1308_, 2, v_tag_1290_);
lean_ctor_set_float(v_data_1308_, sizeof(void*)*3, v___x_1307_);
lean_ctor_set_float(v_data_1308_, sizeof(void*)*3 + 8, v___x_1307_);
lean_ctor_set_uint8(v_data_1308_, sizeof(void*)*3 + 16, v_collapsed_1289_);
if (v___x_1291_ == 0)
{
lean_dec_ref(v___x_1306_);
lean_dec_ref(v_tag_1290_);
lean_dec(v_cls_1288_);
v_data_1303_ = v_data_1308_;
goto v___jp_1302_;
}
else
{
lean_object* v_data_1309_; 
lean_dec_ref(v_data_1308_);
v_data_1309_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1309_, 0, v_cls_1288_);
lean_ctor_set(v_data_1309_, 1, v___x_1306_);
lean_ctor_set(v_data_1309_, 2, v_tag_1290_);
lean_ctor_set_float(v_data_1309_, sizeof(void*)*3, v_fst_1292_);
lean_ctor_set_float(v_data_1309_, sizeof(void*)*3 + 8, v_snd_1293_);
lean_ctor_set_uint8(v_data_1309_, sizeof(void*)*3 + 16, v_collapsed_1289_);
v_data_1303_ = v_data_1309_;
goto v___jp_1302_;
}
v___jp_1302_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_1280_, v_inst_1281_, v_inst_1282_, v_inst_1283_, v_oldTraces_1284_, v_data_1303_, v_ref_1285_, v_m_1301_);
v___x_1305_ = lean_apply_4(v_toBind_1286_, lean_box(0), lean_box(0), v___x_1304_, v___f_1287_);
return v___x_1305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_1310_ = _args[0];
lean_object* v_fst_1311_ = _args[1];
lean_object* v_inst_1312_ = _args[2];
lean_object* v_inst_1313_ = _args[3];
lean_object* v_inst_1314_ = _args[4];
lean_object* v_inst_1315_ = _args[5];
lean_object* v_oldTraces_1316_ = _args[6];
lean_object* v_ref_1317_ = _args[7];
lean_object* v_toBind_1318_ = _args[8];
lean_object* v___f_1319_ = _args[9];
lean_object* v_cls_1320_ = _args[10];
lean_object* v_collapsed_1321_ = _args[11];
lean_object* v_tag_1322_ = _args[12];
lean_object* v___x_1323_ = _args[13];
lean_object* v_fst_1324_ = _args[14];
lean_object* v_snd_1325_ = _args[15];
lean_object* v_m_1326_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1327_; uint8_t v___x_676__boxed_1328_; double v_fst_677__boxed_1329_; double v_snd_678__boxed_1330_; lean_object* v_res_1331_; 
v_collapsed_boxed_1327_ = lean_unbox(v_collapsed_1321_);
v___x_676__boxed_1328_ = lean_unbox(v___x_1323_);
v_fst_677__boxed_1329_ = lean_unbox_float(v_fst_1324_);
lean_dec_ref(v_fst_1324_);
v_snd_678__boxed_1330_ = lean_unbox_float(v_snd_1325_);
lean_dec_ref(v_snd_1325_);
v_res_1331_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1310_, v_fst_1311_, v_inst_1312_, v_inst_1313_, v_inst_1314_, v_inst_1315_, v_oldTraces_1316_, v_ref_1317_, v_toBind_1318_, v___f_1319_, v_cls_1320_, v_collapsed_boxed_1327_, v_tag_1322_, v___x_676__boxed_1328_, v_fst_677__boxed_1329_, v_snd_678__boxed_1330_, v_m_1326_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(lean_object* v_always_1332_, lean_object* v_inst_1333_, lean_object* v_fst_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_oldTraces_1339_, lean_object* v_toBind_1340_, lean_object* v_cls_1341_, uint8_t v_collapsed_1342_, lean_object* v_tag_1343_, uint8_t v___x_1344_, double v_fst_1345_, double v_snd_1346_, lean_object* v_msg_1347_, lean_object* v___f_1348_, lean_object* v_ref_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v_tryCatch_1351_; lean_object* v___f_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___f_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_inc_ref(v_always_1332_);
v___x_1350_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1332_);
v_tryCatch_1351_ = lean_ctor_get(v_always_1332_, 1);
lean_inc(v_tryCatch_1351_);
lean_dec_ref(v_always_1332_);
lean_inc_ref_n(v_fst_1334_, 2);
lean_inc_ref(v_inst_1333_);
v___f_1352_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1352_, 0, v_inst_1333_);
lean_closure_set(v___f_1352_, 1, v___x_1350_);
lean_closure_set(v___f_1352_, 2, v_fst_1334_);
v___x_1353_ = lean_box(v_collapsed_1342_);
v___x_1354_ = lean_box(v___x_1344_);
v___x_1355_ = lean_box_float(v_fst_1345_);
v___x_1356_ = lean_box_float(v_snd_1346_);
lean_inc(v_toBind_1340_);
v___f_1357_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1357_, 0, v_inst_1335_);
lean_closure_set(v___f_1357_, 1, v_fst_1334_);
lean_closure_set(v___f_1357_, 2, v_inst_1333_);
lean_closure_set(v___f_1357_, 3, v_inst_1336_);
lean_closure_set(v___f_1357_, 4, v_inst_1337_);
lean_closure_set(v___f_1357_, 5, v_inst_1338_);
lean_closure_set(v___f_1357_, 6, v_oldTraces_1339_);
lean_closure_set(v___f_1357_, 7, v_ref_1349_);
lean_closure_set(v___f_1357_, 8, v_toBind_1340_);
lean_closure_set(v___f_1357_, 9, v___f_1352_);
lean_closure_set(v___f_1357_, 10, v_cls_1341_);
lean_closure_set(v___f_1357_, 11, v___x_1353_);
lean_closure_set(v___f_1357_, 12, v_tag_1343_);
lean_closure_set(v___f_1357_, 13, v___x_1354_);
lean_closure_set(v___f_1357_, 14, v___x_1355_);
lean_closure_set(v___f_1357_, 15, v___x_1356_);
v___x_1358_ = lean_apply_1(v_msg_1347_, v_fst_1334_);
v___x_1359_ = lean_apply_3(v_tryCatch_1351_, lean_box(0), v___x_1358_, v___f_1348_);
v___x_1360_ = lean_apply_4(v_toBind_1340_, lean_box(0), lean_box(0), v___x_1359_, v___f_1357_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_always_1361_ = _args[0];
lean_object* v_inst_1362_ = _args[1];
lean_object* v_fst_1363_ = _args[2];
lean_object* v_inst_1364_ = _args[3];
lean_object* v_inst_1365_ = _args[4];
lean_object* v_inst_1366_ = _args[5];
lean_object* v_inst_1367_ = _args[6];
lean_object* v_oldTraces_1368_ = _args[7];
lean_object* v_toBind_1369_ = _args[8];
lean_object* v_cls_1370_ = _args[9];
lean_object* v_collapsed_1371_ = _args[10];
lean_object* v_tag_1372_ = _args[11];
lean_object* v___x_1373_ = _args[12];
lean_object* v_fst_1374_ = _args[13];
lean_object* v_snd_1375_ = _args[14];
lean_object* v_msg_1376_ = _args[15];
lean_object* v___f_1377_ = _args[16];
lean_object* v_ref_1378_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_1379_; uint8_t v___x_728__boxed_1380_; double v_fst_729__boxed_1381_; double v_snd_730__boxed_1382_; lean_object* v_res_1383_; 
v_collapsed_boxed_1379_ = lean_unbox(v_collapsed_1371_);
v___x_728__boxed_1380_ = lean_unbox(v___x_1373_);
v_fst_729__boxed_1381_ = lean_unbox_float(v_fst_1374_);
lean_dec_ref(v_fst_1374_);
v_snd_730__boxed_1382_ = lean_unbox_float(v_snd_1375_);
lean_dec_ref(v_snd_1375_);
v_res_1383_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(v_always_1361_, v_inst_1362_, v_fst_1363_, v_inst_1364_, v_inst_1365_, v_inst_1366_, v_inst_1367_, v_oldTraces_1368_, v_toBind_1369_, v_cls_1370_, v_collapsed_boxed_1379_, v_tag_1372_, v___x_728__boxed_1380_, v_fst_729__boxed_1381_, v_snd_730__boxed_1382_, v_msg_1376_, v___f_1377_, v_ref_1378_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_always_1388_, lean_object* v_inst_1389_, lean_object* v_cls_1390_, uint8_t v_collapsed_1391_, lean_object* v_tag_1392_, lean_object* v_opts_1393_, uint8_t v_clsEnabled_1394_, lean_object* v_oldTraces_1395_, lean_object* v_msg_1396_, lean_object* v_resStartStop_1397_){
_start:
{
lean_object* v___x_1398_; lean_object* v_snd_1399_; lean_object* v_fst_1400_; lean_object* v_fst_1401_; lean_object* v_snd_1402_; lean_object* v___f_1403_; lean_object* v___f_1404_; lean_object* v___f_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___y_1415_; double v___y_1421_; uint8_t v___x_1426_; 
v___x_1398_ = l_Lean_KVMap_instValueBool;
v_snd_1399_ = lean_ctor_get(v_resStartStop_1397_, 1);
lean_inc(v_snd_1399_);
v_fst_1400_ = lean_ctor_get(v_resStartStop_1397_, 0);
lean_inc_n(v_fst_1400_, 2);
lean_dec_ref(v_resStartStop_1397_);
v_fst_1401_ = lean_ctor_get(v_snd_1399_, 0);
lean_inc(v_fst_1401_);
v_snd_1402_ = lean_ctor_get(v_snd_1399_, 1);
lean_inc(v_snd_1402_);
lean_dec(v_snd_1399_);
lean_inc_ref_n(v_inst_1384_, 2);
v___f_1403_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1403_, 0, v_inst_1384_);
lean_inc_ref(v_oldTraces_1395_);
v___f_1404_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1404_, 0, v_oldTraces_1395_);
lean_inc_ref(v_always_1388_);
v___f_1405_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1405_, 0, v_always_1388_);
lean_closure_set(v___f_1405_, 1, v_inst_1384_);
lean_closure_set(v___f_1405_, 2, v_fst_1400_);
v___x_1406_ = l_Lean_trace_profiler;
v___x_1407_ = l_Lean_Option_get___redArg(v___x_1398_, v_opts_1393_, v___x_1406_);
v___x_1426_ = lean_unbox(v___x_1407_);
if (v___x_1426_ == 0)
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_unbox(v___x_1407_);
v___y_1415_ = v___x_1427_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1429_ = l_Lean_Option_get___redArg(v___x_1398_, v_opts_1393_, v___x_1428_);
v___x_1430_ = lean_unbox(v___x_1429_);
lean_dec(v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; double v___x_1434_; double v___x_1435_; double v___x_1436_; 
v___x_1431_ = l_Lean_KVMap_instValueNat;
v___x_1432_ = l_Lean_trace_profiler_threshold;
v___x_1433_ = l_Lean_Option_get___redArg(v___x_1431_, v_opts_1393_, v___x_1432_);
v___x_1434_ = lean_float_of_nat(v___x_1433_);
v___x_1435_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1436_ = lean_float_div(v___x_1434_, v___x_1435_);
v___y_1421_ = v___x_1436_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; double v___x_1440_; 
v___x_1437_ = l_Lean_KVMap_instValueNat;
v___x_1438_ = l_Lean_trace_profiler_threshold;
v___x_1439_ = l_Lean_Option_get___redArg(v___x_1437_, v_opts_1393_, v___x_1438_);
v___x_1440_ = lean_float_of_nat(v___x_1439_);
v___y_1421_ = v___x_1440_;
goto v___jp_1420_;
}
}
v___jp_1408_:
{
lean_object* v_toBind_1409_; lean_object* v_getRef_1410_; lean_object* v___x_1411_; lean_object* v___f_1412_; lean_object* v___x_1413_; 
v_toBind_1409_ = lean_ctor_get(v_inst_1384_, 1);
lean_inc_n(v_toBind_1409_, 2);
v_getRef_1410_ = lean_ctor_get(v_inst_1386_, 0);
lean_inc(v_getRef_1410_);
v___x_1411_ = lean_box(v_collapsed_1391_);
v___f_1412_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed), 18, 17);
lean_closure_set(v___f_1412_, 0, v_always_1388_);
lean_closure_set(v___f_1412_, 1, v_inst_1384_);
lean_closure_set(v___f_1412_, 2, v_fst_1400_);
lean_closure_set(v___f_1412_, 3, v_inst_1389_);
lean_closure_set(v___f_1412_, 4, v_inst_1385_);
lean_closure_set(v___f_1412_, 5, v_inst_1386_);
lean_closure_set(v___f_1412_, 6, v_inst_1387_);
lean_closure_set(v___f_1412_, 7, v_oldTraces_1395_);
lean_closure_set(v___f_1412_, 8, v_toBind_1409_);
lean_closure_set(v___f_1412_, 9, v_cls_1390_);
lean_closure_set(v___f_1412_, 10, v___x_1411_);
lean_closure_set(v___f_1412_, 11, v_tag_1392_);
lean_closure_set(v___f_1412_, 12, v___x_1407_);
lean_closure_set(v___f_1412_, 13, v_fst_1401_);
lean_closure_set(v___f_1412_, 14, v_snd_1402_);
lean_closure_set(v___f_1412_, 15, v_msg_1396_);
lean_closure_set(v___f_1412_, 16, v___f_1403_);
v___x_1413_ = lean_apply_4(v_toBind_1409_, lean_box(0), lean_box(0), v_getRef_1410_, v___f_1412_);
return v___x_1413_;
}
v___jp_1414_:
{
if (v_clsEnabled_1394_ == 0)
{
if (v___y_1415_ == 0)
{
lean_object* v_toBind_1416_; lean_object* v_modifyTraceState_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec(v___x_1407_);
lean_dec_ref(v___f_1403_);
lean_dec(v_snd_1402_);
lean_dec(v_fst_1401_);
lean_dec(v_fst_1400_);
lean_dec(v_msg_1396_);
lean_dec_ref(v_oldTraces_1395_);
lean_dec_ref(v_tag_1392_);
lean_dec(v_cls_1390_);
lean_dec_ref(v_inst_1389_);
lean_dec_ref(v_always_1388_);
lean_dec(v_inst_1387_);
lean_dec_ref(v_inst_1386_);
v_toBind_1416_ = lean_ctor_get(v_inst_1384_, 1);
lean_inc(v_toBind_1416_);
lean_dec_ref(v_inst_1384_);
v_modifyTraceState_1417_ = lean_ctor_get(v_inst_1385_, 0);
lean_inc(v_modifyTraceState_1417_);
lean_dec_ref(v_inst_1385_);
v___x_1418_ = lean_apply_1(v_modifyTraceState_1417_, v___f_1404_);
v___x_1419_ = lean_apply_4(v_toBind_1416_, lean_box(0), lean_box(0), v___x_1418_, v___f_1405_);
return v___x_1419_;
}
else
{
lean_dec_ref(v___f_1405_);
lean_dec_ref(v___f_1404_);
goto v___jp_1408_;
}
}
else
{
lean_dec_ref(v___f_1405_);
lean_dec_ref(v___f_1404_);
goto v___jp_1408_;
}
}
v___jp_1420_:
{
double v___x_1422_; double v___x_1423_; double v___x_1424_; uint8_t v___x_1425_; 
v___x_1422_ = lean_unbox_float(v_snd_1402_);
v___x_1423_ = lean_unbox_float(v_fst_1401_);
v___x_1424_ = lean_float_sub(v___x_1422_, v___x_1423_);
v___x_1425_ = lean_float_decLt(v___y_1421_, v___x_1424_);
v___y_1415_ = v___x_1425_;
goto v___jp_1414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_always_1445_, lean_object* v_inst_1446_, lean_object* v_cls_1447_, lean_object* v_collapsed_1448_, lean_object* v_tag_1449_, lean_object* v_opts_1450_, lean_object* v_clsEnabled_1451_, lean_object* v_oldTraces_1452_, lean_object* v_msg_1453_, lean_object* v_resStartStop_1454_){
_start:
{
uint8_t v_collapsed_boxed_1455_; uint8_t v_clsEnabled_boxed_1456_; lean_object* v_res_1457_; 
v_collapsed_boxed_1455_ = lean_unbox(v_collapsed_1448_);
v_clsEnabled_boxed_1456_ = lean_unbox(v_clsEnabled_1451_);
v_res_1457_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1441_, v_inst_1442_, v_inst_1443_, v_inst_1444_, v_always_1445_, v_inst_1446_, v_cls_1447_, v_collapsed_boxed_1455_, v_tag_1449_, v_opts_1450_, v_clsEnabled_boxed_1456_, v_oldTraces_1452_, v_msg_1453_, v_resStartStop_1454_);
lean_dec_ref(v_opts_1450_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object* v_00_u03b1_1458_, lean_object* v_m_1459_, lean_object* v_inst_1460_, lean_object* v_inst_1461_, lean_object* v_inst_1462_, lean_object* v_inst_1463_, lean_object* v_00_u03b5_1464_, lean_object* v_always_1465_, lean_object* v_inst_1466_, lean_object* v_cls_1467_, uint8_t v_collapsed_1468_, lean_object* v_tag_1469_, lean_object* v_opts_1470_, uint8_t v_clsEnabled_1471_, lean_object* v_oldTraces_1472_, lean_object* v_msg_1473_, lean_object* v_resStartStop_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1460_, v_inst_1461_, v_inst_1462_, v_inst_1463_, v_always_1465_, v_inst_1466_, v_cls_1467_, v_collapsed_1468_, v_tag_1469_, v_opts_1470_, v_clsEnabled_1471_, v_oldTraces_1472_, v_msg_1473_, v_resStartStop_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_1476_ = _args[0];
lean_object* v_m_1477_ = _args[1];
lean_object* v_inst_1478_ = _args[2];
lean_object* v_inst_1479_ = _args[3];
lean_object* v_inst_1480_ = _args[4];
lean_object* v_inst_1481_ = _args[5];
lean_object* v_00_u03b5_1482_ = _args[6];
lean_object* v_always_1483_ = _args[7];
lean_object* v_inst_1484_ = _args[8];
lean_object* v_cls_1485_ = _args[9];
lean_object* v_collapsed_1486_ = _args[10];
lean_object* v_tag_1487_ = _args[11];
lean_object* v_opts_1488_ = _args[12];
lean_object* v_clsEnabled_1489_ = _args[13];
lean_object* v_oldTraces_1490_ = _args[14];
lean_object* v_msg_1491_ = _args[15];
lean_object* v_resStartStop_1492_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1493_; uint8_t v_clsEnabled_boxed_1494_; lean_object* v_res_1495_; 
v_collapsed_boxed_1493_ = lean_unbox(v_collapsed_1486_);
v_clsEnabled_boxed_1494_ = lean_unbox(v_clsEnabled_1489_);
v_res_1495_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(v_00_u03b1_1476_, v_m_1477_, v_inst_1478_, v_inst_1479_, v_inst_1480_, v_inst_1481_, v_00_u03b5_1482_, v_always_1483_, v_inst_1484_, v_cls_1485_, v_collapsed_boxed_1493_, v_tag_1487_, v_opts_1488_, v_clsEnabled_boxed_1494_, v_oldTraces_1490_, v_msg_1491_, v_resStartStop_1492_);
lean_dec_ref(v_opts_1488_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_inst_1499_, lean_object* v_always_1500_, lean_object* v_inst_1501_, lean_object* v_cls_1502_, uint8_t v_collapsed_1503_, lean_object* v_tag_1504_, lean_object* v_opts_1505_, uint8_t v_clsEnabled_1506_, lean_object* v_oldTraces_1507_, lean_object* v_msg_1508_, lean_object* v_resStartStop_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1496_, v_inst_1497_, v_inst_1498_, v_inst_1499_, v_always_1500_, v_inst_1501_, v_cls_1502_, v_collapsed_1503_, v_tag_1504_, v_opts_1505_, v_clsEnabled_1506_, v_oldTraces_1507_, v_msg_1508_, v_resStartStop_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_always_1515_, lean_object* v_inst_1516_, lean_object* v_cls_1517_, lean_object* v_collapsed_1518_, lean_object* v_tag_1519_, lean_object* v_opts_1520_, lean_object* v_clsEnabled_1521_, lean_object* v_oldTraces_1522_, lean_object* v_msg_1523_, lean_object* v_resStartStop_1524_){
_start:
{
uint8_t v_collapsed_boxed_1525_; uint8_t v_clsEnabled_boxed_1526_; lean_object* v_res_1527_; 
v_collapsed_boxed_1525_ = lean_unbox(v_collapsed_1518_);
v_clsEnabled_boxed_1526_ = lean_unbox(v_clsEnabled_1521_);
v_res_1527_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1511_, v_inst_1512_, v_inst_1513_, v_inst_1514_, v_always_1515_, v_inst_1516_, v_cls_1517_, v_collapsed_boxed_1525_, v_tag_1519_, v_opts_1520_, v_clsEnabled_boxed_1526_, v_oldTraces_1522_, v_msg_1523_, v_resStartStop_1524_);
lean_dec_ref(v_opts_1520_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object* v_toPure_1528_, lean_object* v_ex_1529_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_ex_1529_);
v___x_1531_ = lean_apply_2(v_toPure_1528_, lean_box(0), v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object* v_toPure_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_a_1533_);
v___x_1535_ = lean_apply_2(v_toPure_1532_, lean_box(0), v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object* v_start_1536_, lean_object* v_a_1537_, lean_object* v_toPure_1538_, lean_object* v_stop_1539_){
_start:
{
double v___x_1540_; double v___x_1541_; double v___x_1542_; double v___x_1543_; double v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1540_ = lean_float_of_nat(v_start_1536_);
v___x_1541_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1542_ = lean_float_div(v___x_1540_, v___x_1541_);
v___x_1543_ = lean_float_of_nat(v_stop_1539_);
v___x_1544_ = lean_float_div(v___x_1543_, v___x_1541_);
v___x_1545_ = lean_box_float(v___x_1542_);
v___x_1546_ = lean_box_float(v___x_1544_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_a_1537_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = lean_apply_2(v_toPure_1538_, lean_box(0), v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object* v_start_1550_, lean_object* v_toPure_1551_, lean_object* v_toBind_1552_, lean_object* v___x_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___f_1555_; lean_object* v___x_1556_; 
v___f_1555_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1555_, 0, v_start_1550_);
lean_closure_set(v___f_1555_, 1, v_a_1554_);
lean_closure_set(v___f_1555_, 2, v_toPure_1551_);
v___x_1556_ = lean_apply_4(v_toBind_1552_, lean_box(0), lean_box(0), v___x_1553_, v___f_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object* v_toPure_1557_, lean_object* v_toBind_1558_, lean_object* v___x_1559_, lean_object* v___x_1560_, lean_object* v_start_1561_){
_start:
{
lean_object* v___f_1562_; lean_object* v___x_1563_; 
lean_inc(v_toBind_1558_);
v___f_1562_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1562_, 0, v_start_1561_);
lean_closure_set(v___f_1562_, 1, v_toPure_1557_);
lean_closure_set(v___f_1562_, 2, v_toBind_1558_);
lean_closure_set(v___f_1562_, 3, v___x_1559_);
v___x_1563_ = lean_apply_4(v_toBind_1558_, lean_box(0), lean_box(0), v___x_1560_, v___f_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object* v_start_1564_, lean_object* v_a_1565_, lean_object* v_toPure_1566_, lean_object* v_stop_1567_){
_start:
{
double v___x_1568_; double v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1568_ = lean_float_of_nat(v_start_1564_);
v___x_1569_ = lean_float_of_nat(v_stop_1567_);
v___x_1570_ = lean_box_float(v___x_1568_);
v___x_1571_ = lean_box_float(v___x_1569_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v_a_1565_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = lean_apply_2(v_toPure_1566_, lean_box(0), v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object* v_start_1575_, lean_object* v_toPure_1576_, lean_object* v_toBind_1577_, lean_object* v___x_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___f_1580_; lean_object* v___x_1581_; 
v___f_1580_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__6), 4, 3);
lean_closure_set(v___f_1580_, 0, v_start_1575_);
lean_closure_set(v___f_1580_, 1, v_a_1579_);
lean_closure_set(v___f_1580_, 2, v_toPure_1576_);
v___x_1581_ = lean_apply_4(v_toBind_1577_, lean_box(0), lean_box(0), v___x_1578_, v___f_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object* v_toPure_1582_, lean_object* v_toBind_1583_, lean_object* v___x_1584_, lean_object* v___x_1585_, lean_object* v_start_1586_){
_start:
{
lean_object* v___f_1587_; lean_object* v___x_1588_; 
lean_inc(v_toBind_1583_);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1587_, 0, v_start_1586_);
lean_closure_set(v___f_1587_, 1, v_toPure_1582_);
lean_closure_set(v___f_1587_, 2, v_toBind_1583_);
lean_closure_set(v___f_1587_, 3, v___x_1584_);
v___x_1588_ = lean_apply_4(v_toBind_1583_, lean_box(0), lean_box(0), v___x_1585_, v___f_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object* v_always_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_cls_1595_, uint8_t v_collapsed_1596_, lean_object* v_tag_1597_, lean_object* v_opts_1598_, uint8_t v_clsEnabled_1599_, lean_object* v_msg_1600_, lean_object* v_toPure_1601_, lean_object* v_toBind_1602_, lean_object* v_k_1603_, lean_object* v_inst_1604_, lean_object* v_oldTraces_1605_){
_start:
{
lean_object* v_tryCatch_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___f_1609_; lean_object* v___f_1610_; lean_object* v___f_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_tryCatch_1606_ = lean_ctor_get(v_always_1589_, 1);
lean_inc(v_tryCatch_1606_);
v___x_1607_ = lean_box(v_collapsed_1596_);
v___x_1608_ = lean_box(v_clsEnabled_1599_);
lean_inc_ref(v_opts_1598_);
v___f_1609_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1609_, 0, v_inst_1590_);
lean_closure_set(v___f_1609_, 1, v_inst_1591_);
lean_closure_set(v___f_1609_, 2, v_inst_1592_);
lean_closure_set(v___f_1609_, 3, v_inst_1593_);
lean_closure_set(v___f_1609_, 4, v_always_1589_);
lean_closure_set(v___f_1609_, 5, v_inst_1594_);
lean_closure_set(v___f_1609_, 6, v_cls_1595_);
lean_closure_set(v___f_1609_, 7, v___x_1607_);
lean_closure_set(v___f_1609_, 8, v_tag_1597_);
lean_closure_set(v___f_1609_, 9, v_opts_1598_);
lean_closure_set(v___f_1609_, 10, v___x_1608_);
lean_closure_set(v___f_1609_, 11, v_oldTraces_1605_);
lean_closure_set(v___f_1609_, 12, v_msg_1600_);
lean_inc_n(v_toPure_1601_, 2);
v___f_1610_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1610_, 0, v_toPure_1601_);
v___f_1611_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1611_, 0, v_toPure_1601_);
lean_inc(v_toBind_1602_);
v___x_1612_ = lean_apply_4(v_toBind_1602_, lean_box(0), lean_box(0), v_k_1603_, v___f_1611_);
v___x_1613_ = lean_apply_3(v_tryCatch_1606_, lean_box(0), v___x_1612_, v___f_1610_);
v___x_1614_ = l_Lean_KVMap_instValueBool;
v___x_1615_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1616_ = l_Lean_Option_get___redArg(v___x_1614_, v_opts_1598_, v___x_1615_);
lean_dec_ref(v_opts_1598_);
v___x_1617_ = lean_unbox(v___x_1616_);
lean_dec(v___x_1616_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___f_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1618_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1619_ = lean_apply_2(v_inst_1604_, lean_box(0), v___x_1618_);
lean_inc(v___x_1619_);
lean_inc_n(v_toBind_1602_, 2);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1620_, 0, v_toPure_1601_);
lean_closure_set(v___f_1620_, 1, v_toBind_1602_);
lean_closure_set(v___f_1620_, 2, v___x_1619_);
lean_closure_set(v___f_1620_, 3, v___x_1613_);
v___x_1621_ = lean_apply_4(v_toBind_1602_, lean_box(0), lean_box(0), v___x_1619_, v___f_1620_);
v___x_1622_ = lean_apply_4(v_toBind_1602_, lean_box(0), lean_box(0), v___x_1621_, v___f_1609_);
return v___x_1622_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___f_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1624_ = lean_apply_2(v_inst_1604_, lean_box(0), v___x_1623_);
lean_inc(v___x_1624_);
lean_inc_n(v_toBind_1602_, 2);
v___f_1625_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_1625_, 0, v_toPure_1601_);
lean_closure_set(v___f_1625_, 1, v_toBind_1602_);
lean_closure_set(v___f_1625_, 2, v___x_1624_);
lean_closure_set(v___f_1625_, 3, v___x_1613_);
v___x_1626_ = lean_apply_4(v_toBind_1602_, lean_box(0), lean_box(0), v___x_1624_, v___f_1625_);
v___x_1627_ = lean_apply_4(v_toBind_1602_, lean_box(0), lean_box(0), v___x_1626_, v___f_1609_);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_always_1628_ = _args[0];
lean_object* v_inst_1629_ = _args[1];
lean_object* v_inst_1630_ = _args[2];
lean_object* v_inst_1631_ = _args[3];
lean_object* v_inst_1632_ = _args[4];
lean_object* v_inst_1633_ = _args[5];
lean_object* v_cls_1634_ = _args[6];
lean_object* v_collapsed_1635_ = _args[7];
lean_object* v_tag_1636_ = _args[8];
lean_object* v_opts_1637_ = _args[9];
lean_object* v_clsEnabled_1638_ = _args[10];
lean_object* v_msg_1639_ = _args[11];
lean_object* v_toPure_1640_ = _args[12];
lean_object* v_toBind_1641_ = _args[13];
lean_object* v_k_1642_ = _args[14];
lean_object* v_inst_1643_ = _args[15];
lean_object* v_oldTraces_1644_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1645_; uint8_t v_clsEnabled_boxed_1646_; lean_object* v_res_1647_; 
v_collapsed_boxed_1645_ = lean_unbox(v_collapsed_1635_);
v_clsEnabled_boxed_1646_ = lean_unbox(v_clsEnabled_1638_);
v_res_1647_ = l_Lean_withTraceNode___redArg___lam__9(v_always_1628_, v_inst_1629_, v_inst_1630_, v_inst_1631_, v_inst_1632_, v_inst_1633_, v_cls_1634_, v_collapsed_boxed_1645_, v_tag_1636_, v_opts_1637_, v_clsEnabled_boxed_1646_, v_msg_1639_, v_toPure_1640_, v_toBind_1641_, v_k_1642_, v_inst_1643_, v_oldTraces_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object* v_always_1648_, lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_cls_1654_, uint8_t v_collapsed_1655_, lean_object* v_tag_1656_, lean_object* v_opts_1657_, lean_object* v_msg_1658_, lean_object* v_toPure_1659_, lean_object* v_toBind_1660_, lean_object* v_k_1661_, lean_object* v_inst_1662_, uint8_t v_clsEnabled_1663_){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___f_1666_; 
v___x_1664_ = lean_box(v_collapsed_1655_);
v___x_1665_ = lean_box(v_clsEnabled_1663_);
lean_inc(v_k_1661_);
lean_inc(v_toBind_1660_);
lean_inc_ref(v_opts_1657_);
lean_inc_ref(v_inst_1650_);
lean_inc_ref(v_inst_1649_);
v___f_1666_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_1666_, 0, v_always_1648_);
lean_closure_set(v___f_1666_, 1, v_inst_1649_);
lean_closure_set(v___f_1666_, 2, v_inst_1650_);
lean_closure_set(v___f_1666_, 3, v_inst_1651_);
lean_closure_set(v___f_1666_, 4, v_inst_1652_);
lean_closure_set(v___f_1666_, 5, v_inst_1653_);
lean_closure_set(v___f_1666_, 6, v_cls_1654_);
lean_closure_set(v___f_1666_, 7, v___x_1664_);
lean_closure_set(v___f_1666_, 8, v_tag_1656_);
lean_closure_set(v___f_1666_, 9, v_opts_1657_);
lean_closure_set(v___f_1666_, 10, v___x_1665_);
lean_closure_set(v___f_1666_, 11, v_msg_1658_);
lean_closure_set(v___f_1666_, 12, v_toPure_1659_);
lean_closure_set(v___f_1666_, 13, v_toBind_1660_);
lean_closure_set(v___f_1666_, 14, v_k_1661_);
lean_closure_set(v___f_1666_, 15, v_inst_1662_);
if (v_clsEnabled_1663_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1670_ = l_Lean_KVMap_instValueBool;
v___x_1671_ = l_Lean_trace_profiler;
v___x_1672_ = l_Lean_Option_get___redArg(v___x_1670_, v_opts_1657_, v___x_1671_);
lean_dec_ref(v_opts_1657_);
v___x_1673_ = lean_unbox(v___x_1672_);
lean_dec(v___x_1672_);
if (v___x_1673_ == 0)
{
lean_dec_ref(v___f_1666_);
lean_dec(v_toBind_1660_);
lean_dec_ref(v_inst_1650_);
lean_dec_ref(v_inst_1649_);
return v_k_1661_;
}
else
{
lean_dec(v_k_1661_);
goto v___jp_1667_;
}
}
else
{
lean_dec(v_k_1661_);
lean_dec_ref(v_opts_1657_);
goto v___jp_1667_;
}
v___jp_1667_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1649_, v_inst_1650_);
v___x_1669_ = lean_apply_4(v_toBind_1660_, lean_box(0), lean_box(0), v___x_1668_, v___f_1666_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object* v_always_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_cls_1680_, lean_object* v_collapsed_1681_, lean_object* v_tag_1682_, lean_object* v_opts_1683_, lean_object* v_msg_1684_, lean_object* v_toPure_1685_, lean_object* v_toBind_1686_, lean_object* v_k_1687_, lean_object* v_inst_1688_, lean_object* v_clsEnabled_1689_){
_start:
{
uint8_t v_collapsed_boxed_1690_; uint8_t v_clsEnabled_boxed_1691_; lean_object* v_res_1692_; 
v_collapsed_boxed_1690_ = lean_unbox(v_collapsed_1681_);
v_clsEnabled_boxed_1691_ = lean_unbox(v_clsEnabled_1689_);
v_res_1692_ = l_Lean_withTraceNode___redArg___lam__10(v_always_1674_, v_inst_1675_, v_inst_1676_, v_inst_1677_, v_inst_1678_, v_inst_1679_, v_cls_1680_, v_collapsed_boxed_1690_, v_tag_1682_, v_opts_1683_, v_msg_1684_, v_toPure_1685_, v_toBind_1686_, v_k_1687_, v_inst_1688_, v_clsEnabled_boxed_1691_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object* v_k_1693_, lean_object* v_inst_1694_, lean_object* v_toApplicative_1695_, lean_object* v_always_1696_, lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_cls_1701_, uint8_t v_collapsed_1702_, lean_object* v_tag_1703_, lean_object* v_msg_1704_, lean_object* v_toBind_1705_, lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_opts_1708_){
_start:
{
uint8_t v_hasTrace_1709_; 
v_hasTrace_1709_ = lean_ctor_get_uint8(v_opts_1708_, sizeof(void*)*1);
if (v_hasTrace_1709_ == 0)
{
lean_dec_ref(v_opts_1708_);
lean_dec(v_inst_1707_);
lean_dec(v_inst_1706_);
lean_dec(v_toBind_1705_);
lean_dec(v_msg_1704_);
lean_dec_ref(v_tag_1703_);
lean_dec(v_cls_1701_);
lean_dec_ref(v_inst_1700_);
lean_dec(v_inst_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec_ref(v_inst_1697_);
lean_dec_ref(v_always_1696_);
lean_dec_ref(v_toApplicative_1695_);
lean_dec_ref(v_inst_1694_);
return v_k_1693_;
}
else
{
lean_object* v_getInheritedTraceOptions_1710_; lean_object* v_toPure_1711_; lean_object* v___x_1712_; lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_getInheritedTraceOptions_1710_ = lean_ctor_get(v_inst_1694_, 2);
lean_inc(v_getInheritedTraceOptions_1710_);
v_toPure_1711_ = lean_ctor_get(v_toApplicative_1695_, 1);
lean_inc_n(v_toPure_1711_, 2);
lean_dec_ref(v_toApplicative_1695_);
v___x_1712_ = lean_box(v_collapsed_1702_);
lean_inc_n(v_toBind_1705_, 3);
lean_inc(v_cls_1701_);
v___f_1713_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_1713_, 0, v_always_1696_);
lean_closure_set(v___f_1713_, 1, v_inst_1697_);
lean_closure_set(v___f_1713_, 2, v_inst_1694_);
lean_closure_set(v___f_1713_, 3, v_inst_1698_);
lean_closure_set(v___f_1713_, 4, v_inst_1699_);
lean_closure_set(v___f_1713_, 5, v_inst_1700_);
lean_closure_set(v___f_1713_, 6, v_cls_1701_);
lean_closure_set(v___f_1713_, 7, v___x_1712_);
lean_closure_set(v___f_1713_, 8, v_tag_1703_);
lean_closure_set(v___f_1713_, 9, v_opts_1708_);
lean_closure_set(v___f_1713_, 10, v_msg_1704_);
lean_closure_set(v___f_1713_, 11, v_toPure_1711_);
lean_closure_set(v___f_1713_, 12, v_toBind_1705_);
lean_closure_set(v___f_1713_, 13, v_k_1693_);
lean_closure_set(v___f_1713_, 14, v_inst_1706_);
v___f_1714_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1714_, 0, v_toPure_1711_);
lean_closure_set(v___f_1714_, 1, v_cls_1701_);
lean_closure_set(v___f_1714_, 2, v_toBind_1705_);
lean_closure_set(v___f_1714_, 3, v_inst_1707_);
v___x_1715_ = lean_apply_4(v_toBind_1705_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1710_, v___f_1714_);
v___x_1716_ = lean_apply_4(v_toBind_1705_, lean_box(0), lean_box(0), v___x_1715_, v___f_1713_);
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13___boxed(lean_object* v_k_1717_, lean_object* v_inst_1718_, lean_object* v_toApplicative_1719_, lean_object* v_always_1720_, lean_object* v_inst_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_cls_1725_, lean_object* v_collapsed_1726_, lean_object* v_tag_1727_, lean_object* v_msg_1728_, lean_object* v_toBind_1729_, lean_object* v_inst_1730_, lean_object* v_inst_1731_, lean_object* v_opts_1732_){
_start:
{
uint8_t v_collapsed_boxed_1733_; lean_object* v_res_1734_; 
v_collapsed_boxed_1733_ = lean_unbox(v_collapsed_1726_);
v_res_1734_ = l_Lean_withTraceNode___redArg___lam__13(v_k_1717_, v_inst_1718_, v_toApplicative_1719_, v_always_1720_, v_inst_1721_, v_inst_1722_, v_inst_1723_, v_inst_1724_, v_cls_1725_, v_collapsed_boxed_1733_, v_tag_1727_, v_msg_1728_, v_toBind_1729_, v_inst_1730_, v_inst_1731_, v_opts_1732_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_inst_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_always_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_cls_1743_, lean_object* v_msg_1744_, lean_object* v_k_1745_, uint8_t v_collapsed_1746_, lean_object* v_tag_1747_){
_start:
{
lean_object* v_toApplicative_1748_; lean_object* v_toBind_1749_; lean_object* v___x_1750_; lean_object* v___f_1751_; lean_object* v___x_1752_; 
v_toApplicative_1748_ = lean_ctor_get(v_inst_1735_, 0);
lean_inc_ref(v_toApplicative_1748_);
v_toBind_1749_ = lean_ctor_get(v_inst_1735_, 1);
lean_inc_n(v_toBind_1749_, 2);
v___x_1750_ = lean_box(v_collapsed_1746_);
lean_inc(v_inst_1739_);
v___f_1751_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1751_, 0, v_k_1745_);
lean_closure_set(v___f_1751_, 1, v_inst_1736_);
lean_closure_set(v___f_1751_, 2, v_toApplicative_1748_);
lean_closure_set(v___f_1751_, 3, v_always_1740_);
lean_closure_set(v___f_1751_, 4, v_inst_1735_);
lean_closure_set(v___f_1751_, 5, v_inst_1737_);
lean_closure_set(v___f_1751_, 6, v_inst_1738_);
lean_closure_set(v___f_1751_, 7, v_inst_1742_);
lean_closure_set(v___f_1751_, 8, v_cls_1743_);
lean_closure_set(v___f_1751_, 9, v___x_1750_);
lean_closure_set(v___f_1751_, 10, v_tag_1747_);
lean_closure_set(v___f_1751_, 11, v_msg_1744_);
lean_closure_set(v___f_1751_, 12, v_toBind_1749_);
lean_closure_set(v___f_1751_, 13, v_inst_1741_);
lean_closure_set(v___f_1751_, 14, v_inst_1739_);
v___x_1752_ = lean_apply_4(v_toBind_1749_, lean_box(0), lean_box(0), v_inst_1739_, v___f_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object* v_inst_1753_, lean_object* v_inst_1754_, lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_always_1758_, lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_cls_1761_, lean_object* v_msg_1762_, lean_object* v_k_1763_, lean_object* v_collapsed_1764_, lean_object* v_tag_1765_){
_start:
{
uint8_t v_collapsed_boxed_1766_; lean_object* v_res_1767_; 
v_collapsed_boxed_1766_ = lean_unbox(v_collapsed_1764_);
v_res_1767_ = l_Lean_withTraceNode___redArg(v_inst_1753_, v_inst_1754_, v_inst_1755_, v_inst_1756_, v_inst_1757_, v_always_1758_, v_inst_1759_, v_inst_1760_, v_cls_1761_, v_msg_1762_, v_k_1763_, v_collapsed_boxed_1766_, v_tag_1765_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object* v_00_u03b1_1768_, lean_object* v_m_1769_, lean_object* v_inst_1770_, lean_object* v_inst_1771_, lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_00_u03b5_1775_, lean_object* v_always_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_cls_1779_, lean_object* v_msg_1780_, lean_object* v_k_1781_, uint8_t v_collapsed_1782_, lean_object* v_tag_1783_){
_start:
{
lean_object* v_toApplicative_1784_; lean_object* v_toBind_1785_; lean_object* v___x_1786_; lean_object* v___f_1787_; lean_object* v___x_1788_; 
v_toApplicative_1784_ = lean_ctor_get(v_inst_1770_, 0);
lean_inc_ref(v_toApplicative_1784_);
v_toBind_1785_ = lean_ctor_get(v_inst_1770_, 1);
lean_inc_n(v_toBind_1785_, 2);
v___x_1786_ = lean_box(v_collapsed_1782_);
lean_inc(v_inst_1774_);
v___f_1787_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1787_, 0, v_k_1781_);
lean_closure_set(v___f_1787_, 1, v_inst_1771_);
lean_closure_set(v___f_1787_, 2, v_toApplicative_1784_);
lean_closure_set(v___f_1787_, 3, v_always_1776_);
lean_closure_set(v___f_1787_, 4, v_inst_1770_);
lean_closure_set(v___f_1787_, 5, v_inst_1772_);
lean_closure_set(v___f_1787_, 6, v_inst_1773_);
lean_closure_set(v___f_1787_, 7, v_inst_1778_);
lean_closure_set(v___f_1787_, 8, v_cls_1779_);
lean_closure_set(v___f_1787_, 9, v___x_1786_);
lean_closure_set(v___f_1787_, 10, v_tag_1783_);
lean_closure_set(v___f_1787_, 11, v_msg_1780_);
lean_closure_set(v___f_1787_, 12, v_toBind_1785_);
lean_closure_set(v___f_1787_, 13, v_inst_1777_);
lean_closure_set(v___f_1787_, 14, v_inst_1774_);
v___x_1788_ = lean_apply_4(v_toBind_1785_, lean_box(0), lean_box(0), v_inst_1774_, v___f_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object* v_00_u03b1_1789_, lean_object* v_m_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_00_u03b5_1796_, lean_object* v_always_1797_, lean_object* v_inst_1798_, lean_object* v_inst_1799_, lean_object* v_cls_1800_, lean_object* v_msg_1801_, lean_object* v_k_1802_, lean_object* v_collapsed_1803_, lean_object* v_tag_1804_){
_start:
{
uint8_t v_collapsed_boxed_1805_; lean_object* v_res_1806_; 
v_collapsed_boxed_1805_ = lean_unbox(v_collapsed_1803_);
v_res_1806_ = l_Lean_withTraceNode(v_00_u03b1_1789_, v_m_1790_, v_inst_1791_, v_inst_1792_, v_inst_1793_, v_inst_1794_, v_inst_1795_, v_00_u03b5_1796_, v_always_1797_, v_inst_1798_, v_inst_1799_, v_cls_1800_, v_msg_1801_, v_k_1802_, v_collapsed_boxed_1805_, v_tag_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object* v_self_1807_){
_start:
{
lean_object* v_fst_1808_; 
v_fst_1808_ = lean_ctor_get(v_self_1807_, 0);
lean_inc(v_fst_1808_);
return v_fst_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object* v_self_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_1809_);
lean_dec_ref(v_self_1809_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object* v_toPure_1811_, lean_object* v_x_1812_){
_start:
{
if (lean_obj_tag(v_x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v_a_1813_ = lean_ctor_get(v_x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref(v_x_1812_);
v___x_1814_ = l_Lean_Exception_toMessageData(v_a_1813_);
v___x_1815_ = lean_apply_2(v_toPure_1811_, lean_box(0), v___x_1814_);
return v___x_1815_;
}
else
{
lean_object* v_a_1816_; lean_object* v_snd_1817_; lean_object* v___x_1818_; 
v_a_1816_ = lean_ctor_get(v_x_1812_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v_x_1812_);
v_snd_1817_ = lean_ctor_get(v_a_1816_, 1);
lean_inc(v_snd_1817_);
lean_dec(v_a_1816_);
v___x_1818_ = lean_apply_2(v_toPure_1811_, lean_box(0), v_snd_1817_);
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object* v_toPure_1819_, lean_object* v_ex_1820_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v_ex_1820_);
v___x_1822_ = lean_apply_2(v_toPure_1819_, lean_box(0), v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object* v_toPure_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_a_1824_);
v___x_1826_ = lean_apply_2(v_toPure_1823_, lean_box(0), v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v___f_1832_, lean_object* v_cls_1833_, uint8_t v_collapsed_1834_, lean_object* v_tag_1835_, lean_object* v_opts_1836_, uint8_t v_clsEnabled_1837_, lean_object* v_oldTraces_1838_, lean_object* v_msg_1839_, lean_object* v_resStartStop_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1827_, v_inst_1828_, v_inst_1829_, v_inst_1830_, v_inst_1831_, v___f_1832_, v_cls_1833_, v_collapsed_1834_, v_tag_1835_, v_opts_1836_, v_clsEnabled_1837_, v_oldTraces_1838_, v_msg_1839_, v_resStartStop_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3___boxed(lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v___f_1847_, lean_object* v_cls_1848_, lean_object* v_collapsed_1849_, lean_object* v_tag_1850_, lean_object* v_opts_1851_, lean_object* v_clsEnabled_1852_, lean_object* v_oldTraces_1853_, lean_object* v_msg_1854_, lean_object* v_resStartStop_1855_){
_start:
{
uint8_t v_collapsed_boxed_1856_; uint8_t v_clsEnabled_boxed_1857_; lean_object* v_res_1858_; 
v_collapsed_boxed_1856_ = lean_unbox(v_collapsed_1849_);
v_clsEnabled_boxed_1857_ = lean_unbox(v_clsEnabled_1852_);
v_res_1858_ = l_Lean_withTraceNode_x27___redArg___lam__3(v_inst_1842_, v_inst_1843_, v_inst_1844_, v_inst_1845_, v_inst_1846_, v___f_1847_, v_cls_1848_, v_collapsed_boxed_1856_, v_tag_1850_, v_opts_1851_, v_clsEnabled_boxed_1857_, v_oldTraces_1853_, v_msg_1854_, v_resStartStop_1855_);
lean_dec_ref(v_opts_1851_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object* v_start_1859_, lean_object* v_a_1860_, lean_object* v_toPure_1861_, lean_object* v_stop_1862_){
_start:
{
double v___x_1863_; double v___x_1864_; double v___x_1865_; double v___x_1866_; double v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1863_ = lean_float_of_nat(v_start_1859_);
v___x_1864_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1865_ = lean_float_div(v___x_1863_, v___x_1864_);
v___x_1866_ = lean_float_of_nat(v_stop_1862_);
v___x_1867_ = lean_float_div(v___x_1866_, v___x_1864_);
v___x_1868_ = lean_box_float(v___x_1865_);
v___x_1869_ = lean_box_float(v___x_1867_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v_a_1860_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_apply_2(v_toPure_1861_, lean_box(0), v___x_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object* v_start_1873_, lean_object* v_toPure_1874_, lean_object* v_toBind_1875_, lean_object* v___x_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v___f_1878_; lean_object* v___x_1879_; 
v___f_1878_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__5), 4, 3);
lean_closure_set(v___f_1878_, 0, v_start_1873_);
lean_closure_set(v___f_1878_, 1, v_a_1877_);
lean_closure_set(v___f_1878_, 2, v_toPure_1874_);
v___x_1879_ = lean_apply_4(v_toBind_1875_, lean_box(0), lean_box(0), v___x_1876_, v___f_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object* v_toPure_1880_, lean_object* v_toBind_1881_, lean_object* v___x_1882_, lean_object* v___x_1883_, lean_object* v_start_1884_){
_start:
{
lean_object* v___f_1885_; lean_object* v___x_1886_; 
lean_inc(v_toBind_1881_);
v___f_1885_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__6), 5, 4);
lean_closure_set(v___f_1885_, 0, v_start_1884_);
lean_closure_set(v___f_1885_, 1, v_toPure_1880_);
lean_closure_set(v___f_1885_, 2, v_toBind_1881_);
lean_closure_set(v___f_1885_, 3, v___x_1882_);
v___x_1886_ = lean_apply_4(v_toBind_1881_, lean_box(0), lean_box(0), v___x_1883_, v___f_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object* v_start_1887_, lean_object* v_a_1888_, lean_object* v_toPure_1889_, lean_object* v_stop_1890_){
_start:
{
double v___x_1891_; double v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1891_ = lean_float_of_nat(v_start_1887_);
v___x_1892_ = lean_float_of_nat(v_stop_1890_);
v___x_1893_ = lean_box_float(v___x_1891_);
v___x_1894_ = lean_box_float(v___x_1892_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_a_1888_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = lean_apply_2(v_toPure_1889_, lean_box(0), v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object* v_start_1898_, lean_object* v_toPure_1899_, lean_object* v_toBind_1900_, lean_object* v___x_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___f_1903_; lean_object* v___x_1904_; 
v___f_1903_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__8), 4, 3);
lean_closure_set(v___f_1903_, 0, v_start_1898_);
lean_closure_set(v___f_1903_, 1, v_a_1902_);
lean_closure_set(v___f_1903_, 2, v_toPure_1899_);
v___x_1904_ = lean_apply_4(v_toBind_1900_, lean_box(0), lean_box(0), v___x_1901_, v___f_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object* v_toPure_1905_, lean_object* v_toBind_1906_, lean_object* v___x_1907_, lean_object* v___x_1908_, lean_object* v_start_1909_){
_start:
{
lean_object* v___f_1910_; lean_object* v___x_1911_; 
lean_inc(v_toBind_1906_);
v___f_1910_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__9), 5, 4);
lean_closure_set(v___f_1910_, 0, v_start_1909_);
lean_closure_set(v___f_1910_, 1, v_toPure_1905_);
lean_closure_set(v___f_1910_, 2, v_toBind_1906_);
lean_closure_set(v___f_1910_, 3, v___x_1907_);
v___x_1911_ = lean_apply_4(v_toBind_1906_, lean_box(0), lean_box(0), v___x_1908_, v___f_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_inst_1914_, lean_object* v_inst_1915_, lean_object* v_inst_1916_, lean_object* v___f_1917_, lean_object* v_cls_1918_, uint8_t v_collapsed_1919_, lean_object* v_tag_1920_, lean_object* v_opts_1921_, uint8_t v_clsEnabled_1922_, lean_object* v_msg_1923_, lean_object* v_toBind_1924_, lean_object* v_k_1925_, lean_object* v___f_1926_, lean_object* v___f_1927_, lean_object* v_inst_1928_, lean_object* v_toPure_1929_, lean_object* v_oldTraces_1930_){
_start:
{
lean_object* v_tryCatch_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v_tryCatch_1931_ = lean_ctor_get(v_inst_1912_, 1);
lean_inc(v_tryCatch_1931_);
v___x_1932_ = lean_box(v_collapsed_1919_);
v___x_1933_ = lean_box(v_clsEnabled_1922_);
lean_inc_ref(v_opts_1921_);
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_1934_, 0, v_inst_1913_);
lean_closure_set(v___f_1934_, 1, v_inst_1914_);
lean_closure_set(v___f_1934_, 2, v_inst_1915_);
lean_closure_set(v___f_1934_, 3, v_inst_1916_);
lean_closure_set(v___f_1934_, 4, v_inst_1912_);
lean_closure_set(v___f_1934_, 5, v___f_1917_);
lean_closure_set(v___f_1934_, 6, v_cls_1918_);
lean_closure_set(v___f_1934_, 7, v___x_1932_);
lean_closure_set(v___f_1934_, 8, v_tag_1920_);
lean_closure_set(v___f_1934_, 9, v_opts_1921_);
lean_closure_set(v___f_1934_, 10, v___x_1933_);
lean_closure_set(v___f_1934_, 11, v_oldTraces_1930_);
lean_closure_set(v___f_1934_, 12, v_msg_1923_);
lean_inc(v_toBind_1924_);
v___x_1935_ = lean_apply_4(v_toBind_1924_, lean_box(0), lean_box(0), v_k_1925_, v___f_1926_);
v___x_1936_ = lean_apply_3(v_tryCatch_1931_, lean_box(0), v___x_1935_, v___f_1927_);
v___x_1937_ = l_Lean_KVMap_instValueBool;
v___x_1938_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1939_ = l_Lean_Option_get___redArg(v___x_1937_, v_opts_1921_, v___x_1938_);
lean_dec_ref(v_opts_1921_);
v___x_1940_ = lean_unbox(v___x_1939_);
lean_dec(v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1941_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1942_ = lean_apply_2(v_inst_1928_, lean_box(0), v___x_1941_);
lean_inc(v___x_1942_);
lean_inc_n(v_toBind_1924_, 2);
v___f_1943_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1943_, 0, v_toPure_1929_);
lean_closure_set(v___f_1943_, 1, v_toBind_1924_);
lean_closure_set(v___f_1943_, 2, v___x_1942_);
lean_closure_set(v___f_1943_, 3, v___x_1936_);
v___x_1944_ = lean_apply_4(v_toBind_1924_, lean_box(0), lean_box(0), v___x_1942_, v___f_1943_);
v___x_1945_ = lean_apply_4(v_toBind_1924_, lean_box(0), lean_box(0), v___x_1944_, v___f_1934_);
return v___x_1945_;
}
else
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1946_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1947_ = lean_apply_2(v_inst_1928_, lean_box(0), v___x_1946_);
lean_inc(v___x_1947_);
lean_inc_n(v_toBind_1924_, 2);
v___f_1948_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__10), 5, 4);
lean_closure_set(v___f_1948_, 0, v_toPure_1929_);
lean_closure_set(v___f_1948_, 1, v_toBind_1924_);
lean_closure_set(v___f_1948_, 2, v___x_1947_);
lean_closure_set(v___f_1948_, 3, v___x_1936_);
v___x_1949_ = lean_apply_4(v_toBind_1924_, lean_box(0), lean_box(0), v___x_1947_, v___f_1948_);
v___x_1950_ = lean_apply_4(v_toBind_1924_, lean_box(0), lean_box(0), v___x_1949_, v___f_1934_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_1951_ = _args[0];
lean_object* v_inst_1952_ = _args[1];
lean_object* v_inst_1953_ = _args[2];
lean_object* v_inst_1954_ = _args[3];
lean_object* v_inst_1955_ = _args[4];
lean_object* v___f_1956_ = _args[5];
lean_object* v_cls_1957_ = _args[6];
lean_object* v_collapsed_1958_ = _args[7];
lean_object* v_tag_1959_ = _args[8];
lean_object* v_opts_1960_ = _args[9];
lean_object* v_clsEnabled_1961_ = _args[10];
lean_object* v_msg_1962_ = _args[11];
lean_object* v_toBind_1963_ = _args[12];
lean_object* v_k_1964_ = _args[13];
lean_object* v___f_1965_ = _args[14];
lean_object* v___f_1966_ = _args[15];
lean_object* v_inst_1967_ = _args[16];
lean_object* v_toPure_1968_ = _args[17];
lean_object* v_oldTraces_1969_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_1970_; uint8_t v_clsEnabled_boxed_1971_; lean_object* v_res_1972_; 
v_collapsed_boxed_1970_ = lean_unbox(v_collapsed_1958_);
v_clsEnabled_boxed_1971_ = lean_unbox(v_clsEnabled_1961_);
v_res_1972_ = l_Lean_withTraceNode_x27___redArg___lam__11(v_inst_1951_, v_inst_1952_, v_inst_1953_, v_inst_1954_, v_inst_1955_, v___f_1956_, v_cls_1957_, v_collapsed_boxed_1970_, v_tag_1959_, v_opts_1960_, v_clsEnabled_boxed_1971_, v_msg_1962_, v_toBind_1963_, v_k_1964_, v___f_1965_, v___f_1966_, v_inst_1967_, v_toPure_1968_, v_oldTraces_1969_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_inst_1977_, lean_object* v___f_1978_, lean_object* v_cls_1979_, uint8_t v_collapsed_1980_, lean_object* v_tag_1981_, lean_object* v_opts_1982_, lean_object* v_msg_1983_, lean_object* v_toBind_1984_, lean_object* v_k_1985_, lean_object* v___f_1986_, lean_object* v___f_1987_, lean_object* v_inst_1988_, lean_object* v_toPure_1989_, uint8_t v_clsEnabled_1990_){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___f_1993_; 
v___x_1991_ = lean_box(v_collapsed_1980_);
v___x_1992_ = lean_box(v_clsEnabled_1990_);
lean_inc(v_k_1985_);
lean_inc(v_toBind_1984_);
lean_inc_ref(v_opts_1982_);
lean_inc_ref(v_inst_1975_);
lean_inc_ref(v_inst_1974_);
v___f_1993_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__11___boxed), 19, 18);
lean_closure_set(v___f_1993_, 0, v_inst_1973_);
lean_closure_set(v___f_1993_, 1, v_inst_1974_);
lean_closure_set(v___f_1993_, 2, v_inst_1975_);
lean_closure_set(v___f_1993_, 3, v_inst_1976_);
lean_closure_set(v___f_1993_, 4, v_inst_1977_);
lean_closure_set(v___f_1993_, 5, v___f_1978_);
lean_closure_set(v___f_1993_, 6, v_cls_1979_);
lean_closure_set(v___f_1993_, 7, v___x_1991_);
lean_closure_set(v___f_1993_, 8, v_tag_1981_);
lean_closure_set(v___f_1993_, 9, v_opts_1982_);
lean_closure_set(v___f_1993_, 10, v___x_1992_);
lean_closure_set(v___f_1993_, 11, v_msg_1983_);
lean_closure_set(v___f_1993_, 12, v_toBind_1984_);
lean_closure_set(v___f_1993_, 13, v_k_1985_);
lean_closure_set(v___f_1993_, 14, v___f_1986_);
lean_closure_set(v___f_1993_, 15, v___f_1987_);
lean_closure_set(v___f_1993_, 16, v_inst_1988_);
lean_closure_set(v___f_1993_, 17, v_toPure_1989_);
if (v_clsEnabled_1990_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1997_ = l_Lean_KVMap_instValueBool;
v___x_1998_ = l_Lean_trace_profiler;
v___x_1999_ = l_Lean_Option_get___redArg(v___x_1997_, v_opts_1982_, v___x_1998_);
lean_dec_ref(v_opts_1982_);
v___x_2000_ = lean_unbox(v___x_1999_);
lean_dec(v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec_ref(v___f_1993_);
lean_dec(v_toBind_1984_);
lean_dec_ref(v_inst_1975_);
lean_dec_ref(v_inst_1974_);
return v_k_1985_;
}
else
{
lean_dec(v_k_1985_);
goto v___jp_1994_;
}
}
else
{
lean_dec(v_k_1985_);
lean_dec_ref(v_opts_1982_);
goto v___jp_1994_;
}
v___jp_1994_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1974_, v_inst_1975_);
v___x_1996_ = lean_apply_4(v_toBind_1984_, lean_box(0), lean_box(0), v___x_1995_, v___f_1993_);
return v___x_1996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_inst_2001_ = _args[0];
lean_object* v_inst_2002_ = _args[1];
lean_object* v_inst_2003_ = _args[2];
lean_object* v_inst_2004_ = _args[3];
lean_object* v_inst_2005_ = _args[4];
lean_object* v___f_2006_ = _args[5];
lean_object* v_cls_2007_ = _args[6];
lean_object* v_collapsed_2008_ = _args[7];
lean_object* v_tag_2009_ = _args[8];
lean_object* v_opts_2010_ = _args[9];
lean_object* v_msg_2011_ = _args[10];
lean_object* v_toBind_2012_ = _args[11];
lean_object* v_k_2013_ = _args[12];
lean_object* v___f_2014_ = _args[13];
lean_object* v___f_2015_ = _args[14];
lean_object* v_inst_2016_ = _args[15];
lean_object* v_toPure_2017_ = _args[16];
lean_object* v_clsEnabled_2018_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2019_; uint8_t v_clsEnabled_boxed_2020_; lean_object* v_res_2021_; 
v_collapsed_boxed_2019_ = lean_unbox(v_collapsed_2008_);
v_clsEnabled_boxed_2020_ = lean_unbox(v_clsEnabled_2018_);
v_res_2021_ = l_Lean_withTraceNode_x27___redArg___lam__12(v_inst_2001_, v_inst_2002_, v_inst_2003_, v_inst_2004_, v_inst_2005_, v___f_2006_, v_cls_2007_, v_collapsed_boxed_2019_, v_tag_2009_, v_opts_2010_, v_msg_2011_, v_toBind_2012_, v_k_2013_, v___f_2014_, v___f_2015_, v_inst_2016_, v_toPure_2017_, v_clsEnabled_boxed_2020_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object* v_k_2022_, lean_object* v_inst_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v___f_2028_, lean_object* v_cls_2029_, uint8_t v_collapsed_2030_, lean_object* v_tag_2031_, lean_object* v_msg_2032_, lean_object* v_toBind_2033_, lean_object* v___f_2034_, lean_object* v___f_2035_, lean_object* v_inst_2036_, lean_object* v_toPure_2037_, lean_object* v___f_2038_, lean_object* v_opts_2039_){
_start:
{
uint8_t v_hasTrace_2040_; 
v_hasTrace_2040_ = lean_ctor_get_uint8(v_opts_2039_, sizeof(void*)*1);
if (v_hasTrace_2040_ == 0)
{
lean_dec_ref(v_opts_2039_);
lean_dec(v___f_2038_);
lean_dec(v_toPure_2037_);
lean_dec(v_inst_2036_);
lean_dec(v___f_2035_);
lean_dec(v___f_2034_);
lean_dec(v_toBind_2033_);
lean_dec(v_msg_2032_);
lean_dec_ref(v_tag_2031_);
lean_dec(v_cls_2029_);
lean_dec_ref(v___f_2028_);
lean_dec(v_inst_2027_);
lean_dec_ref(v_inst_2026_);
lean_dec_ref(v_inst_2025_);
lean_dec_ref(v_inst_2024_);
lean_dec_ref(v_inst_2023_);
return v_k_2022_;
}
else
{
lean_object* v_getInheritedTraceOptions_2041_; lean_object* v___x_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_getInheritedTraceOptions_2041_ = lean_ctor_get(v_inst_2023_, 2);
lean_inc(v_getInheritedTraceOptions_2041_);
v___x_2042_ = lean_box(v_collapsed_2030_);
lean_inc_n(v_toBind_2033_, 2);
v___f_2043_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_2043_, 0, v_inst_2024_);
lean_closure_set(v___f_2043_, 1, v_inst_2025_);
lean_closure_set(v___f_2043_, 2, v_inst_2023_);
lean_closure_set(v___f_2043_, 3, v_inst_2026_);
lean_closure_set(v___f_2043_, 4, v_inst_2027_);
lean_closure_set(v___f_2043_, 5, v___f_2028_);
lean_closure_set(v___f_2043_, 6, v_cls_2029_);
lean_closure_set(v___f_2043_, 7, v___x_2042_);
lean_closure_set(v___f_2043_, 8, v_tag_2031_);
lean_closure_set(v___f_2043_, 9, v_opts_2039_);
lean_closure_set(v___f_2043_, 10, v_msg_2032_);
lean_closure_set(v___f_2043_, 11, v_toBind_2033_);
lean_closure_set(v___f_2043_, 12, v_k_2022_);
lean_closure_set(v___f_2043_, 13, v___f_2034_);
lean_closure_set(v___f_2043_, 14, v___f_2035_);
lean_closure_set(v___f_2043_, 15, v_inst_2036_);
lean_closure_set(v___f_2043_, 16, v_toPure_2037_);
v___x_2044_ = lean_apply_4(v_toBind_2033_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2041_, v___f_2038_);
v___x_2045_ = lean_apply_4(v_toBind_2033_, lean_box(0), lean_box(0), v___x_2044_, v___f_2043_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_k_2046_ = _args[0];
lean_object* v_inst_2047_ = _args[1];
lean_object* v_inst_2048_ = _args[2];
lean_object* v_inst_2049_ = _args[3];
lean_object* v_inst_2050_ = _args[4];
lean_object* v_inst_2051_ = _args[5];
lean_object* v___f_2052_ = _args[6];
lean_object* v_cls_2053_ = _args[7];
lean_object* v_collapsed_2054_ = _args[8];
lean_object* v_tag_2055_ = _args[9];
lean_object* v_msg_2056_ = _args[10];
lean_object* v_toBind_2057_ = _args[11];
lean_object* v___f_2058_ = _args[12];
lean_object* v___f_2059_ = _args[13];
lean_object* v_inst_2060_ = _args[14];
lean_object* v_toPure_2061_ = _args[15];
lean_object* v___f_2062_ = _args[16];
lean_object* v_opts_2063_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2064_; lean_object* v_res_2065_; 
v_collapsed_boxed_2064_ = lean_unbox(v_collapsed_2054_);
v_res_2065_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_k_2046_, v_inst_2047_, v_inst_2048_, v_inst_2049_, v_inst_2050_, v_inst_2051_, v___f_2052_, v_cls_2053_, v_collapsed_boxed_2064_, v_tag_2055_, v_msg_2056_, v_toBind_2057_, v___f_2058_, v___f_2059_, v_inst_2060_, v_toPure_2061_, v___f_2062_, v_opts_2063_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_cls_2074_, lean_object* v_k_2075_, uint8_t v_collapsed_2076_, lean_object* v_tag_2077_){
_start:
{
lean_object* v_toApplicative_2078_; lean_object* v_toFunctor_2079_; lean_object* v_toBind_2080_; lean_object* v_toPure_2081_; lean_object* v_map_2082_; lean_object* v___f_2083_; lean_object* v_msg_2084_; lean_object* v___f_2085_; lean_object* v___f_2086_; lean_object* v___f_2087_; lean_object* v___f_2088_; lean_object* v___x_2089_; lean_object* v___f_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_toApplicative_2078_ = lean_ctor_get(v_inst_2067_, 0);
v_toFunctor_2079_ = lean_ctor_get(v_toApplicative_2078_, 0);
v_toBind_2080_ = lean_ctor_get(v_inst_2067_, 1);
lean_inc_n(v_toBind_2080_, 3);
v_toPure_2081_ = lean_ctor_get(v_toApplicative_2078_, 1);
lean_inc_n(v_toPure_2081_, 5);
v_map_2082_ = lean_ctor_get(v_toFunctor_2079_, 0);
lean_inc(v_map_2082_);
v___f_2083_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2084_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2084_, 0, v_toPure_2081_);
lean_inc(v_inst_2071_);
lean_inc(v_cls_2074_);
v___f_2085_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2085_, 0, v_toPure_2081_);
lean_closure_set(v___f_2085_, 1, v_cls_2074_);
lean_closure_set(v___f_2085_, 2, v_toBind_2080_);
lean_closure_set(v___f_2085_, 3, v_inst_2071_);
v___f_2086_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2086_, 0, v_toPure_2081_);
v___f_2087_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2087_, 0, v_toPure_2081_);
v___f_2088_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2089_ = lean_box(v_collapsed_2076_);
v___f_2090_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2090_, 0, v_k_2075_);
lean_closure_set(v___f_2090_, 1, v_inst_2068_);
lean_closure_set(v___f_2090_, 2, v_inst_2072_);
lean_closure_set(v___f_2090_, 3, v_inst_2067_);
lean_closure_set(v___f_2090_, 4, v_inst_2069_);
lean_closure_set(v___f_2090_, 5, v_inst_2070_);
lean_closure_set(v___f_2090_, 6, v___f_2088_);
lean_closure_set(v___f_2090_, 7, v_cls_2074_);
lean_closure_set(v___f_2090_, 8, v___x_2089_);
lean_closure_set(v___f_2090_, 9, v_tag_2077_);
lean_closure_set(v___f_2090_, 10, v_msg_2084_);
lean_closure_set(v___f_2090_, 11, v_toBind_2080_);
lean_closure_set(v___f_2090_, 12, v___f_2087_);
lean_closure_set(v___f_2090_, 13, v___f_2086_);
lean_closure_set(v___f_2090_, 14, v_inst_2073_);
lean_closure_set(v___f_2090_, 15, v_toPure_2081_);
lean_closure_set(v___f_2090_, 16, v___f_2085_);
v___x_2091_ = lean_apply_4(v_toBind_2080_, lean_box(0), lean_box(0), v_inst_2071_, v___f_2090_);
v___x_2092_ = lean_apply_4(v_map_2082_, lean_box(0), lean_box(0), v___f_2083_, v___x_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_cls_2100_, lean_object* v_k_2101_, lean_object* v_collapsed_2102_, lean_object* v_tag_2103_){
_start:
{
uint8_t v_collapsed_boxed_2104_; lean_object* v_res_2105_; 
v_collapsed_boxed_2104_ = lean_unbox(v_collapsed_2102_);
v_res_2105_ = l_Lean_withTraceNode_x27___redArg(v_inst_2093_, v_inst_2094_, v_inst_2095_, v_inst_2096_, v_inst_2097_, v_inst_2098_, v_inst_2099_, v_cls_2100_, v_k_2101_, v_collapsed_boxed_2104_, v_tag_2103_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object* v_00_u03b1_2106_, lean_object* v_m_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_cls_2115_, lean_object* v_k_2116_, uint8_t v_collapsed_2117_, lean_object* v_tag_2118_){
_start:
{
lean_object* v_toApplicative_2119_; lean_object* v_toFunctor_2120_; lean_object* v_toBind_2121_; lean_object* v_toPure_2122_; lean_object* v_map_2123_; lean_object* v___f_2124_; lean_object* v_msg_2125_; lean_object* v___f_2126_; lean_object* v___f_2127_; lean_object* v___f_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___f_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_toApplicative_2119_ = lean_ctor_get(v_inst_2108_, 0);
v_toFunctor_2120_ = lean_ctor_get(v_toApplicative_2119_, 0);
v_toBind_2121_ = lean_ctor_get(v_inst_2108_, 1);
lean_inc_n(v_toBind_2121_, 3);
v_toPure_2122_ = lean_ctor_get(v_toApplicative_2119_, 1);
lean_inc_n(v_toPure_2122_, 5);
v_map_2123_ = lean_ctor_get(v_toFunctor_2120_, 0);
lean_inc(v_map_2123_);
v___f_2124_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2125_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2125_, 0, v_toPure_2122_);
lean_inc(v_inst_2112_);
lean_inc(v_cls_2115_);
v___f_2126_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2126_, 0, v_toPure_2122_);
lean_closure_set(v___f_2126_, 1, v_cls_2115_);
lean_closure_set(v___f_2126_, 2, v_toBind_2121_);
lean_closure_set(v___f_2126_, 3, v_inst_2112_);
v___f_2127_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2127_, 0, v_toPure_2122_);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2128_, 0, v_toPure_2122_);
v___f_2129_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2130_ = lean_box(v_collapsed_2117_);
v___f_2131_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2131_, 0, v_k_2116_);
lean_closure_set(v___f_2131_, 1, v_inst_2109_);
lean_closure_set(v___f_2131_, 2, v_inst_2113_);
lean_closure_set(v___f_2131_, 3, v_inst_2108_);
lean_closure_set(v___f_2131_, 4, v_inst_2110_);
lean_closure_set(v___f_2131_, 5, v_inst_2111_);
lean_closure_set(v___f_2131_, 6, v___f_2129_);
lean_closure_set(v___f_2131_, 7, v_cls_2115_);
lean_closure_set(v___f_2131_, 8, v___x_2130_);
lean_closure_set(v___f_2131_, 9, v_tag_2118_);
lean_closure_set(v___f_2131_, 10, v_msg_2125_);
lean_closure_set(v___f_2131_, 11, v_toBind_2121_);
lean_closure_set(v___f_2131_, 12, v___f_2128_);
lean_closure_set(v___f_2131_, 13, v___f_2127_);
lean_closure_set(v___f_2131_, 14, v_inst_2114_);
lean_closure_set(v___f_2131_, 15, v_toPure_2122_);
lean_closure_set(v___f_2131_, 16, v___f_2126_);
v___x_2132_ = lean_apply_4(v_toBind_2121_, lean_box(0), lean_box(0), v_inst_2112_, v___f_2131_);
v___x_2133_ = lean_apply_4(v_map_2123_, lean_box(0), lean_box(0), v___f_2124_, v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object* v_00_u03b1_2134_, lean_object* v_m_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_cls_2143_, lean_object* v_k_2144_, lean_object* v_collapsed_2145_, lean_object* v_tag_2146_){
_start:
{
uint8_t v_collapsed_boxed_2147_; lean_object* v_res_2148_; 
v_collapsed_boxed_2147_ = lean_unbox(v_collapsed_2145_);
v_res_2148_ = l_Lean_withTraceNode_x27(v_00_u03b1_2134_, v_m_2135_, v_inst_2136_, v_inst_2137_, v_inst_2138_, v_inst_2139_, v_inst_2140_, v_inst_2141_, v_inst_2142_, v_cls_2143_, v_k_2144_, v_collapsed_boxed_2147_, v_tag_2146_);
return v_res_2148_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__4(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__3));
v___x_2158_ = l_Lean_mkAtom(v___x_2157_);
return v___x_2158_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__5(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__4, &l_Lean_registerTraceClass___auto__1___closed__4_once, _init_l_Lean_registerTraceClass___auto__1___closed__4);
v___x_2160_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2161_ = lean_array_push(v___x_2160_, v___x_2159_);
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__6(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2162_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__5, &l_Lean_registerTraceClass___auto__1___closed__5_once, _init_l_Lean_registerTraceClass___auto__1___closed__5);
v___x_2163_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__2));
v___x_2164_ = lean_box(2);
v___x_2165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
lean_ctor_set(v___x_2165_, 1, v___x_2163_);
lean_ctor_set(v___x_2165_, 2, v___x_2162_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__7(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__6, &l_Lean_registerTraceClass___auto__1___closed__6_once, _init_l_Lean_registerTraceClass___auto__1___closed__6);
v___x_2167_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_2168_ = lean_array_push(v___x_2167_, v___x_2166_);
return v___x_2168_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2169_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__7, &l_Lean_registerTraceClass___auto__1___closed__7_once, _init_l_Lean_registerTraceClass___auto__1___closed__7);
v___x_2170_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_2171_ = lean_box(2);
v___x_2172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v___x_2170_);
lean_ctor_set(v___x_2172_, 2, v___x_2169_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__8, &l_Lean_registerTraceClass___auto__1___closed__8_once, _init_l_Lean_registerTraceClass___auto__1___closed__8);
v___x_2174_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2175_ = lean_array_push(v___x_2174_, v___x_2173_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2176_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__9, &l_Lean_registerTraceClass___auto__1___closed__9_once, _init_l_Lean_registerTraceClass___auto__1___closed__9);
v___x_2177_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2178_ = lean_box(2);
v___x_2179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v___x_2177_);
lean_ctor_set(v___x_2179_, 2, v___x_2176_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__11(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__10, &l_Lean_registerTraceClass___auto__1___closed__10_once, _init_l_Lean_registerTraceClass___auto__1___closed__10);
v___x_2181_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2182_ = lean_array_push(v___x_2181_, v___x_2180_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2183_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__11, &l_Lean_registerTraceClass___auto__1___closed__11_once, _init_l_Lean_registerTraceClass___auto__1___closed__11);
v___x_2184_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_2185_ = lean_box(2);
v___x_2186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v___x_2184_);
lean_ctor_set(v___x_2186_, 2, v___x_2183_);
return v___x_2186_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__12, &l_Lean_registerTraceClass___auto__1___closed__12_once, _init_l_Lean_registerTraceClass___auto__1___closed__12);
v___x_2188_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2189_ = lean_array_push(v___x_2188_, v___x_2187_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2190_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__13, &l_Lean_registerTraceClass___auto__1___closed__13_once, _init_l_Lean_registerTraceClass___auto__1___closed__13);
v___x_2191_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_2192_ = lean_box(2);
v___x_2193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set(v___x_2193_, 1, v___x_2191_);
lean_ctor_set(v___x_2193_, 2, v___x_2190_);
return v___x_2193_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1(void){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__14, &l_Lean_registerTraceClass___auto__1___closed__14_once, _init_l_Lean_registerTraceClass___auto__1___closed__14);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2195_, lean_object* v_x_2196_){
_start:
{
if (lean_obj_tag(v_x_2196_) == 0)
{
return v_x_2195_;
}
else
{
lean_object* v_key_2197_; lean_object* v_value_2198_; lean_object* v_tail_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2225_; 
v_key_2197_ = lean_ctor_get(v_x_2196_, 0);
v_value_2198_ = lean_ctor_get(v_x_2196_, 1);
v_tail_2199_ = lean_ctor_get(v_x_2196_, 2);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_x_2196_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2201_ = v_x_2196_;
v_isShared_2202_ = v_isSharedCheck_2225_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_tail_2199_);
lean_inc(v_value_2198_);
lean_inc(v_key_2197_);
lean_dec(v_x_2196_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2225_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; uint64_t v___y_2205_; 
v___x_2203_ = lean_array_get_size(v_x_2195_);
if (lean_obj_tag(v_key_2197_) == 0)
{
uint64_t v___x_2223_; 
v___x_2223_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2205_ = v___x_2223_;
goto v___jp_2204_;
}
else
{
uint64_t v_hash_2224_; 
v_hash_2224_ = lean_ctor_get_uint64(v_key_2197_, sizeof(void*)*2);
v___y_2205_ = v_hash_2224_;
goto v___jp_2204_;
}
v___jp_2204_:
{
uint64_t v___x_2206_; uint64_t v___x_2207_; uint64_t v_fold_2208_; uint64_t v___x_2209_; uint64_t v___x_2210_; uint64_t v___x_2211_; size_t v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2206_ = 32ULL;
v___x_2207_ = lean_uint64_shift_right(v___y_2205_, v___x_2206_);
v_fold_2208_ = lean_uint64_xor(v___y_2205_, v___x_2207_);
v___x_2209_ = 16ULL;
v___x_2210_ = lean_uint64_shift_right(v_fold_2208_, v___x_2209_);
v___x_2211_ = lean_uint64_xor(v_fold_2208_, v___x_2210_);
v___x_2212_ = lean_uint64_to_usize(v___x_2211_);
v___x_2213_ = lean_usize_of_nat(v___x_2203_);
v___x_2214_ = ((size_t)1ULL);
v___x_2215_ = lean_usize_sub(v___x_2213_, v___x_2214_);
v___x_2216_ = lean_usize_land(v___x_2212_, v___x_2215_);
v___x_2217_ = lean_array_uget_borrowed(v_x_2195_, v___x_2216_);
lean_inc(v___x_2217_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 2, v___x_2217_);
v___x_2219_ = v___x_2201_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_key_2197_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_value_2198_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_array_uset(v_x_2195_, v___x_2216_, v___x_2219_);
v_x_2195_ = v___x_2220_;
v_x_2196_ = v_tail_2199_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object* v_i_2226_, lean_object* v_source_2227_, lean_object* v_target_2228_){
_start:
{
lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2229_ = lean_array_get_size(v_source_2227_);
v___x_2230_ = lean_nat_dec_lt(v_i_2226_, v___x_2229_);
if (v___x_2230_ == 0)
{
lean_dec_ref(v_source_2227_);
lean_dec(v_i_2226_);
return v_target_2228_;
}
else
{
lean_object* v_es_2231_; lean_object* v___x_2232_; lean_object* v_source_2233_; lean_object* v_target_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v_es_2231_ = lean_array_fget(v_source_2227_, v_i_2226_);
v___x_2232_ = lean_box(0);
v_source_2233_ = lean_array_fset(v_source_2227_, v_i_2226_, v___x_2232_);
v_target_2234_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_2228_, v_es_2231_);
v___x_2235_ = lean_unsigned_to_nat(1u);
v___x_2236_ = lean_nat_add(v_i_2226_, v___x_2235_);
lean_dec(v_i_2226_);
v_i_2226_ = v___x_2236_;
v_source_2227_ = v_source_2233_;
v_target_2228_ = v_target_2234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object* v_data_2238_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v_nbuckets_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2239_ = lean_array_get_size(v_data_2238_);
v___x_2240_ = lean_unsigned_to_nat(2u);
v_nbuckets_2241_ = lean_nat_mul(v___x_2239_, v___x_2240_);
v___x_2242_ = lean_unsigned_to_nat(0u);
v___x_2243_ = lean_box(0);
v___x_2244_ = lean_mk_array(v_nbuckets_2241_, v___x_2243_);
v___x_2245_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_2242_, v_data_2238_, v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object* v_m_2246_, lean_object* v_a_2247_, lean_object* v_b_2248_){
_start:
{
lean_object* v_size_2249_; lean_object* v_buckets_2250_; lean_object* v___x_2251_; uint64_t v___y_2253_; 
v_size_2249_ = lean_ctor_get(v_m_2246_, 0);
v_buckets_2250_ = lean_ctor_get(v_m_2246_, 1);
v___x_2251_ = lean_array_get_size(v_buckets_2250_);
if (lean_obj_tag(v_a_2247_) == 0)
{
uint64_t v___x_2290_; 
v___x_2290_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2253_ = v___x_2290_;
goto v___jp_2252_;
}
else
{
uint64_t v_hash_2291_; 
v_hash_2291_ = lean_ctor_get_uint64(v_a_2247_, sizeof(void*)*2);
v___y_2253_ = v_hash_2291_;
goto v___jp_2252_;
}
v___jp_2252_:
{
uint64_t v___x_2254_; uint64_t v___x_2255_; uint64_t v_fold_2256_; uint64_t v___x_2257_; uint64_t v___x_2258_; uint64_t v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; size_t v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; lean_object* v_bkt_2265_; uint8_t v___x_2266_; 
v___x_2254_ = 32ULL;
v___x_2255_ = lean_uint64_shift_right(v___y_2253_, v___x_2254_);
v_fold_2256_ = lean_uint64_xor(v___y_2253_, v___x_2255_);
v___x_2257_ = 16ULL;
v___x_2258_ = lean_uint64_shift_right(v_fold_2256_, v___x_2257_);
v___x_2259_ = lean_uint64_xor(v_fold_2256_, v___x_2258_);
v___x_2260_ = lean_uint64_to_usize(v___x_2259_);
v___x_2261_ = lean_usize_of_nat(v___x_2251_);
v___x_2262_ = ((size_t)1ULL);
v___x_2263_ = lean_usize_sub(v___x_2261_, v___x_2262_);
v___x_2264_ = lean_usize_land(v___x_2260_, v___x_2263_);
v_bkt_2265_ = lean_array_uget_borrowed(v_buckets_2250_, v___x_2264_);
v___x_2266_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_2247_, v_bkt_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2287_; 
lean_inc_ref(v_buckets_2250_);
lean_inc(v_size_2249_);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_m_2246_);
if (v_isSharedCheck_2287_ == 0)
{
lean_object* v_unused_2288_; lean_object* v_unused_2289_; 
v_unused_2288_ = lean_ctor_get(v_m_2246_, 1);
lean_dec(v_unused_2288_);
v_unused_2289_ = lean_ctor_get(v_m_2246_, 0);
lean_dec(v_unused_2289_);
v___x_2268_ = v_m_2246_;
v_isShared_2269_ = v_isSharedCheck_2287_;
goto v_resetjp_2267_;
}
else
{
lean_dec(v_m_2246_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2287_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v_size_x27_2271_; lean_object* v___x_2272_; lean_object* v_buckets_x27_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2270_ = lean_unsigned_to_nat(1u);
v_size_x27_2271_ = lean_nat_add(v_size_2249_, v___x_2270_);
lean_dec(v_size_2249_);
lean_inc(v_bkt_2265_);
v___x_2272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2272_, 0, v_a_2247_);
lean_ctor_set(v___x_2272_, 1, v_b_2248_);
lean_ctor_set(v___x_2272_, 2, v_bkt_2265_);
v_buckets_x27_2273_ = lean_array_uset(v_buckets_2250_, v___x_2264_, v___x_2272_);
v___x_2274_ = lean_unsigned_to_nat(4u);
v___x_2275_ = lean_nat_mul(v_size_x27_2271_, v___x_2274_);
v___x_2276_ = lean_unsigned_to_nat(3u);
v___x_2277_ = lean_nat_div(v___x_2275_, v___x_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_array_get_size(v_buckets_x27_2273_);
v___x_2279_ = lean_nat_dec_le(v___x_2277_, v___x_2278_);
lean_dec(v___x_2277_);
if (v___x_2279_ == 0)
{
lean_object* v_val_2280_; lean_object* v___x_2282_; 
v_val_2280_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_2273_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v_val_2280_);
lean_ctor_set(v___x_2268_, 0, v_size_x27_2271_);
v___x_2282_ = v___x_2268_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_size_x27_2271_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_val_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
else
{
lean_object* v___x_2285_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v_buckets_x27_2273_);
lean_ctor_set(v___x_2268_, 0, v_size_x27_2271_);
v___x_2285_ = v___x_2268_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_size_x27_2271_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_buckets_x27_2273_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
else
{
lean_dec(v_b_2248_);
lean_dec(v_a_2247_);
return v_m_2246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object* v_traceClassName_2295_, uint8_t v_inherited_2296_, lean_object* v_ref_2297_){
_start:
{
lean_object* v___x_2299_; lean_object* v_optionName_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2299_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v_optionName_2300_ = l_Lean_Name_append(v___x_2299_, v_traceClassName_2295_);
v___x_2301_ = ((lean_object*)(l_Lean_registerTraceClass___closed__0));
v___x_2302_ = ((lean_object*)(l_Lean_registerTraceClass___closed__1));
v___x_2303_ = lean_box(0);
lean_inc_n(v_optionName_2300_, 2);
v___x_2304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2304_, 0, v_optionName_2300_);
lean_ctor_set(v___x_2304_, 1, v_ref_2297_);
lean_ctor_set(v___x_2304_, 2, v___x_2301_);
lean_ctor_set(v___x_2304_, 3, v___x_2302_);
lean_ctor_set(v___x_2304_, 4, v___x_2303_);
v___x_2305_ = lean_register_option(v_optionName_2300_, v___x_2304_);
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
if (v_inherited_2296_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
lean_dec(v_optionName_2300_);
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
v___x_2316_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2314_, v_optionName_2300_, v___x_2315_);
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
lean_dec(v_optionName_2300_);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_2356_ = l_String_toRawSubstring_x27(v___x_2355_);
return v___x_2356_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12));
v___x_2362_ = l_String_toRawSubstring_x27(v___x_2361_);
return v___x_2362_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18));
v___x_2369_ = l_String_toRawSubstring_x27(v___x_2368_);
return v___x_2369_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31(void){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Array_mkArray0(lean_box(0));
return v___x_2397_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40));
v___x_2424_ = l_String_toRawSubstring_x27(v___x_2423_);
return v___x_2424_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57));
v___x_2460_ = l_String_toRawSubstring_x27(v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object* v_id_2482_, lean_object* v_s_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v_msg_2582_; lean_object* v_quotContext_2583_; lean_object* v_currMacroScope_2584_; lean_object* v_ref_2585_; lean_object* v___y_2586_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
lean_inc(v_s_2483_);
v___x_2632_ = l_Lean_Syntax_getKind(v_s_2483_);
v___x_2633_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49));
v___x_2634_ = lean_name_eq(v___x_2632_, v___x_2633_);
lean_dec(v___x_2632_);
if (v___x_2634_ == 0)
{
lean_object* v_quotContext_2635_; lean_object* v_currMacroScope_2636_; lean_object* v_ref_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v_quotContext_2635_ = lean_ctor_get(v_a_2484_, 1);
v_currMacroScope_2636_ = lean_ctor_get(v_a_2484_, 2);
v_ref_2637_ = lean_ctor_get(v_a_2484_, 5);
v___x_2638_ = l_Lean_SourceInfo_fromRef(v_ref_2637_, v___x_2634_);
v___x_2639_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51));
v___x_2640_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52));
v___x_2641_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
lean_inc_n(v___x_2638_, 8);
v___x_2642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2638_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2644_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2645_ = lean_box(0);
lean_inc_n(v_currMacroScope_2636_, 3);
lean_inc_n(v_quotContext_2635_, 3);
v___x_2646_ = l_Lean_addMacroScope(v_quotContext_2635_, v___x_2645_, v_currMacroScope_2636_);
v___x_2647_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55));
v___x_2648_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2638_);
lean_ctor_set(v___x_2648_, 1, v___x_2644_);
lean_ctor_set(v___x_2648_, 2, v___x_2646_);
lean_ctor_set(v___x_2648_, 3, v___x_2647_);
v___x_2649_ = l_Lean_Syntax_node1(v___x_2638_, v___x_2643_, v___x_2648_);
v___x_2650_ = l_Lean_Syntax_node2(v___x_2638_, v___x_2640_, v___x_2642_, v___x_2649_);
v___x_2651_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56));
v___x_2652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2638_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2654_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58);
v___x_2655_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59));
v___x_2656_ = l_Lean_addMacroScope(v_quotContext_2635_, v___x_2655_, v_currMacroScope_2636_);
v___x_2657_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64));
v___x_2658_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2638_);
lean_ctor_set(v___x_2658_, 1, v___x_2654_);
lean_ctor_set(v___x_2658_, 2, v___x_2656_);
lean_ctor_set(v___x_2658_, 3, v___x_2657_);
v___x_2659_ = l_Lean_Syntax_node1(v___x_2638_, v___x_2653_, v___x_2658_);
v___x_2660_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2638_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = l_Lean_Syntax_node5(v___x_2638_, v___x_2639_, v___x_2650_, v_s_2483_, v___x_2652_, v___x_2659_, v___x_2661_);
v_msg_2582_ = v___x_2662_;
v_quotContext_2583_ = v_quotContext_2635_;
v_currMacroScope_2584_ = v_currMacroScope_2636_;
v_ref_2585_ = v_ref_2637_;
v___y_2586_ = v_a_2485_;
goto v___jp_2581_;
}
else
{
lean_object* v_quotContext_2663_; lean_object* v_currMacroScope_2664_; lean_object* v_ref_2665_; uint8_t v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_quotContext_2663_ = lean_ctor_get(v_a_2484_, 1);
v_currMacroScope_2664_ = lean_ctor_get(v_a_2484_, 2);
v_ref_2665_ = lean_ctor_get(v_a_2484_, 5);
v___x_2666_ = 0;
v___x_2667_ = l_Lean_SourceInfo_fromRef(v_ref_2665_, v___x_2666_);
v___x_2668_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66));
v___x_2669_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67));
lean_inc(v___x_2667_);
v___x_2670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2667_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = l_Lean_Syntax_node2(v___x_2667_, v___x_2668_, v___x_2670_, v_s_2483_);
lean_inc(v_currMacroScope_2664_);
lean_inc(v_quotContext_2663_);
v_msg_2582_ = v___x_2671_;
v_quotContext_2583_ = v_quotContext_2663_;
v_currMacroScope_2584_ = v_currMacroScope_2664_;
v_ref_2585_ = v_ref_2665_;
v___y_2586_ = v_a_2485_;
goto v___jp_2581_;
}
v___jp_2486_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_inc_n(v___y_2497_, 8);
lean_inc(v___y_2488_);
lean_inc_n(v___y_2492_, 29);
v___x_2511_ = l_Lean_Syntax_node5(v___y_2492_, v___y_2488_, v___y_2489_, v___y_2497_, v___y_2497_, v___y_2504_, v___y_2510_);
lean_inc(v___y_2493_);
v___x_2512_ = l_Lean_Syntax_node1(v___y_2492_, v___y_2493_, v___x_2511_);
lean_inc(v___y_2494_);
v___x_2513_ = l_Lean_Syntax_node4(v___y_2492_, v___y_2494_, v___y_2506_, v___y_2497_, v___y_2507_, v___x_2512_);
lean_inc_n(v___y_2508_, 3);
v___x_2514_ = l_Lean_Syntax_node2(v___y_2492_, v___y_2508_, v___x_2513_, v___y_2497_);
v___x_2515_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0));
lean_inc_ref_n(v___y_2495_, 7);
lean_inc_ref_n(v___y_2505_, 7);
lean_inc_ref_n(v___y_2496_, 10);
v___x_2516_ = l_Lean_Name_mkStr4(v___y_2496_, v___y_2505_, v___y_2495_, v___x_2515_);
v___x_2517_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1));
v___x_2518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___y_2492_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2));
v___x_2520_ = l_Lean_Name_mkStr4(v___y_2496_, v___y_2505_, v___y_2495_, v___x_2519_);
v___x_2521_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3));
v___x_2522_ = l_Lean_Name_mkStr4(v___y_2496_, v___y_2505_, v___y_2495_, v___x_2521_);
v___x_2523_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4));
v___x_2524_ = l_Lean_Name_mkStr4(v___y_2496_, v___y_2505_, v___y_2495_, v___x_2523_);
v___x_2525_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
v___x_2526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___y_2492_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2528_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2529_ = lean_box(0);
lean_inc_n(v___y_2502_, 2);
lean_inc_n(v___y_2490_, 2);
v___x_2530_ = l_Lean_addMacroScope(v___y_2490_, v___x_2529_, v___y_2502_);
v___x_2531_ = l_Lean_Name_mkStr1(v___y_2496_);
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_inc_n(v___y_2503_, 2);
v___x_2533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v___y_2503_);
v___x_2534_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2534_, 0, v___y_2492_);
lean_ctor_set(v___x_2534_, 1, v___x_2528_);
lean_ctor_set(v___x_2534_, 2, v___x_2530_);
lean_ctor_set(v___x_2534_, 3, v___x_2533_);
v___x_2535_ = l_Lean_Syntax_node1(v___y_2492_, v___x_2527_, v___x_2534_);
v___x_2536_ = l_Lean_Syntax_node2(v___y_2492_, v___x_2524_, v___x_2526_, v___x_2535_);
v___x_2537_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9));
v___x_2538_ = l_Lean_Name_mkStr4(v___y_2496_, v___y_2505_, v___y_2495_, v___x_2537_);
v___x_2539_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10));
v___x_2540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___y_2492_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11));
v___x_2542_ = l_Lean_Name_mkStr4(v___y_2496_, v___y_2505_, v___y_2495_, v___x_2541_);
v___x_2543_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13);
v___x_2544_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14));
v___x_2545_ = l_Lean_Name_mkStr2(v___y_2496_, v___x_2544_);
lean_inc(v___x_2545_);
v___x_2546_ = l_Lean_addMacroScope(v___y_2490_, v___x_2545_, v___y_2502_);
v___x_2547_ = lean_box(0);
v___x_2548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2545_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
lean_ctor_set(v___x_2549_, 1, v___y_2503_);
v___x_2550_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2550_, 0, v___y_2492_);
lean_ctor_set(v___x_2550_, 1, v___x_2543_);
lean_ctor_set(v___x_2550_, 2, v___x_2546_);
lean_ctor_set(v___x_2550_, 3, v___x_2549_);
lean_inc(v___y_2491_);
lean_inc_n(v___y_2487_, 4);
v___x_2551_ = l_Lean_Syntax_node1(v___y_2492_, v___y_2487_, v___y_2491_);
lean_inc(v___x_2542_);
v___x_2552_ = l_Lean_Syntax_node2(v___y_2492_, v___x_2542_, v___x_2550_, v___x_2551_);
v___x_2553_ = l_Lean_Syntax_node2(v___y_2492_, v___x_2538_, v___x_2540_, v___x_2552_);
v___x_2554_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___y_2492_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = l_Lean_Syntax_node3(v___y_2492_, v___x_2522_, v___x_2536_, v___x_2553_, v___x_2555_);
v___x_2557_ = l_Lean_Syntax_node2(v___y_2492_, v___x_2520_, v___y_2497_, v___x_2556_);
v___x_2558_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2559_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___y_2492_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17));
v___x_2561_ = l_Lean_Name_mkStr4(v___y_2496_, v___y_2505_, v___y_2495_, v___x_2560_);
v___x_2562_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19);
v___x_2563_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20));
v___x_2564_ = l_Lean_Name_mkStr2(v___y_2496_, v___x_2563_);
lean_inc(v___x_2564_);
v___x_2565_ = l_Lean_addMacroScope(v___y_2490_, v___x_2564_, v___y_2502_);
v___x_2566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set(v___x_2566_, 1, v___x_2547_);
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v___y_2503_);
v___x_2568_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2568_, 0, v___y_2492_);
lean_ctor_set(v___x_2568_, 1, v___x_2562_);
lean_ctor_set(v___x_2568_, 2, v___x_2565_);
lean_ctor_set(v___x_2568_, 3, v___x_2567_);
v___x_2569_ = l_Lean_Syntax_node2(v___y_2492_, v___y_2487_, v___y_2491_, v___y_2500_);
v___x_2570_ = l_Lean_Syntax_node2(v___y_2492_, v___x_2542_, v___x_2568_, v___x_2569_);
v___x_2571_ = l_Lean_Syntax_node1(v___y_2492_, v___x_2561_, v___x_2570_);
v___x_2572_ = l_Lean_Syntax_node2(v___y_2492_, v___y_2508_, v___x_2571_, v___y_2497_);
v___x_2573_ = l_Lean_Syntax_node1(v___y_2492_, v___y_2487_, v___x_2572_);
lean_inc_n(v___y_2499_, 2);
v___x_2574_ = l_Lean_Syntax_node1(v___y_2492_, v___y_2499_, v___x_2573_);
v___x_2575_ = l_Lean_Syntax_node6(v___y_2492_, v___x_2516_, v___x_2518_, v___x_2557_, v___x_2559_, v___x_2574_, v___y_2497_, v___y_2497_);
v___x_2576_ = l_Lean_Syntax_node2(v___y_2492_, v___y_2508_, v___x_2575_, v___y_2497_);
v___x_2577_ = l_Lean_Syntax_node2(v___y_2492_, v___y_2487_, v___x_2514_, v___x_2576_);
v___x_2578_ = l_Lean_Syntax_node1(v___y_2492_, v___y_2499_, v___x_2577_);
lean_inc(v___y_2509_);
v___x_2579_ = l_Lean_Syntax_node2(v___y_2492_, v___y_2509_, v___y_2501_, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___y_2498_);
return v___x_2580_;
}
v___jp_2581_:
{
uint8_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2587_ = 0;
v___x_2588_ = l_Lean_SourceInfo_fromRef(v_ref_2585_, v___x_2587_);
v___x_2589_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0));
v___x_2590_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1));
v___x_2591_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__0));
v___x_2592_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22));
v___x_2593_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23));
lean_inc_n(v___x_2588_, 7);
v___x_2594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2588_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25));
v___x_2596_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2597_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27));
v___x_2598_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2599_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
v___x_2600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2588_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31);
v___x_2602_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2588_);
lean_ctor_set(v___x_2602_, 1, v___x_2596_);
lean_ctor_set(v___x_2602_, 2, v___x_2601_);
v___x_2603_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33));
lean_inc_ref(v___x_2602_);
v___x_2604_ = l_Lean_Syntax_node1(v___x_2588_, v___x_2603_, v___x_2602_);
v___x_2605_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35));
v___x_2606_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37));
v___x_2607_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39));
v___x_2608_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41);
v___x_2609_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42));
lean_inc(v_currMacroScope_2584_);
lean_inc(v_quotContext_2583_);
v___x_2610_ = l_Lean_addMacroScope(v_quotContext_2583_, v___x_2609_, v_currMacroScope_2584_);
v___x_2611_ = lean_box(0);
v___x_2612_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2588_);
lean_ctor_set(v___x_2612_, 1, v___x_2608_);
lean_ctor_set(v___x_2612_, 2, v___x_2610_);
lean_ctor_set(v___x_2612_, 3, v___x_2611_);
lean_inc_ref(v___x_2612_);
v___x_2613_ = l_Lean_Syntax_node1(v___x_2588_, v___x_2607_, v___x_2612_);
v___x_2614_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43));
v___x_2615_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2588_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = l_Lean_Syntax_getId(v_id_2482_);
v___x_2617_ = lean_erase_macro_scopes(v___x_2616_);
lean_inc(v___x_2617_);
v___x_2618_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2611_, v___x_2617_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_quoteNameMk(v___x_2617_);
v___y_2487_ = v___x_2596_;
v___y_2488_ = v___x_2606_;
v___y_2489_ = v___x_2613_;
v___y_2490_ = v_quotContext_2583_;
v___y_2491_ = v___x_2612_;
v___y_2492_ = v___x_2588_;
v___y_2493_ = v___x_2605_;
v___y_2494_ = v___x_2598_;
v___y_2495_ = v___x_2591_;
v___y_2496_ = v___x_2589_;
v___y_2497_ = v___x_2602_;
v___y_2498_ = v___y_2586_;
v___y_2499_ = v___x_2595_;
v___y_2500_ = v_msg_2582_;
v___y_2501_ = v___x_2594_;
v___y_2502_ = v_currMacroScope_2584_;
v___y_2503_ = v___x_2611_;
v___y_2504_ = v___x_2615_;
v___y_2505_ = v___x_2590_;
v___y_2506_ = v___x_2600_;
v___y_2507_ = v___x_2604_;
v___y_2508_ = v___x_2597_;
v___y_2509_ = v___x_2592_;
v___y_2510_ = v___x_2619_;
goto v___jp_2486_;
}
else
{
lean_object* v_val_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec(v___x_2617_);
v_val_2620_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_val_2620_);
lean_dec_ref(v___x_2618_);
v___x_2621_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45));
v___x_2622_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46));
v___x_2623_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47));
v___x_2624_ = lean_string_intercalate(v___x_2623_, v_val_2620_);
v___x_2625_ = lean_string_append(v___x_2622_, v___x_2624_);
lean_dec_ref(v___x_2624_);
v___x_2626_ = lean_box(2);
v___x_2627_ = l_Lean_Syntax_mkNameLit(v___x_2625_, v___x_2626_);
v___x_2628_ = lean_unsigned_to_nat(1u);
v___x_2629_ = lean_mk_empty_array_with_capacity(v___x_2628_);
v___x_2630_ = lean_array_push(v___x_2629_, v___x_2627_);
v___x_2631_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2626_);
lean_ctor_set(v___x_2631_, 1, v___x_2621_);
lean_ctor_set(v___x_2631_, 2, v___x_2630_);
v___y_2487_ = v___x_2596_;
v___y_2488_ = v___x_2606_;
v___y_2489_ = v___x_2613_;
v___y_2490_ = v_quotContext_2583_;
v___y_2491_ = v___x_2612_;
v___y_2492_ = v___x_2588_;
v___y_2493_ = v___x_2605_;
v___y_2494_ = v___x_2598_;
v___y_2495_ = v___x_2591_;
v___y_2496_ = v___x_2589_;
v___y_2497_ = v___x_2602_;
v___y_2498_ = v___y_2586_;
v___y_2499_ = v___x_2595_;
v___y_2500_ = v_msg_2582_;
v___y_2501_ = v___x_2594_;
v___y_2502_ = v_currMacroScope_2584_;
v___y_2503_ = v___x_2611_;
v___y_2504_ = v___x_2615_;
v___y_2505_ = v___x_2590_;
v___y_2506_ = v___x_2600_;
v___y_2507_ = v___x_2604_;
v___y_2508_ = v___x_2597_;
v___y_2509_ = v___x_2592_;
v___y_2510_ = v___x_2631_;
goto v___jp_2486_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object* v_id_2672_, lean_object* v_s_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v_id_2672_, v_s_2673_, v_a_2674_, v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_id_2672_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object* v_x_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = ((lean_object*)(l_Lean_doElemTrace_x5b___x5d_____00__closed__1));
lean_inc(v_x_2731_);
v___x_2735_ = l_Lean_Syntax_isOfKind(v_x_2731_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec(v_x_2731_);
v___x_2736_ = lean_box(1);
v___x_2737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
lean_ctor_set(v___x_2737_, 1, v_a_2733_);
return v___x_2737_;
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v_a_2743_; lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
v___x_2738_ = lean_unsigned_to_nat(1u);
v___x_2739_ = l_Lean_Syntax_getArg(v_x_2731_, v___x_2738_);
v___x_2740_ = lean_unsigned_to_nat(3u);
v___x_2741_ = l_Lean_Syntax_getArg(v_x_2731_, v___x_2740_);
lean_dec(v_x_2731_);
v___x_2742_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v___x_2739_, v___x_2741_, v_a_2732_, v_a_2733_);
lean_dec(v___x_2739_);
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_a_2744_ = lean_ctor_get(v___x_2742_, 1);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2742_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2743_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object* v_x_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(v_x_2752_, v_a_2753_, v_a_2754_);
lean_dec_ref(v_a_2753_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object* v_inst_2756_, lean_object* v_inst_2757_, lean_object* v_inst_2758_, lean_object* v_inst_2759_, lean_object* v_always_2760_, lean_object* v_inst_2761_, lean_object* v_cls_2762_, uint8_t v_collapsed_2763_, lean_object* v_tag_2764_, lean_object* v_opts_2765_, uint8_t v_clsEnabled_2766_, lean_object* v_oldTraces_2767_, lean_object* v_ref_2768_, lean_object* v_msg_2769_, lean_object* v_resStartStop_2770_){
_start:
{
lean_object* v___x_2771_; lean_object* v_snd_2772_; lean_object* v_fst_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2839_; 
v___x_2771_ = l_Lean_KVMap_instValueBool;
v_snd_2772_ = lean_ctor_get(v_resStartStop_2770_, 1);
v_fst_2773_ = lean_ctor_get(v_resStartStop_2770_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_resStartStop_2770_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2775_ = v_resStartStop_2770_;
v_isShared_2776_ = v_isSharedCheck_2839_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_snd_2772_);
lean_inc(v_fst_2773_);
lean_dec(v_resStartStop_2770_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2839_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v_fst_2777_; lean_object* v_snd_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2838_; 
v_fst_2777_ = lean_ctor_get(v_snd_2772_, 0);
v_snd_2778_ = lean_ctor_get(v_snd_2772_, 1);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_snd_2772_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2780_ = v_snd_2772_;
v_isShared_2781_ = v_isSharedCheck_2838_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_snd_2778_);
lean_inc(v_fst_2777_);
lean_dec(v_snd_2772_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2838_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___f_2782_; lean_object* v___f_2783_; lean_object* v___y_2785_; lean_object* v_data_2786_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___y_2812_; double v___y_2818_; uint8_t v___x_2823_; 
lean_inc_ref(v_oldTraces_2767_);
v___f_2782_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2782_, 0, v_oldTraces_2767_);
lean_inc(v_fst_2773_);
lean_inc_ref(v_inst_2756_);
v___f_2783_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2783_, 0, v_always_2760_);
lean_closure_set(v___f_2783_, 1, v_inst_2756_);
lean_closure_set(v___f_2783_, 2, v_fst_2773_);
v___x_2790_ = l_Lean_trace_profiler;
v___x_2791_ = l_Lean_Option_get___redArg(v___x_2771_, v_opts_2765_, v___x_2790_);
v___x_2823_ = lean_unbox(v___x_2791_);
if (v___x_2823_ == 0)
{
uint8_t v___x_2824_; 
v___x_2824_ = lean_unbox(v___x_2791_);
v___y_2812_ = v___x_2824_;
goto v___jp_2811_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2825_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2826_ = l_Lean_Option_get___redArg(v___x_2771_, v_opts_2765_, v___x_2825_);
v___x_2827_ = lean_unbox(v___x_2826_);
lean_dec(v___x_2826_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; double v___x_2831_; double v___x_2832_; double v___x_2833_; 
v___x_2828_ = l_Lean_KVMap_instValueNat;
v___x_2829_ = l_Lean_trace_profiler_threshold;
v___x_2830_ = l_Lean_Option_get___redArg(v___x_2828_, v_opts_2765_, v___x_2829_);
v___x_2831_ = lean_float_of_nat(v___x_2830_);
v___x_2832_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_2833_ = lean_float_div(v___x_2831_, v___x_2832_);
v___y_2818_ = v___x_2833_;
goto v___jp_2817_;
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; double v___x_2837_; 
v___x_2834_ = l_Lean_KVMap_instValueNat;
v___x_2835_ = l_Lean_trace_profiler_threshold;
v___x_2836_ = l_Lean_Option_get___redArg(v___x_2834_, v_opts_2765_, v___x_2835_);
v___x_2837_ = lean_float_of_nat(v___x_2836_);
v___y_2818_ = v___x_2837_;
goto v___jp_2817_;
}
}
v___jp_2784_:
{
lean_object* v_toBind_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_toBind_2787_ = lean_ctor_get(v_inst_2756_, 1);
lean_inc(v_toBind_2787_);
v___x_2788_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_2756_, v_inst_2757_, v_inst_2758_, v_inst_2759_, v_oldTraces_2767_, v_data_2786_, v_ref_2768_, v___y_2785_);
v___x_2789_ = lean_apply_4(v_toBind_2787_, lean_box(0), lean_box(0), v___x_2788_, v___f_2783_);
return v___x_2789_;
}
v___jp_2792_:
{
lean_object* v_result_2793_; uint8_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
v_result_2793_ = lean_apply_1(v_inst_2761_, v_fst_2773_);
v___x_2794_ = lean_unbox(v_result_2793_);
v___x_2795_ = l_Lean_TraceResult_toEmoji(v___x_2794_);
v___x_2796_ = l_Lean_stringToMessageData(v___x_2795_);
v___x_2797_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___closed__1);
if (v_isShared_2781_ == 0)
{
lean_ctor_set_tag(v___x_2780_, 7);
lean_ctor_set(v___x_2780_, 1, v___x_2797_);
lean_ctor_set(v___x_2780_, 0, v___x_2796_);
v___x_2799_ = v___x_2780_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v_msg_2801_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set_tag(v___x_2775_, 7);
lean_ctor_set(v___x_2775_, 1, v_msg_2769_);
lean_ctor_set(v___x_2775_, 0, v___x_2799_);
v_msg_2801_ = v___x_2775_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_msg_2769_);
v_msg_2801_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; double v___x_2803_; lean_object* v_data_2804_; uint8_t v___x_2805_; 
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v_result_2793_);
v___x_2803_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_2764_);
lean_inc_ref(v___x_2802_);
lean_inc(v_cls_2762_);
v_data_2804_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2804_, 0, v_cls_2762_);
lean_ctor_set(v_data_2804_, 1, v___x_2802_);
lean_ctor_set(v_data_2804_, 2, v_tag_2764_);
lean_ctor_set_float(v_data_2804_, sizeof(void*)*3, v___x_2803_);
lean_ctor_set_float(v_data_2804_, sizeof(void*)*3 + 8, v___x_2803_);
lean_ctor_set_uint8(v_data_2804_, sizeof(void*)*3 + 16, v_collapsed_2763_);
v___x_2805_ = lean_unbox(v___x_2791_);
lean_dec(v___x_2791_);
if (v___x_2805_ == 0)
{
lean_dec_ref(v___x_2802_);
lean_dec(v_snd_2778_);
lean_dec(v_fst_2777_);
lean_dec_ref(v_tag_2764_);
lean_dec(v_cls_2762_);
v___y_2785_ = v_msg_2801_;
v_data_2786_ = v_data_2804_;
goto v___jp_2784_;
}
else
{
lean_object* v_data_2806_; double v___x_2807_; double v___x_2808_; 
lean_dec_ref(v_data_2804_);
v_data_2806_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2806_, 0, v_cls_2762_);
lean_ctor_set(v_data_2806_, 1, v___x_2802_);
lean_ctor_set(v_data_2806_, 2, v_tag_2764_);
v___x_2807_ = lean_unbox_float(v_fst_2777_);
lean_dec(v_fst_2777_);
lean_ctor_set_float(v_data_2806_, sizeof(void*)*3, v___x_2807_);
v___x_2808_ = lean_unbox_float(v_snd_2778_);
lean_dec(v_snd_2778_);
lean_ctor_set_float(v_data_2806_, sizeof(void*)*3 + 8, v___x_2808_);
lean_ctor_set_uint8(v_data_2806_, sizeof(void*)*3 + 16, v_collapsed_2763_);
v___y_2785_ = v_msg_2801_;
v_data_2786_ = v_data_2806_;
goto v___jp_2784_;
}
}
}
}
v___jp_2811_:
{
if (v_clsEnabled_2766_ == 0)
{
if (v___y_2812_ == 0)
{
lean_object* v_toBind_2813_; lean_object* v_modifyTraceState_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_dec(v___x_2791_);
lean_del_object(v___x_2780_);
lean_dec(v_snd_2778_);
lean_dec(v_fst_2777_);
lean_del_object(v___x_2775_);
lean_dec(v_fst_2773_);
lean_dec_ref(v_msg_2769_);
lean_dec(v_ref_2768_);
lean_dec_ref(v_oldTraces_2767_);
lean_dec_ref(v_tag_2764_);
lean_dec(v_cls_2762_);
lean_dec_ref(v_inst_2761_);
lean_dec(v_inst_2759_);
lean_dec_ref(v_inst_2758_);
v_toBind_2813_ = lean_ctor_get(v_inst_2756_, 1);
lean_inc(v_toBind_2813_);
lean_dec_ref(v_inst_2756_);
v_modifyTraceState_2814_ = lean_ctor_get(v_inst_2757_, 0);
lean_inc(v_modifyTraceState_2814_);
lean_dec_ref(v_inst_2757_);
v___x_2815_ = lean_apply_1(v_modifyTraceState_2814_, v___f_2782_);
v___x_2816_ = lean_apply_4(v_toBind_2813_, lean_box(0), lean_box(0), v___x_2815_, v___f_2783_);
return v___x_2816_;
}
else
{
lean_dec_ref(v___f_2782_);
goto v___jp_2792_;
}
}
else
{
lean_dec_ref(v___f_2782_);
goto v___jp_2792_;
}
}
v___jp_2817_:
{
double v___x_2819_; double v___x_2820_; double v___x_2821_; uint8_t v___x_2822_; 
v___x_2819_ = lean_unbox_float(v_snd_2778_);
v___x_2820_ = lean_unbox_float(v_fst_2777_);
v___x_2821_ = lean_float_sub(v___x_2819_, v___x_2820_);
v___x_2822_ = lean_float_decLt(v___y_2818_, v___x_2821_);
v___y_2812_ = v___x_2822_;
goto v___jp_2811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object* v_inst_2840_, lean_object* v_inst_2841_, lean_object* v_inst_2842_, lean_object* v_inst_2843_, lean_object* v_always_2844_, lean_object* v_inst_2845_, lean_object* v_cls_2846_, lean_object* v_collapsed_2847_, lean_object* v_tag_2848_, lean_object* v_opts_2849_, lean_object* v_clsEnabled_2850_, lean_object* v_oldTraces_2851_, lean_object* v_ref_2852_, lean_object* v_msg_2853_, lean_object* v_resStartStop_2854_){
_start:
{
uint8_t v_collapsed_boxed_2855_; uint8_t v_clsEnabled_boxed_2856_; lean_object* v_res_2857_; 
v_collapsed_boxed_2855_ = lean_unbox(v_collapsed_2847_);
v_clsEnabled_boxed_2856_ = lean_unbox(v_clsEnabled_2850_);
v_res_2857_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2840_, v_inst_2841_, v_inst_2842_, v_inst_2843_, v_always_2844_, v_inst_2845_, v_cls_2846_, v_collapsed_boxed_2855_, v_tag_2848_, v_opts_2849_, v_clsEnabled_boxed_2856_, v_oldTraces_2851_, v_ref_2852_, v_msg_2853_, v_resStartStop_2854_);
lean_dec_ref(v_opts_2849_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object* v_00_u03b1_2858_, lean_object* v_m_2859_, lean_object* v_inst_2860_, lean_object* v_inst_2861_, lean_object* v_00_u03b5_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_always_2865_, lean_object* v_inst_2866_, lean_object* v_cls_2867_, uint8_t v_collapsed_2868_, lean_object* v_tag_2869_, lean_object* v_opts_2870_, uint8_t v_clsEnabled_2871_, lean_object* v_oldTraces_2872_, lean_object* v_ref_2873_, lean_object* v_msg_2874_, lean_object* v_resStartStop_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2860_, v_inst_2861_, v_inst_2863_, v_inst_2864_, v_always_2865_, v_inst_2866_, v_cls_2867_, v_collapsed_2868_, v_tag_2869_, v_opts_2870_, v_clsEnabled_2871_, v_oldTraces_2872_, v_ref_2873_, v_msg_2874_, v_resStartStop_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_2877_ = _args[0];
lean_object* v_m_2878_ = _args[1];
lean_object* v_inst_2879_ = _args[2];
lean_object* v_inst_2880_ = _args[3];
lean_object* v_00_u03b5_2881_ = _args[4];
lean_object* v_inst_2882_ = _args[5];
lean_object* v_inst_2883_ = _args[6];
lean_object* v_always_2884_ = _args[7];
lean_object* v_inst_2885_ = _args[8];
lean_object* v_cls_2886_ = _args[9];
lean_object* v_collapsed_2887_ = _args[10];
lean_object* v_tag_2888_ = _args[11];
lean_object* v_opts_2889_ = _args[12];
lean_object* v_clsEnabled_2890_ = _args[13];
lean_object* v_oldTraces_2891_ = _args[14];
lean_object* v_ref_2892_ = _args[15];
lean_object* v_msg_2893_ = _args[16];
lean_object* v_resStartStop_2894_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2895_; uint8_t v_clsEnabled_boxed_2896_; lean_object* v_res_2897_; 
v_collapsed_boxed_2895_ = lean_unbox(v_collapsed_2887_);
v_clsEnabled_boxed_2896_ = lean_unbox(v_clsEnabled_2890_);
v_res_2897_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(v_00_u03b1_2877_, v_m_2878_, v_inst_2879_, v_inst_2880_, v_00_u03b5_2881_, v_inst_2882_, v_inst_2883_, v_always_2884_, v_inst_2885_, v_cls_2886_, v_collapsed_boxed_2895_, v_tag_2888_, v_opts_2889_, v_clsEnabled_boxed_2896_, v_oldTraces_2891_, v_ref_2892_, v_msg_2893_, v_resStartStop_2894_);
lean_dec_ref(v_opts_2889_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object* v_inst_2898_, lean_object* v_____do__lift_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_apply_1(v_inst_2898_, v_____do__lift_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object* v_inst_2901_, lean_object* v_inst_2902_, lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_always_2905_, lean_object* v_inst_2906_, lean_object* v_cls_2907_, uint8_t v_collapsed_2908_, lean_object* v_tag_2909_, lean_object* v_opts_2910_, uint8_t v_clsEnabled_2911_, lean_object* v_oldTraces_2912_, lean_object* v_ref_2913_, lean_object* v_msg_2914_, lean_object* v_resStartStop_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2901_, v_inst_2902_, v_inst_2903_, v_inst_2904_, v_always_2905_, v_inst_2906_, v_cls_2907_, v_collapsed_2908_, v_tag_2909_, v_opts_2910_, v_clsEnabled_2911_, v_oldTraces_2912_, v_ref_2913_, v_msg_2914_, v_resStartStop_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object* v_inst_2917_, lean_object* v_inst_2918_, lean_object* v_inst_2919_, lean_object* v_inst_2920_, lean_object* v_always_2921_, lean_object* v_inst_2922_, lean_object* v_cls_2923_, lean_object* v_collapsed_2924_, lean_object* v_tag_2925_, lean_object* v_opts_2926_, lean_object* v_clsEnabled_2927_, lean_object* v_oldTraces_2928_, lean_object* v_ref_2929_, lean_object* v_msg_2930_, lean_object* v_resStartStop_2931_){
_start:
{
uint8_t v_collapsed_boxed_2932_; uint8_t v_clsEnabled_boxed_2933_; lean_object* v_res_2934_; 
v_collapsed_boxed_2932_ = lean_unbox(v_collapsed_2924_);
v_clsEnabled_boxed_2933_ = lean_unbox(v_clsEnabled_2927_);
v_res_2934_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_2917_, v_inst_2918_, v_inst_2919_, v_inst_2920_, v_always_2921_, v_inst_2922_, v_cls_2923_, v_collapsed_boxed_2932_, v_tag_2925_, v_opts_2926_, v_clsEnabled_boxed_2933_, v_oldTraces_2928_, v_ref_2929_, v_msg_2930_, v_resStartStop_2931_);
lean_dec_ref(v_opts_2926_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object* v_always_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_inst_2938_, lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_cls_2941_, uint8_t v_collapsed_2942_, lean_object* v_tag_2943_, lean_object* v_opts_2944_, uint8_t v_clsEnabled_2945_, lean_object* v_oldTraces_2946_, lean_object* v_ref_2947_, lean_object* v_toPure_2948_, lean_object* v_toBind_2949_, lean_object* v_k_2950_, lean_object* v_inst_2951_, lean_object* v_msg_2952_){
_start:
{
lean_object* v_tryCatch_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___f_2956_; lean_object* v___f_2957_; lean_object* v___f_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v_tryCatch_2953_ = lean_ctor_get(v_always_2935_, 1);
lean_inc(v_tryCatch_2953_);
v___x_2954_ = lean_box(v_collapsed_2942_);
v___x_2955_ = lean_box(v_clsEnabled_2945_);
lean_inc_ref(v_opts_2944_);
v___f_2956_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__1___boxed), 15, 14);
lean_closure_set(v___f_2956_, 0, v_inst_2936_);
lean_closure_set(v___f_2956_, 1, v_inst_2937_);
lean_closure_set(v___f_2956_, 2, v_inst_2938_);
lean_closure_set(v___f_2956_, 3, v_inst_2939_);
lean_closure_set(v___f_2956_, 4, v_always_2935_);
lean_closure_set(v___f_2956_, 5, v_inst_2940_);
lean_closure_set(v___f_2956_, 6, v_cls_2941_);
lean_closure_set(v___f_2956_, 7, v___x_2954_);
lean_closure_set(v___f_2956_, 8, v_tag_2943_);
lean_closure_set(v___f_2956_, 9, v_opts_2944_);
lean_closure_set(v___f_2956_, 10, v___x_2955_);
lean_closure_set(v___f_2956_, 11, v_oldTraces_2946_);
lean_closure_set(v___f_2956_, 12, v_ref_2947_);
lean_closure_set(v___f_2956_, 13, v_msg_2952_);
lean_inc_n(v_toPure_2948_, 2);
v___f_2957_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2957_, 0, v_toPure_2948_);
v___f_2958_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2958_, 0, v_toPure_2948_);
lean_inc(v_toBind_2949_);
v___x_2959_ = lean_apply_4(v_toBind_2949_, lean_box(0), lean_box(0), v_k_2950_, v___f_2958_);
v___x_2960_ = lean_apply_3(v_tryCatch_2953_, lean_box(0), v___x_2959_, v___f_2957_);
v___x_2961_ = l_Lean_KVMap_instValueBool;
v___x_2962_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2963_ = l_Lean_Option_get___redArg(v___x_2961_, v_opts_2944_, v___x_2962_);
lean_dec_ref(v_opts_2944_);
v___x_2964_ = lean_unbox(v___x_2963_);
lean_dec(v___x_2963_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___f_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2965_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_2966_ = lean_apply_2(v_inst_2951_, lean_box(0), v___x_2965_);
lean_inc(v___x_2966_);
lean_inc_n(v_toBind_2949_, 2);
v___f_2967_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_2967_, 0, v_toPure_2948_);
lean_closure_set(v___f_2967_, 1, v_toBind_2949_);
lean_closure_set(v___f_2967_, 2, v___x_2966_);
lean_closure_set(v___f_2967_, 3, v___x_2960_);
v___x_2968_ = lean_apply_4(v_toBind_2949_, lean_box(0), lean_box(0), v___x_2966_, v___f_2967_);
v___x_2969_ = lean_apply_4(v_toBind_2949_, lean_box(0), lean_box(0), v___x_2968_, v___f_2956_);
return v___x_2969_;
}
else
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___f_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2970_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_2971_ = lean_apply_2(v_inst_2951_, lean_box(0), v___x_2970_);
lean_inc(v___x_2971_);
lean_inc_n(v_toBind_2949_, 2);
v___f_2972_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_2972_, 0, v_toPure_2948_);
lean_closure_set(v___f_2972_, 1, v_toBind_2949_);
lean_closure_set(v___f_2972_, 2, v___x_2971_);
lean_closure_set(v___f_2972_, 3, v___x_2960_);
v___x_2973_ = lean_apply_4(v_toBind_2949_, lean_box(0), lean_box(0), v___x_2971_, v___f_2972_);
v___x_2974_ = lean_apply_4(v_toBind_2949_, lean_box(0), lean_box(0), v___x_2973_, v___f_2956_);
return v___x_2974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_2975_ = _args[0];
lean_object* v_inst_2976_ = _args[1];
lean_object* v_inst_2977_ = _args[2];
lean_object* v_inst_2978_ = _args[3];
lean_object* v_inst_2979_ = _args[4];
lean_object* v_inst_2980_ = _args[5];
lean_object* v_cls_2981_ = _args[6];
lean_object* v_collapsed_2982_ = _args[7];
lean_object* v_tag_2983_ = _args[8];
lean_object* v_opts_2984_ = _args[9];
lean_object* v_clsEnabled_2985_ = _args[10];
lean_object* v_oldTraces_2986_ = _args[11];
lean_object* v_ref_2987_ = _args[12];
lean_object* v_toPure_2988_ = _args[13];
lean_object* v_toBind_2989_ = _args[14];
lean_object* v_k_2990_ = _args[15];
lean_object* v_inst_2991_ = _args[16];
lean_object* v_msg_2992_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2993_; uint8_t v_clsEnabled_boxed_2994_; lean_object* v_res_2995_; 
v_collapsed_boxed_2993_ = lean_unbox(v_collapsed_2982_);
v_clsEnabled_boxed_2994_ = lean_unbox(v_clsEnabled_2985_);
v_res_2995_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_always_2975_, v_inst_2976_, v_inst_2977_, v_inst_2978_, v_inst_2979_, v_inst_2980_, v_cls_2981_, v_collapsed_boxed_2993_, v_tag_2983_, v_opts_2984_, v_clsEnabled_boxed_2994_, v_oldTraces_2986_, v_ref_2987_, v_toPure_2988_, v_toBind_2989_, v_k_2990_, v_inst_2991_, v_msg_2992_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object* v_always_2996_, lean_object* v_inst_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_inst_3001_, lean_object* v_cls_3002_, uint8_t v_collapsed_3003_, lean_object* v_tag_3004_, lean_object* v_opts_3005_, uint8_t v_clsEnabled_3006_, lean_object* v_oldTraces_3007_, lean_object* v_toPure_3008_, lean_object* v_toBind_3009_, lean_object* v_k_3010_, lean_object* v_inst_3011_, lean_object* v_msg_3012_, lean_object* v___f_3013_, lean_object* v_withRef_3014_, lean_object* v_getRef_3015_, lean_object* v_ref_3016_){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___f_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3017_ = lean_box(v_collapsed_3003_);
v___x_3018_ = lean_box(v_clsEnabled_3006_);
lean_inc_n(v_toBind_3009_, 3);
lean_inc(v_ref_3016_);
v___f_3019_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__10___boxed), 18, 17);
lean_closure_set(v___f_3019_, 0, v_always_2996_);
lean_closure_set(v___f_3019_, 1, v_inst_2997_);
lean_closure_set(v___f_3019_, 2, v_inst_2998_);
lean_closure_set(v___f_3019_, 3, v_inst_2999_);
lean_closure_set(v___f_3019_, 4, v_inst_3000_);
lean_closure_set(v___f_3019_, 5, v_inst_3001_);
lean_closure_set(v___f_3019_, 6, v_cls_3002_);
lean_closure_set(v___f_3019_, 7, v___x_3017_);
lean_closure_set(v___f_3019_, 8, v_tag_3004_);
lean_closure_set(v___f_3019_, 9, v_opts_3005_);
lean_closure_set(v___f_3019_, 10, v___x_3018_);
lean_closure_set(v___f_3019_, 11, v_oldTraces_3007_);
lean_closure_set(v___f_3019_, 12, v_ref_3016_);
lean_closure_set(v___f_3019_, 13, v_toPure_3008_);
lean_closure_set(v___f_3019_, 14, v_toBind_3009_);
lean_closure_set(v___f_3019_, 15, v_k_3010_);
lean_closure_set(v___f_3019_, 16, v_inst_3011_);
v___x_3020_ = lean_box(0);
v___x_3021_ = lean_apply_1(v_msg_3012_, v___x_3020_);
v___x_3022_ = lean_apply_4(v_toBind_3009_, lean_box(0), lean_box(0), v___x_3021_, v___f_3013_);
v___f_3023_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3023_, 0, v_ref_3016_);
lean_closure_set(v___f_3023_, 1, v_withRef_3014_);
lean_closure_set(v___f_3023_, 2, v___x_3022_);
v___x_3024_ = lean_apply_4(v_toBind_3009_, lean_box(0), lean_box(0), v_getRef_3015_, v___f_3023_);
v___x_3025_ = lean_apply_4(v_toBind_3009_, lean_box(0), lean_box(0), v___x_3024_, v___f_3019_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_3026_ = _args[0];
lean_object* v_inst_3027_ = _args[1];
lean_object* v_inst_3028_ = _args[2];
lean_object* v_inst_3029_ = _args[3];
lean_object* v_inst_3030_ = _args[4];
lean_object* v_inst_3031_ = _args[5];
lean_object* v_cls_3032_ = _args[6];
lean_object* v_collapsed_3033_ = _args[7];
lean_object* v_tag_3034_ = _args[8];
lean_object* v_opts_3035_ = _args[9];
lean_object* v_clsEnabled_3036_ = _args[10];
lean_object* v_oldTraces_3037_ = _args[11];
lean_object* v_toPure_3038_ = _args[12];
lean_object* v_toBind_3039_ = _args[13];
lean_object* v_k_3040_ = _args[14];
lean_object* v_inst_3041_ = _args[15];
lean_object* v_msg_3042_ = _args[16];
lean_object* v___f_3043_ = _args[17];
lean_object* v_withRef_3044_ = _args[18];
lean_object* v_getRef_3045_ = _args[19];
lean_object* v_ref_3046_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_3047_; uint8_t v_clsEnabled_boxed_3048_; lean_object* v_res_3049_; 
v_collapsed_boxed_3047_ = lean_unbox(v_collapsed_3033_);
v_clsEnabled_boxed_3048_ = lean_unbox(v_clsEnabled_3036_);
v_res_3049_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_always_3026_, v_inst_3027_, v_inst_3028_, v_inst_3029_, v_inst_3030_, v_inst_3031_, v_cls_3032_, v_collapsed_boxed_3047_, v_tag_3034_, v_opts_3035_, v_clsEnabled_boxed_3048_, v_oldTraces_3037_, v_toPure_3038_, v_toBind_3039_, v_k_3040_, v_inst_3041_, v_msg_3042_, v___f_3043_, v_withRef_3044_, v_getRef_3045_, v_ref_3046_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object* v_inst_3050_, lean_object* v_always_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_inst_3055_, lean_object* v_cls_3056_, uint8_t v_collapsed_3057_, lean_object* v_tag_3058_, lean_object* v_opts_3059_, uint8_t v_clsEnabled_3060_, lean_object* v_toPure_3061_, lean_object* v_toBind_3062_, lean_object* v_k_3063_, lean_object* v_inst_3064_, lean_object* v_msg_3065_, lean_object* v___f_3066_, lean_object* v_oldTraces_3067_){
_start:
{
lean_object* v_getRef_3068_; lean_object* v_withRef_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___f_3072_; lean_object* v___x_3073_; 
v_getRef_3068_ = lean_ctor_get(v_inst_3050_, 0);
lean_inc_n(v_getRef_3068_, 2);
v_withRef_3069_ = lean_ctor_get(v_inst_3050_, 1);
lean_inc(v_withRef_3069_);
v___x_3070_ = lean_box(v_collapsed_3057_);
v___x_3071_ = lean_box(v_clsEnabled_3060_);
lean_inc(v_toBind_3062_);
v___f_3072_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__3___boxed), 21, 20);
lean_closure_set(v___f_3072_, 0, v_always_3051_);
lean_closure_set(v___f_3072_, 1, v_inst_3052_);
lean_closure_set(v___f_3072_, 2, v_inst_3053_);
lean_closure_set(v___f_3072_, 3, v_inst_3050_);
lean_closure_set(v___f_3072_, 4, v_inst_3054_);
lean_closure_set(v___f_3072_, 5, v_inst_3055_);
lean_closure_set(v___f_3072_, 6, v_cls_3056_);
lean_closure_set(v___f_3072_, 7, v___x_3070_);
lean_closure_set(v___f_3072_, 8, v_tag_3058_);
lean_closure_set(v___f_3072_, 9, v_opts_3059_);
lean_closure_set(v___f_3072_, 10, v___x_3071_);
lean_closure_set(v___f_3072_, 11, v_oldTraces_3067_);
lean_closure_set(v___f_3072_, 12, v_toPure_3061_);
lean_closure_set(v___f_3072_, 13, v_toBind_3062_);
lean_closure_set(v___f_3072_, 14, v_k_3063_);
lean_closure_set(v___f_3072_, 15, v_inst_3064_);
lean_closure_set(v___f_3072_, 16, v_msg_3065_);
lean_closure_set(v___f_3072_, 17, v___f_3066_);
lean_closure_set(v___f_3072_, 18, v_withRef_3069_);
lean_closure_set(v___f_3072_, 19, v_getRef_3068_);
v___x_3073_ = lean_apply_4(v_toBind_3062_, lean_box(0), lean_box(0), v_getRef_3068_, v___f_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_3074_ = _args[0];
lean_object* v_always_3075_ = _args[1];
lean_object* v_inst_3076_ = _args[2];
lean_object* v_inst_3077_ = _args[3];
lean_object* v_inst_3078_ = _args[4];
lean_object* v_inst_3079_ = _args[5];
lean_object* v_cls_3080_ = _args[6];
lean_object* v_collapsed_3081_ = _args[7];
lean_object* v_tag_3082_ = _args[8];
lean_object* v_opts_3083_ = _args[9];
lean_object* v_clsEnabled_3084_ = _args[10];
lean_object* v_toPure_3085_ = _args[11];
lean_object* v_toBind_3086_ = _args[12];
lean_object* v_k_3087_ = _args[13];
lean_object* v_inst_3088_ = _args[14];
lean_object* v_msg_3089_ = _args[15];
lean_object* v___f_3090_ = _args[16];
lean_object* v_oldTraces_3091_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3092_; uint8_t v_clsEnabled_boxed_3093_; lean_object* v_res_3094_; 
v_collapsed_boxed_3092_ = lean_unbox(v_collapsed_3081_);
v_clsEnabled_boxed_3093_ = lean_unbox(v_clsEnabled_3084_);
v_res_3094_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3074_, v_always_3075_, v_inst_3076_, v_inst_3077_, v_inst_3078_, v_inst_3079_, v_cls_3080_, v_collapsed_boxed_3092_, v_tag_3082_, v_opts_3083_, v_clsEnabled_boxed_3093_, v_toPure_3085_, v_toBind_3086_, v_k_3087_, v_inst_3088_, v_msg_3089_, v___f_3090_, v_oldTraces_3091_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object* v_inst_3095_, lean_object* v_always_3096_, lean_object* v_inst_3097_, lean_object* v_inst_3098_, lean_object* v_inst_3099_, lean_object* v_inst_3100_, lean_object* v_cls_3101_, uint8_t v_collapsed_3102_, lean_object* v_tag_3103_, lean_object* v_opts_3104_, lean_object* v_toPure_3105_, lean_object* v_toBind_3106_, lean_object* v_k_3107_, lean_object* v_inst_3108_, lean_object* v_msg_3109_, lean_object* v___f_3110_, uint8_t v_clsEnabled_3111_){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___f_3114_; 
v___x_3112_ = lean_box(v_collapsed_3102_);
v___x_3113_ = lean_box(v_clsEnabled_3111_);
lean_inc(v_k_3107_);
lean_inc(v_toBind_3106_);
lean_inc_ref(v_opts_3104_);
lean_inc_ref(v_inst_3098_);
lean_inc_ref(v_inst_3097_);
v___f_3114_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__2___boxed), 18, 17);
lean_closure_set(v___f_3114_, 0, v_inst_3095_);
lean_closure_set(v___f_3114_, 1, v_always_3096_);
lean_closure_set(v___f_3114_, 2, v_inst_3097_);
lean_closure_set(v___f_3114_, 3, v_inst_3098_);
lean_closure_set(v___f_3114_, 4, v_inst_3099_);
lean_closure_set(v___f_3114_, 5, v_inst_3100_);
lean_closure_set(v___f_3114_, 6, v_cls_3101_);
lean_closure_set(v___f_3114_, 7, v___x_3112_);
lean_closure_set(v___f_3114_, 8, v_tag_3103_);
lean_closure_set(v___f_3114_, 9, v_opts_3104_);
lean_closure_set(v___f_3114_, 10, v___x_3113_);
lean_closure_set(v___f_3114_, 11, v_toPure_3105_);
lean_closure_set(v___f_3114_, 12, v_toBind_3106_);
lean_closure_set(v___f_3114_, 13, v_k_3107_);
lean_closure_set(v___f_3114_, 14, v_inst_3108_);
lean_closure_set(v___f_3114_, 15, v_msg_3109_);
lean_closure_set(v___f_3114_, 16, v___f_3110_);
if (v_clsEnabled_3111_ == 0)
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3118_ = l_Lean_KVMap_instValueBool;
v___x_3119_ = l_Lean_trace_profiler;
v___x_3120_ = l_Lean_Option_get___redArg(v___x_3118_, v_opts_3104_, v___x_3119_);
lean_dec_ref(v_opts_3104_);
v___x_3121_ = lean_unbox(v___x_3120_);
lean_dec(v___x_3120_);
if (v___x_3121_ == 0)
{
lean_dec_ref(v___f_3114_);
lean_dec(v_toBind_3106_);
lean_dec_ref(v_inst_3098_);
lean_dec_ref(v_inst_3097_);
return v_k_3107_;
}
else
{
lean_dec(v_k_3107_);
goto v___jp_3115_;
}
}
else
{
lean_dec(v_k_3107_);
lean_dec_ref(v_opts_3104_);
goto v___jp_3115_;
}
v___jp_3115_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3097_, v_inst_3098_);
v___x_3117_ = lean_apply_4(v_toBind_3106_, lean_box(0), lean_box(0), v___x_3116_, v___f_3114_);
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_3122_ = _args[0];
lean_object* v_always_3123_ = _args[1];
lean_object* v_inst_3124_ = _args[2];
lean_object* v_inst_3125_ = _args[3];
lean_object* v_inst_3126_ = _args[4];
lean_object* v_inst_3127_ = _args[5];
lean_object* v_cls_3128_ = _args[6];
lean_object* v_collapsed_3129_ = _args[7];
lean_object* v_tag_3130_ = _args[8];
lean_object* v_opts_3131_ = _args[9];
lean_object* v_toPure_3132_ = _args[10];
lean_object* v_toBind_3133_ = _args[11];
lean_object* v_k_3134_ = _args[12];
lean_object* v_inst_3135_ = _args[13];
lean_object* v_msg_3136_ = _args[14];
lean_object* v___f_3137_ = _args[15];
lean_object* v_clsEnabled_3138_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3139_; uint8_t v_clsEnabled_boxed_3140_; lean_object* v_res_3141_; 
v_collapsed_boxed_3139_ = lean_unbox(v_collapsed_3129_);
v_clsEnabled_boxed_3140_ = lean_unbox(v_clsEnabled_3138_);
v_res_3141_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3122_, v_always_3123_, v_inst_3124_, v_inst_3125_, v_inst_3126_, v_inst_3127_, v_cls_3128_, v_collapsed_boxed_3139_, v_tag_3130_, v_opts_3131_, v_toPure_3132_, v_toBind_3133_, v_k_3134_, v_inst_3135_, v_msg_3136_, v___f_3137_, v_clsEnabled_boxed_3140_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object* v_k_3142_, lean_object* v_inst_3143_, lean_object* v_toApplicative_3144_, lean_object* v_inst_3145_, lean_object* v_always_3146_, lean_object* v_inst_3147_, lean_object* v_inst_3148_, lean_object* v_inst_3149_, lean_object* v_cls_3150_, uint8_t v_collapsed_3151_, lean_object* v_tag_3152_, lean_object* v_toBind_3153_, lean_object* v_inst_3154_, lean_object* v_msg_3155_, lean_object* v___f_3156_, lean_object* v_inst_3157_, lean_object* v_opts_3158_){
_start:
{
uint8_t v_hasTrace_3159_; 
v_hasTrace_3159_ = lean_ctor_get_uint8(v_opts_3158_, sizeof(void*)*1);
if (v_hasTrace_3159_ == 0)
{
lean_dec_ref(v_opts_3158_);
lean_dec(v_inst_3157_);
lean_dec(v___f_3156_);
lean_dec(v_msg_3155_);
lean_dec(v_inst_3154_);
lean_dec(v_toBind_3153_);
lean_dec_ref(v_tag_3152_);
lean_dec(v_cls_3150_);
lean_dec_ref(v_inst_3149_);
lean_dec(v_inst_3148_);
lean_dec_ref(v_inst_3147_);
lean_dec_ref(v_always_3146_);
lean_dec_ref(v_inst_3145_);
lean_dec_ref(v_toApplicative_3144_);
lean_dec_ref(v_inst_3143_);
return v_k_3142_;
}
else
{
lean_object* v_getInheritedTraceOptions_3160_; lean_object* v_toPure_3161_; lean_object* v___x_3162_; lean_object* v___f_3163_; lean_object* v___f_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v_getInheritedTraceOptions_3160_ = lean_ctor_get(v_inst_3143_, 2);
lean_inc(v_getInheritedTraceOptions_3160_);
v_toPure_3161_ = lean_ctor_get(v_toApplicative_3144_, 1);
lean_inc_n(v_toPure_3161_, 2);
lean_dec_ref(v_toApplicative_3144_);
v___x_3162_ = lean_box(v_collapsed_3151_);
lean_inc_n(v_toBind_3153_, 3);
lean_inc(v_cls_3150_);
v___f_3163_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_3163_, 0, v_inst_3145_);
lean_closure_set(v___f_3163_, 1, v_always_3146_);
lean_closure_set(v___f_3163_, 2, v_inst_3147_);
lean_closure_set(v___f_3163_, 3, v_inst_3143_);
lean_closure_set(v___f_3163_, 4, v_inst_3148_);
lean_closure_set(v___f_3163_, 5, v_inst_3149_);
lean_closure_set(v___f_3163_, 6, v_cls_3150_);
lean_closure_set(v___f_3163_, 7, v___x_3162_);
lean_closure_set(v___f_3163_, 8, v_tag_3152_);
lean_closure_set(v___f_3163_, 9, v_opts_3158_);
lean_closure_set(v___f_3163_, 10, v_toPure_3161_);
lean_closure_set(v___f_3163_, 11, v_toBind_3153_);
lean_closure_set(v___f_3163_, 12, v_k_3142_);
lean_closure_set(v___f_3163_, 13, v_inst_3154_);
lean_closure_set(v___f_3163_, 14, v_msg_3155_);
lean_closure_set(v___f_3163_, 15, v___f_3156_);
v___f_3164_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3164_, 0, v_toPure_3161_);
lean_closure_set(v___f_3164_, 1, v_cls_3150_);
lean_closure_set(v___f_3164_, 2, v_toBind_3153_);
lean_closure_set(v___f_3164_, 3, v_inst_3157_);
v___x_3165_ = lean_apply_4(v_toBind_3153_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3160_, v___f_3164_);
v___x_3166_ = lean_apply_4(v_toBind_3153_, lean_box(0), lean_box(0), v___x_3165_, v___f_3163_);
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_k_3167_ = _args[0];
lean_object* v_inst_3168_ = _args[1];
lean_object* v_toApplicative_3169_ = _args[2];
lean_object* v_inst_3170_ = _args[3];
lean_object* v_always_3171_ = _args[4];
lean_object* v_inst_3172_ = _args[5];
lean_object* v_inst_3173_ = _args[6];
lean_object* v_inst_3174_ = _args[7];
lean_object* v_cls_3175_ = _args[8];
lean_object* v_collapsed_3176_ = _args[9];
lean_object* v_tag_3177_ = _args[10];
lean_object* v_toBind_3178_ = _args[11];
lean_object* v_inst_3179_ = _args[12];
lean_object* v_msg_3180_ = _args[13];
lean_object* v___f_3181_ = _args[14];
lean_object* v_inst_3182_ = _args[15];
lean_object* v_opts_3183_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3184_; lean_object* v_res_3185_; 
v_collapsed_boxed_3184_ = lean_unbox(v_collapsed_3176_);
v_res_3185_ = l_Lean_withTraceNodeBefore___redArg___lam__7(v_k_3167_, v_inst_3168_, v_toApplicative_3169_, v_inst_3170_, v_always_3171_, v_inst_3172_, v_inst_3173_, v_inst_3174_, v_cls_3175_, v_collapsed_boxed_3184_, v_tag_3177_, v_toBind_3178_, v_inst_3179_, v_msg_3180_, v___f_3181_, v_inst_3182_, v_opts_3183_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object* v_inst_3186_, lean_object* v_inst_3187_, lean_object* v_inst_3188_, lean_object* v_inst_3189_, lean_object* v_inst_3190_, lean_object* v_always_3191_, lean_object* v_inst_3192_, lean_object* v_inst_3193_, lean_object* v_cls_3194_, lean_object* v_msg_3195_, lean_object* v_k_3196_, uint8_t v_collapsed_3197_, lean_object* v_tag_3198_){
_start:
{
lean_object* v_toApplicative_3199_; lean_object* v_toBind_3200_; lean_object* v___f_3201_; lean_object* v___x_3202_; lean_object* v___f_3203_; lean_object* v___x_3204_; 
v_toApplicative_3199_ = lean_ctor_get(v_inst_3186_, 0);
lean_inc_ref(v_toApplicative_3199_);
v_toBind_3200_ = lean_ctor_get(v_inst_3186_, 1);
lean_inc_n(v_toBind_3200_, 2);
lean_inc(v_inst_3189_);
v___f_3201_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3201_, 0, v_inst_3189_);
v___x_3202_ = lean_box(v_collapsed_3197_);
lean_inc(v_inst_3190_);
v___f_3203_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3203_, 0, v_k_3196_);
lean_closure_set(v___f_3203_, 1, v_inst_3187_);
lean_closure_set(v___f_3203_, 2, v_toApplicative_3199_);
lean_closure_set(v___f_3203_, 3, v_inst_3188_);
lean_closure_set(v___f_3203_, 4, v_always_3191_);
lean_closure_set(v___f_3203_, 5, v_inst_3186_);
lean_closure_set(v___f_3203_, 6, v_inst_3189_);
lean_closure_set(v___f_3203_, 7, v_inst_3193_);
lean_closure_set(v___f_3203_, 8, v_cls_3194_);
lean_closure_set(v___f_3203_, 9, v___x_3202_);
lean_closure_set(v___f_3203_, 10, v_tag_3198_);
lean_closure_set(v___f_3203_, 11, v_toBind_3200_);
lean_closure_set(v___f_3203_, 12, v_inst_3192_);
lean_closure_set(v___f_3203_, 13, v_msg_3195_);
lean_closure_set(v___f_3203_, 14, v___f_3201_);
lean_closure_set(v___f_3203_, 15, v_inst_3190_);
v___x_3204_ = lean_apply_4(v_toBind_3200_, lean_box(0), lean_box(0), v_inst_3190_, v___f_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object* v_inst_3205_, lean_object* v_inst_3206_, lean_object* v_inst_3207_, lean_object* v_inst_3208_, lean_object* v_inst_3209_, lean_object* v_always_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_cls_3213_, lean_object* v_msg_3214_, lean_object* v_k_3215_, lean_object* v_collapsed_3216_, lean_object* v_tag_3217_){
_start:
{
uint8_t v_collapsed_boxed_3218_; lean_object* v_res_3219_; 
v_collapsed_boxed_3218_ = lean_unbox(v_collapsed_3216_);
v_res_3219_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3205_, v_inst_3206_, v_inst_3207_, v_inst_3208_, v_inst_3209_, v_always_3210_, v_inst_3211_, v_inst_3212_, v_cls_3213_, v_msg_3214_, v_k_3215_, v_collapsed_boxed_3218_, v_tag_3217_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object* v_00_u03b1_3220_, lean_object* v_m_3221_, lean_object* v_inst_3222_, lean_object* v_inst_3223_, lean_object* v_00_u03b5_3224_, lean_object* v_inst_3225_, lean_object* v_inst_3226_, lean_object* v_inst_3227_, lean_object* v_always_3228_, lean_object* v_inst_3229_, lean_object* v_inst_3230_, lean_object* v_cls_3231_, lean_object* v_msg_3232_, lean_object* v_k_3233_, uint8_t v_collapsed_3234_, lean_object* v_tag_3235_){
_start:
{
lean_object* v_toApplicative_3236_; lean_object* v_toBind_3237_; lean_object* v___f_3238_; lean_object* v___x_3239_; lean_object* v___f_3240_; lean_object* v___x_3241_; 
v_toApplicative_3236_ = lean_ctor_get(v_inst_3222_, 0);
lean_inc_ref(v_toApplicative_3236_);
v_toBind_3237_ = lean_ctor_get(v_inst_3222_, 1);
lean_inc_n(v_toBind_3237_, 2);
lean_inc(v_inst_3226_);
v___f_3238_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3238_, 0, v_inst_3226_);
v___x_3239_ = lean_box(v_collapsed_3234_);
lean_inc(v_inst_3227_);
v___f_3240_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3240_, 0, v_k_3233_);
lean_closure_set(v___f_3240_, 1, v_inst_3223_);
lean_closure_set(v___f_3240_, 2, v_toApplicative_3236_);
lean_closure_set(v___f_3240_, 3, v_inst_3225_);
lean_closure_set(v___f_3240_, 4, v_always_3228_);
lean_closure_set(v___f_3240_, 5, v_inst_3222_);
lean_closure_set(v___f_3240_, 6, v_inst_3226_);
lean_closure_set(v___f_3240_, 7, v_inst_3230_);
lean_closure_set(v___f_3240_, 8, v_cls_3231_);
lean_closure_set(v___f_3240_, 9, v___x_3239_);
lean_closure_set(v___f_3240_, 10, v_tag_3235_);
lean_closure_set(v___f_3240_, 11, v_toBind_3237_);
lean_closure_set(v___f_3240_, 12, v_inst_3229_);
lean_closure_set(v___f_3240_, 13, v_msg_3232_);
lean_closure_set(v___f_3240_, 14, v___f_3238_);
lean_closure_set(v___f_3240_, 15, v_inst_3227_);
v___x_3241_ = lean_apply_4(v_toBind_3237_, lean_box(0), lean_box(0), v_inst_3227_, v___f_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object* v_00_u03b1_3242_, lean_object* v_m_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_00_u03b5_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_always_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_cls_3253_, lean_object* v_msg_3254_, lean_object* v_k_3255_, lean_object* v_collapsed_3256_, lean_object* v_tag_3257_){
_start:
{
uint8_t v_collapsed_boxed_3258_; lean_object* v_res_3259_; 
v_collapsed_boxed_3258_ = lean_unbox(v_collapsed_3256_);
v_res_3259_ = l_Lean_withTraceNodeBefore(v_00_u03b1_3242_, v_m_3243_, v_inst_3244_, v_inst_3245_, v_00_u03b5_3246_, v_inst_3247_, v_inst_3248_, v_inst_3249_, v_always_3250_, v_inst_3251_, v_inst_3252_, v_cls_3253_, v_msg_3254_, v_k_3255_, v_collapsed_boxed_3258_, v_tag_3257_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0(lean_object* v_toApplicative_3260_, lean_object* v_____s_3261_){
_start:
{
lean_object* v_toPure_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v_toPure_3262_ = lean_ctor_get(v_toApplicative_3260_, 1);
lean_inc(v_toPure_3262_);
lean_dec_ref(v_toApplicative_3260_);
v___x_3263_ = lean_box(0);
v___x_3264_ = lean_apply_2(v_toPure_3262_, lean_box(0), v___x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__1(lean_object* v_x_3265_, lean_object* v_x_3266_){
_start:
{
lean_object* v_fst_3267_; lean_object* v_fst_3268_; lean_object* v_fst_3269_; lean_object* v_fst_3270_; uint8_t v___x_3271_; 
v_fst_3267_ = lean_ctor_get(v_x_3265_, 0);
v_fst_3268_ = lean_ctor_get(v_x_3266_, 0);
v_fst_3269_ = lean_ctor_get(v_fst_3267_, 0);
v_fst_3270_ = lean_ctor_get(v_fst_3268_, 0);
v___x_3271_ = lean_nat_dec_lt(v_fst_3269_, v_fst_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1___boxed(lean_object* v_x_3272_, lean_object* v_x_3273_){
_start:
{
uint8_t v_res_3274_; lean_object* v_r_3275_; 
v_res_3274_ = l_Lean_addTraceAsMessages___redArg___lam__1(v_x_3272_, v_x_3273_);
lean_dec_ref(v_x_3273_);
lean_dec_ref(v_x_3272_);
v_r_3275_ = lean_box(v_res_3274_);
return v_r_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object* v_x1_3276_, lean_object* v_x2_3277_, lean_object* v_x3_3278_){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3279_, 0, v_x2_3277_);
lean_ctor_set(v___x_3279_, 1, v_x3_3278_);
v___x_3280_ = lean_array_push(v_x1_3276_, v___x_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object* v_toApplicative_3281_, lean_object* v___x_3282_, lean_object* v_r_3283_){
_start:
{
lean_object* v_toPure_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_toPure_3284_ = lean_ctor_get(v_toApplicative_3281_, 1);
lean_inc(v_toPure_3284_);
lean_dec_ref(v_toApplicative_3281_);
v___x_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3282_);
v___x_3286_ = lean_apply_2(v_toPure_3284_, lean_box(0), v___x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object* v_____do__lift_3287_, lean_object* v___x_3288_, lean_object* v_fst_3289_, lean_object* v_snd_3290_, lean_object* v_logMessage_3291_, lean_object* v_toBind_3292_, lean_object* v___f_3293_, lean_object* v_____do__lift_3294_){
_start:
{
uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3295_ = 0;
v___x_3296_ = l_Lean_Elab_mkMessageCore(v_____do__lift_3287_, v_____do__lift_3294_, v___x_3288_, v___x_3295_, v_fst_3289_, v_snd_3290_);
v___x_3297_ = lean_apply_1(v_logMessage_3291_, v___x_3296_);
v___x_3298_ = lean_apply_4(v_toBind_3292_, lean_box(0), lean_box(0), v___x_3297_, v___f_3293_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object* v_____do__lift_3299_, lean_object* v___x_3300_, lean_object* v_fst_3301_, lean_object* v_snd_3302_, lean_object* v_logMessage_3303_, lean_object* v_toBind_3304_, lean_object* v___f_3305_, lean_object* v_____do__lift_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_addTraceAsMessages___redArg___lam__4(v_____do__lift_3299_, v___x_3300_, v_fst_3301_, v_snd_3302_, v_logMessage_3303_, v_toBind_3304_, v___f_3305_, v_____do__lift_3306_);
lean_dec(v_snd_3302_);
lean_dec(v_fst_3301_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object* v___x_3308_, lean_object* v_fst_3309_, lean_object* v_snd_3310_, lean_object* v_logMessage_3311_, lean_object* v_toBind_3312_, lean_object* v___f_3313_, lean_object* v_toMonadFileMap_3314_, lean_object* v_____do__lift_3315_){
_start:
{
lean_object* v___f_3316_; lean_object* v___x_3317_; 
lean_inc(v_toBind_3312_);
v___f_3316_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_3316_, 0, v_____do__lift_3315_);
lean_closure_set(v___f_3316_, 1, v___x_3308_);
lean_closure_set(v___f_3316_, 2, v_fst_3309_);
lean_closure_set(v___f_3316_, 3, v_snd_3310_);
lean_closure_set(v___f_3316_, 4, v_logMessage_3311_);
lean_closure_set(v___f_3316_, 5, v_toBind_3312_);
lean_closure_set(v___f_3316_, 6, v___f_3313_);
v___x_3317_ = lean_apply_4(v_toBind_3312_, lean_box(0), lean_box(0), v_toMonadFileMap_3314_, v___f_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object* v___x_3318_, uint8_t v___x_3319_, lean_object* v_inst_3320_, lean_object* v_toBind_3321_, lean_object* v___f_3322_, lean_object* v_a_3323_, lean_object* v_x_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v_fst_3326_; lean_object* v_snd_3327_; lean_object* v_fst_3328_; lean_object* v_snd_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3349_; 
v_fst_3326_ = lean_ctor_get(v_a_3323_, 0);
lean_inc(v_fst_3326_);
v_snd_3327_ = lean_ctor_get(v_a_3323_, 1);
lean_inc(v_snd_3327_);
lean_dec_ref(v_a_3323_);
v_fst_3328_ = lean_ctor_get(v_fst_3326_, 0);
v_snd_3329_ = lean_ctor_get(v_fst_3326_, 1);
v_isSharedCheck_3349_ = !lean_is_exclusive(v_fst_3326_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3331_ = v_fst_3326_;
v_isShared_3332_ = v_isSharedCheck_3349_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_snd_3329_);
lean_inc(v_fst_3328_);
lean_dec(v_fst_3326_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3349_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; double v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v_toMonadFileMap_3338_; lean_object* v_getFileName_3339_; lean_object* v_logMessage_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3333_ = lean_box(0);
v___x_3334_ = lean_box(0);
v___x_3335_ = lean_float_of_nat(v___x_3318_);
v___x_3336_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_3337_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3337_, 0, v___x_3333_);
lean_ctor_set(v___x_3337_, 1, v___x_3334_);
lean_ctor_set(v___x_3337_, 2, v___x_3336_);
lean_ctor_set_float(v___x_3337_, sizeof(void*)*3, v___x_3335_);
lean_ctor_set_float(v___x_3337_, sizeof(void*)*3 + 8, v___x_3335_);
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*3 + 16, v___x_3319_);
v_toMonadFileMap_3338_ = lean_ctor_get(v_inst_3320_, 0);
lean_inc(v_toMonadFileMap_3338_);
v_getFileName_3339_ = lean_ctor_get(v_inst_3320_, 2);
lean_inc(v_getFileName_3339_);
v_logMessage_3340_ = lean_ctor_get(v_inst_3320_, 4);
lean_inc(v_logMessage_3340_);
lean_dec_ref(v_inst_3320_);
v___x_3341_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_3342_ = l_Lean_MessageData_nil;
v___x_3343_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3337_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
lean_ctor_set(v___x_3343_, 2, v_snd_3327_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set_tag(v___x_3331_, 8);
lean_ctor_set(v___x_3331_, 1, v___x_3343_);
lean_ctor_set(v___x_3331_, 0, v___x_3341_);
v___x_3345_ = v___x_3331_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___f_3346_; lean_object* v___x_3347_; 
lean_inc(v_toBind_3321_);
v___f_3346_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__5), 8, 7);
lean_closure_set(v___f_3346_, 0, v___x_3345_);
lean_closure_set(v___f_3346_, 1, v_fst_3328_);
lean_closure_set(v___f_3346_, 2, v_snd_3329_);
lean_closure_set(v___f_3346_, 3, v_logMessage_3340_);
lean_closure_set(v___f_3346_, 4, v_toBind_3321_);
lean_closure_set(v___f_3346_, 5, v___f_3322_);
lean_closure_set(v___f_3346_, 6, v_toMonadFileMap_3338_);
v___x_3347_ = lean_apply_4(v_toBind_3321_, lean_box(0), lean_box(0), v_getFileName_3339_, v___f_3346_);
return v___x_3347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object* v___x_3350_, lean_object* v___x_3351_, lean_object* v_inst_3352_, lean_object* v_toBind_3353_, lean_object* v___f_3354_, lean_object* v_a_3355_, lean_object* v_x_3356_, lean_object* v___y_3357_){
_start:
{
uint8_t v___x_1915__boxed_3358_; lean_object* v_res_3359_; 
v___x_1915__boxed_3358_ = lean_unbox(v___x_3351_);
v_res_3359_ = l_Lean_addTraceAsMessages___redArg___lam__6(v___x_3350_, v___x_1915__boxed_3358_, v_inst_3352_, v_toBind_3353_, v___f_3354_, v_a_3355_, v_x_3356_, v___y_3357_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object* v___x_3360_, lean_object* v___f_3361_, lean_object* v_acc_3362_, lean_object* v_l_3363_){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_3360_, v___f_3361_, v_acc_3362_, v_l_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object* v_toApplicative_3365_, uint8_t v___x_3366_, lean_object* v_inst_3367_, lean_object* v_toBind_3368_, lean_object* v_inst_3369_, lean_object* v___f_3370_, lean_object* v___f_3371_, lean_object* v___f_3372_, lean_object* v_____s_3373_){
_start:
{
lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3400_; lean_object* v_size_3407_; lean_object* v_buckets_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v_size_3407_ = lean_ctor_get(v_____s_3373_, 0);
lean_inc(v_size_3407_);
v_buckets_3408_ = lean_ctor_get(v_____s_3373_, 1);
lean_inc_ref(v_buckets_3408_);
lean_dec_ref(v_____s_3373_);
v___x_3409_ = lean_mk_empty_array_with_capacity(v_size_3407_);
lean_dec(v_size_3407_);
v___x_3410_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v___x_3411_ = lean_unsigned_to_nat(0u);
v___x_3412_ = lean_array_get_size(v_buckets_3408_);
v___x_3413_ = lean_nat_dec_lt(v___x_3411_, v___x_3412_);
if (v___x_3413_ == 0)
{
lean_dec_ref(v_buckets_3408_);
lean_dec_ref(v___f_3372_);
v___y_3400_ = v___x_3409_;
goto v___jp_3399_;
}
else
{
lean_object* v___f_3414_; uint8_t v___x_3415_; 
v___f_3414_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__7), 4, 2);
lean_closure_set(v___f_3414_, 0, v___x_3410_);
lean_closure_set(v___f_3414_, 1, v___f_3372_);
v___x_3415_ = lean_nat_dec_le(v___x_3412_, v___x_3412_);
if (v___x_3415_ == 0)
{
if (v___x_3413_ == 0)
{
lean_dec_ref(v___f_3414_);
lean_dec_ref(v_buckets_3408_);
v___y_3400_ = v___x_3409_;
goto v___jp_3399_;
}
else
{
size_t v___x_3416_; size_t v___x_3417_; lean_object* v___x_3418_; 
v___x_3416_ = ((size_t)0ULL);
v___x_3417_ = lean_usize_of_nat(v___x_3412_);
v___x_3418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3410_, v___f_3414_, v_buckets_3408_, v___x_3416_, v___x_3417_, v___x_3409_);
v___y_3400_ = v___x_3418_;
goto v___jp_3399_;
}
}
else
{
size_t v___x_3419_; size_t v___x_3420_; lean_object* v___x_3421_; 
v___x_3419_ = ((size_t)0ULL);
v___x_3420_ = lean_usize_of_nat(v___x_3412_);
v___x_3421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3410_, v___f_3414_, v_buckets_3408_, v___x_3419_, v___x_3420_, v___x_3409_);
v___y_3400_ = v___x_3421_;
goto v___jp_3399_;
}
}
v___jp_3374_:
{
lean_object* v___x_3377_; lean_object* v___f_3378_; lean_object* v___x_3379_; lean_object* v___f_3380_; size_t v_sz_3381_; size_t v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3377_ = lean_box(0);
v___f_3378_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3378_, 0, v_toApplicative_3365_);
lean_closure_set(v___f_3378_, 1, v___x_3377_);
v___x_3379_ = lean_box(v___x_3366_);
lean_inc(v_toBind_3368_);
v___f_3380_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__6___boxed), 8, 5);
lean_closure_set(v___f_3380_, 0, v___y_3375_);
lean_closure_set(v___f_3380_, 1, v___x_3379_);
lean_closure_set(v___f_3380_, 2, v_inst_3367_);
lean_closure_set(v___f_3380_, 3, v_toBind_3368_);
lean_closure_set(v___f_3380_, 4, v___f_3378_);
v_sz_3381_ = lean_array_size(v___y_3376_);
v___x_3382_ = ((size_t)0ULL);
v___x_3383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3369_, v___y_3376_, v___f_3380_, v_sz_3381_, v___x_3382_, v___x_3377_);
v___x_3384_ = lean_apply_4(v_toBind_3368_, lean_box(0), lean_box(0), v___x_3383_, v___f_3370_);
return v___x_3384_;
}
v___jp_3385_:
{
lean_object* v___x_3391_; 
v___x_3391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_3371_, v___y_3389_, v___y_3387_, v___y_3388_, v___y_3390_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_3390_);
lean_dec(v___y_3389_);
v___y_3375_ = v___y_3386_;
v___y_3376_ = v___x_3391_;
goto v___jp_3374_;
}
v___jp_3392_:
{
uint8_t v___x_3398_; 
v___x_3398_ = lean_nat_dec_le(v___y_3397_, v___y_3395_);
if (v___x_3398_ == 0)
{
lean_dec(v___y_3395_);
lean_inc(v___y_3397_);
v___y_3386_ = v___y_3393_;
v___y_3387_ = v___y_3394_;
v___y_3388_ = v___y_3397_;
v___y_3389_ = v___y_3396_;
v___y_3390_ = v___y_3397_;
goto v___jp_3385_;
}
else
{
v___y_3386_ = v___y_3393_;
v___y_3387_ = v___y_3394_;
v___y_3388_ = v___y_3397_;
v___y_3389_ = v___y_3396_;
v___y_3390_ = v___y_3395_;
goto v___jp_3385_;
}
}
v___jp_3399_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
v___x_3401_ = lean_unsigned_to_nat(0u);
v___x_3402_ = lean_array_get_size(v___y_3400_);
v___x_3403_ = lean_nat_dec_eq(v___x_3402_, v___x_3401_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3404_ = lean_unsigned_to_nat(1u);
v___x_3405_ = lean_nat_sub(v___x_3402_, v___x_3404_);
v___x_3406_ = lean_nat_dec_le(v___x_3401_, v___x_3405_);
if (v___x_3406_ == 0)
{
lean_inc(v___x_3405_);
v___y_3393_ = v___x_3401_;
v___y_3394_ = v___y_3400_;
v___y_3395_ = v___x_3405_;
v___y_3396_ = v___x_3402_;
v___y_3397_ = v___x_3405_;
goto v___jp_3392_;
}
else
{
v___y_3393_ = v___x_3401_;
v___y_3394_ = v___y_3400_;
v___y_3395_ = v___x_3405_;
v___y_3396_ = v___x_3402_;
v___y_3397_ = v___x_3401_;
goto v___jp_3392_;
}
}
else
{
lean_dec_ref(v___f_3371_);
v___y_3375_ = v___x_3401_;
v___y_3376_ = v___y_3400_;
goto v___jp_3374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object* v_toApplicative_3422_, lean_object* v___x_3423_, lean_object* v_inst_3424_, lean_object* v_toBind_3425_, lean_object* v_inst_3426_, lean_object* v___f_3427_, lean_object* v___f_3428_, lean_object* v___f_3429_, lean_object* v_____s_3430_){
_start:
{
uint8_t v___x_2003__boxed_3431_; lean_object* v_res_3432_; 
v___x_2003__boxed_3431_ = lean_unbox(v___x_3423_);
v_res_3432_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_toApplicative_3422_, v___x_2003__boxed_3431_, v_inst_3424_, v_toBind_3425_, v_inst_3426_, v___f_3427_, v___f_3428_, v___f_3429_, v_____s_3430_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object* v_traceElem_3433_, lean_object* v_toApplicative_3434_, lean_object* v___f_3435_, lean_object* v___f_3436_, lean_object* v_____s_3437_, uint8_t v___x_3438_, lean_object* v_____do__lift_3439_){
_start:
{
lean_object* v_ref_3440_; lean_object* v_msg_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3466_; 
v_ref_3440_ = lean_ctor_get(v_traceElem_3433_, 0);
v_msg_3441_ = lean_ctor_get(v_traceElem_3433_, 1);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_traceElem_3433_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3443_ = v_traceElem_3433_;
v_isShared_3444_ = v_isSharedCheck_3466_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_msg_3441_);
lean_inc(v_ref_3440_);
lean_dec(v_traceElem_3433_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3466_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v_ref_3458_; lean_object* v___y_3460_; lean_object* v___x_3463_; 
v_ref_3458_ = l_Lean_replaceRef(v_ref_3440_, v_____do__lift_3439_);
lean_dec(v_ref_3440_);
v___x_3463_ = l_Lean_Syntax_getPos_x3f(v_ref_3458_, v___x_3438_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v___x_3464_; 
v___x_3464_ = lean_unsigned_to_nat(0u);
v___y_3460_ = v___x_3464_;
goto v___jp_3459_;
}
else
{
lean_object* v_val_3465_; 
v_val_3465_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_val_3465_);
lean_dec_ref(v___x_3463_);
v___y_3460_ = v_val_3465_;
goto v___jp_3459_;
}
v___jp_3445_:
{
lean_object* v_toPure_3448_; lean_object* v___x_3450_; 
v_toPure_3448_ = lean_ctor_get(v_toApplicative_3434_, 1);
lean_inc(v_toPure_3448_);
lean_dec_ref(v_toApplicative_3434_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v___y_3447_);
lean_ctor_set(v___x_3443_, 0, v___y_3446_);
v___x_3450_ = v___x_3443_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___y_3446_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v___y_3447_);
v___x_3450_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v_pos2traces_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3451_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
lean_inc_ref(v___x_3450_);
lean_inc_ref(v___f_3436_);
lean_inc_ref(v___f_3435_);
v___x_3452_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_3435_, v___f_3436_, v_____s_3437_, v___x_3450_, v___x_3451_);
v___x_3453_ = lean_array_push(v___x_3452_, v_msg_3441_);
v_pos2traces_3454_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3435_, v___f_3436_, v_____s_3437_, v___x_3450_, v___x_3453_);
v___x_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3455_, 0, v_pos2traces_3454_);
v___x_3456_ = lean_apply_2(v_toPure_3448_, lean_box(0), v___x_3455_);
return v___x_3456_;
}
}
v___jp_3459_:
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Lean_Syntax_getTailPos_x3f(v_ref_3458_, v___x_3438_);
lean_dec(v_ref_3458_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_inc(v___y_3460_);
v___y_3446_ = v___y_3460_;
v___y_3447_ = v___y_3460_;
goto v___jp_3445_;
}
else
{
lean_object* v_val_3462_; 
v_val_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_val_3462_);
lean_dec_ref(v___x_3461_);
v___y_3446_ = v___y_3460_;
v___y_3447_ = v_val_3462_;
goto v___jp_3445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object* v_traceElem_3467_, lean_object* v_toApplicative_3468_, lean_object* v___f_3469_, lean_object* v___f_3470_, lean_object* v_____s_3471_, lean_object* v___x_3472_, lean_object* v_____do__lift_3473_){
_start:
{
uint8_t v___x_2128__boxed_3474_; lean_object* v_res_3475_; 
v___x_2128__boxed_3474_ = lean_unbox(v___x_3472_);
v_res_3475_ = l_Lean_addTraceAsMessages___redArg___lam__9(v_traceElem_3467_, v_toApplicative_3468_, v___f_3469_, v___f_3470_, v_____s_3471_, v___x_2128__boxed_3474_, v_____do__lift_3473_);
lean_dec(v_____do__lift_3473_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object* v_inst_3476_, lean_object* v_toApplicative_3477_, lean_object* v___f_3478_, lean_object* v___f_3479_, uint8_t v___x_3480_, lean_object* v_toBind_3481_, lean_object* v_traceElem_3482_, lean_object* v_____s_3483_){
_start:
{
lean_object* v_getRef_3484_; lean_object* v___x_3485_; lean_object* v___f_3486_; lean_object* v___x_3487_; 
v_getRef_3484_ = lean_ctor_get(v_inst_3476_, 0);
lean_inc(v_getRef_3484_);
lean_dec_ref(v_inst_3476_);
v___x_3485_ = lean_box(v___x_3480_);
v___f_3486_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_3486_, 0, v_traceElem_3482_);
lean_closure_set(v___f_3486_, 1, v_toApplicative_3477_);
lean_closure_set(v___f_3486_, 2, v___f_3478_);
lean_closure_set(v___f_3486_, 3, v___f_3479_);
lean_closure_set(v___f_3486_, 4, v_____s_3483_);
lean_closure_set(v___f_3486_, 5, v___x_3485_);
v___x_3487_ = lean_apply_4(v_toBind_3481_, lean_box(0), lean_box(0), v_getRef_3484_, v___f_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object* v_inst_3488_, lean_object* v_toApplicative_3489_, lean_object* v___f_3490_, lean_object* v___f_3491_, lean_object* v___x_3492_, lean_object* v_toBind_3493_, lean_object* v_traceElem_3494_, lean_object* v_____s_3495_){
_start:
{
uint8_t v___x_2188__boxed_3496_; lean_object* v_res_3497_; 
v___x_2188__boxed_3496_ = lean_unbox(v___x_3492_);
v_res_3497_ = l_Lean_addTraceAsMessages___redArg___lam__10(v_inst_3488_, v_toApplicative_3489_, v___f_3490_, v___f_3491_, v___x_2188__boxed_3496_, v_toBind_3493_, v_traceElem_3494_, v_____s_3495_);
return v_res_3497_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___f_3499_; 
v___x_3498_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_3499_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3499_, 0, v___x_3498_);
return v___f_3499_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___f_3500_; lean_object* v___f_3501_; 
v___f_3500_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__0, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0);
v___f_3501_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3501_, 0, v___f_3500_);
lean_closure_set(v___f_3501_, 1, v___f_3500_);
return v___f_3501_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = lean_box(0);
v___x_3506_ = lean_unsigned_to_nat(16u);
v___x_3507_ = lean_mk_array(v___x_3506_, v___x_3505_);
return v___x_3507_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v_pos2traces_3510_; 
v___x_3508_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__4, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4);
v___x_3509_ = lean_unsigned_to_nat(0u);
v_pos2traces_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_3510_, 0, v___x_3509_);
lean_ctor_set(v_pos2traces_3510_, 1, v___x_3508_);
return v_pos2traces_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11(lean_object* v_inst_3511_, lean_object* v_toApplicative_3512_, lean_object* v_toBind_3513_, lean_object* v_inst_3514_, lean_object* v___f_3515_, lean_object* v_traces_3516_){
_start:
{
uint8_t v___x_3517_; 
v___x_3517_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_3516_);
if (v___x_3517_ == 0)
{
lean_object* v___f_3518_; lean_object* v___f_3519_; lean_object* v___x_3520_; lean_object* v___f_3521_; lean_object* v_pos2traces_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___f_3518_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__1, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1);
v___f_3519_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___lam__11___closed__3));
v___x_3520_ = lean_box(v___x_3517_);
lean_inc(v_toBind_3513_);
v___f_3521_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3521_, 0, v_inst_3511_);
lean_closure_set(v___f_3521_, 1, v_toApplicative_3512_);
lean_closure_set(v___f_3521_, 2, v___f_3518_);
lean_closure_set(v___f_3521_, 3, v___f_3519_);
lean_closure_set(v___f_3521_, 4, v___x_3520_);
lean_closure_set(v___f_3521_, 5, v_toBind_3513_);
v_pos2traces_3522_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__5, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5);
v___x_3523_ = l_Lean_PersistentArray_forIn___redArg(v_inst_3514_, v_traces_3516_, v_pos2traces_3522_, v___f_3521_);
v___x_3524_ = lean_apply_4(v_toBind_3513_, lean_box(0), lean_box(0), v___x_3523_, v___f_3515_);
return v___x_3524_;
}
else
{
lean_object* v_toPure_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
lean_dec_ref(v_traces_3516_);
lean_dec(v___f_3515_);
lean_dec_ref(v_inst_3514_);
lean_dec(v_toBind_3513_);
lean_dec_ref(v_inst_3511_);
v_toPure_3525_ = lean_ctor_get(v_toApplicative_3512_, 1);
lean_inc(v_toPure_3525_);
lean_dec_ref(v_toApplicative_3512_);
v___x_3526_ = lean_box(0);
v___x_3527_ = lean_apply_2(v_toPure_3525_, lean_box(0), v___x_3526_);
return v___x_3527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12(lean_object* v___x_3528_, lean_object* v_toApplicative_3529_, lean_object* v_inst_3530_, lean_object* v_toBind_3531_, lean_object* v_inst_3532_, lean_object* v___f_3533_, lean_object* v___f_3534_, lean_object* v___f_3535_, lean_object* v_inst_3536_, lean_object* v_inst_3537_, lean_object* v_____do__lift_3538_){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = l_Lean_trace_profiler_output;
v___x_3540_ = l_Lean_Option_get_x3f___redArg(v___x_3528_, v_____do__lift_3538_, v___x_3539_);
if (lean_obj_tag(v___x_3540_) == 0)
{
uint8_t v___x_3541_; lean_object* v___x_3542_; lean_object* v___f_3543_; lean_object* v___f_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3541_ = 1;
v___x_3542_ = lean_box(v___x_3541_);
lean_inc_ref_n(v_inst_3532_, 2);
lean_inc_n(v_toBind_3531_, 2);
lean_inc_ref(v_toApplicative_3529_);
v___f_3543_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__8___boxed), 9, 8);
lean_closure_set(v___f_3543_, 0, v_toApplicative_3529_);
lean_closure_set(v___f_3543_, 1, v___x_3542_);
lean_closure_set(v___f_3543_, 2, v_inst_3530_);
lean_closure_set(v___f_3543_, 3, v_toBind_3531_);
lean_closure_set(v___f_3543_, 4, v_inst_3532_);
lean_closure_set(v___f_3543_, 5, v___f_3533_);
lean_closure_set(v___f_3543_, 6, v___f_3534_);
lean_closure_set(v___f_3543_, 7, v___f_3535_);
v___f_3544_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__11), 6, 5);
lean_closure_set(v___f_3544_, 0, v_inst_3536_);
lean_closure_set(v___f_3544_, 1, v_toApplicative_3529_);
lean_closure_set(v___f_3544_, 2, v_toBind_3531_);
lean_closure_set(v___f_3544_, 3, v_inst_3532_);
lean_closure_set(v___f_3544_, 4, v___f_3543_);
v___x_3545_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3532_, v_inst_3537_);
v___x_3546_ = lean_apply_4(v_toBind_3531_, lean_box(0), lean_box(0), v___x_3545_, v___f_3544_);
return v___x_3546_;
}
else
{
lean_object* v_toPure_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_dec_ref(v___x_3540_);
lean_dec_ref(v_inst_3537_);
lean_dec_ref(v_inst_3536_);
lean_dec_ref(v___f_3535_);
lean_dec_ref(v___f_3534_);
lean_dec(v___f_3533_);
lean_dec_ref(v_inst_3532_);
lean_dec(v_toBind_3531_);
lean_dec_ref(v_inst_3530_);
v_toPure_3547_ = lean_ctor_get(v_toApplicative_3529_, 1);
lean_inc(v_toPure_3547_);
lean_dec_ref(v_toApplicative_3529_);
v___x_3548_ = lean_box(0);
v___x_3549_ = lean_apply_2(v_toPure_3547_, lean_box(0), v___x_3548_);
return v___x_3549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12___boxed(lean_object* v___x_3550_, lean_object* v_toApplicative_3551_, lean_object* v_inst_3552_, lean_object* v_toBind_3553_, lean_object* v_inst_3554_, lean_object* v___f_3555_, lean_object* v___f_3556_, lean_object* v___f_3557_, lean_object* v_inst_3558_, lean_object* v_inst_3559_, lean_object* v_____do__lift_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_addTraceAsMessages___redArg___lam__12(v___x_3550_, v_toApplicative_3551_, v_inst_3552_, v_toBind_3553_, v_inst_3554_, v___f_3555_, v___f_3556_, v___f_3557_, v_inst_3558_, v_inst_3559_, v_____do__lift_3560_);
lean_dec_ref(v_____do__lift_3560_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object* v_inst_3564_, lean_object* v_inst_3565_, lean_object* v_inst_3566_, lean_object* v_inst_3567_, lean_object* v_inst_3568_){
_start:
{
lean_object* v___x_3569_; lean_object* v_toApplicative_3570_; lean_object* v_toBind_3571_; lean_object* v___f_3572_; lean_object* v___f_3573_; lean_object* v___f_3574_; lean_object* v___f_3575_; lean_object* v___x_3576_; 
v___x_3569_ = l_Lean_KVMap_instValueString;
v_toApplicative_3570_ = lean_ctor_get(v_inst_3565_, 0);
lean_inc_ref_n(v_toApplicative_3570_, 2);
v_toBind_3571_ = lean_ctor_get(v_inst_3565_, 1);
lean_inc_n(v_toBind_3571_, 2);
v___f_3572_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3572_, 0, v_toApplicative_3570_);
v___f_3573_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__0));
v___f_3574_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__1));
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3575_, 0, v___x_3569_);
lean_closure_set(v___f_3575_, 1, v_toApplicative_3570_);
lean_closure_set(v___f_3575_, 2, v_inst_3567_);
lean_closure_set(v___f_3575_, 3, v_toBind_3571_);
lean_closure_set(v___f_3575_, 4, v_inst_3565_);
lean_closure_set(v___f_3575_, 5, v___f_3572_);
lean_closure_set(v___f_3575_, 6, v___f_3573_);
lean_closure_set(v___f_3575_, 7, v___f_3574_);
lean_closure_set(v___f_3575_, 8, v_inst_3566_);
lean_closure_set(v___f_3575_, 9, v_inst_3568_);
v___x_3576_ = lean_apply_4(v_toBind_3571_, lean_box(0), lean_box(0), v_inst_3564_, v___f_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object* v_m_3577_, lean_object* v_inst_3578_, lean_object* v_inst_3579_, lean_object* v_inst_3580_, lean_object* v_inst_3581_, lean_object* v_inst_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Lean_addTraceAsMessages___redArg(v_inst_3578_, v_inst_3579_, v_inst_3580_, v_inst_3581_, v_inst_3582_);
return v___x_3583_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3625_ = lean_unsigned_to_nat(2826257906u);
v___x_3626_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3627_ = l_Lean_Name_num___override(v___x_3626_, v___x_3625_);
return v___x_3627_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3630_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3631_ = l_Lean_Name_str___override(v___x_3630_, v___x_3629_);
return v___x_3631_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3634_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3635_ = l_Lean_Name_str___override(v___x_3634_, v___x_3633_);
return v___x_3635_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3636_ = lean_unsigned_to_nat(2u);
v___x_3637_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3638_ = l_Lean_Name_num___override(v___x_3637_, v___x_3636_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3640_; uint8_t v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3640_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3641_ = 0;
v___x_3642_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3643_ = l_Lean_registerTraceClass(v___x_3640_, v___x_3641_, v___x_3642_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object* v_a_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
return v_res_3645_;
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
