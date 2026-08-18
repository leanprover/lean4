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
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonadExceptOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_instDecidableEqRaw___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_String_instHashableRaw_hash___boxed(lean_object*);
lean_object* l_Lean_MessageData_format___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BaseIO_toIO___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueString;
lean_object* l_Lean_Option_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringFormat___lam__0(lean_object*);
lean_object* l_IO_println___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "serve"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 235, 105, 39, 190, 159, 27, 75)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(178, 232, 14, 81, 31, 251, 216, 133)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "serve the `trace.profiler` data over HTTP and open it in `https://profiler.firefox.com`; blocks until interrupted with Ctrl+C"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_checkTraceOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 9, 140, 140, 215, 146, 186, 147)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 2, 1, 242, 207, 168, 68, 219)}};
static const lean_ctor_object l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(43, 90, 16, 252, 133, 113, 145, 70)}};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_serve;
LEAN_EXPORT uint8_t l_Lean_trace_profiler_isExporting(lean_object*);
LEAN_EXPORT lean_object* l_Lean_trace_profiler_isExporting___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResultExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultExpr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResultExpr___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResultExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResult___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResult___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResult___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0___redArg___boxed(lean_object*);
static const lean_ctor_object l_Lean_registerTraceClass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_registerTraceClass___closed__0 = (const lean_object*)&l_Lean_registerTraceClass___closed__0_value;
static const lean_string_object l_Lean_registerTraceClass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "enable/disable tracing for the given module and submodules"};
static const lean_object* l_Lean_registerTraceClass___closed__1 = (const lean_object*)&l_Lean_registerTraceClass___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedAction"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.isTracingEnabledFor"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "isTracingEnabledFor"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16_value;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
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
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___closed__0;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___closed__1;
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___lam__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHashableRaw_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___closed__2 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__10___closed__2_value;
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___lam__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableProd___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__10___closed__2_value),((lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__10___closed__2_value)} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___closed__3 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___lam__10___closed__3_value;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__10___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___closed__4;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__10___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___closed__5;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__10___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___closed__6;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_addTraceAsMessages___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v_cellCount_20_; lean_object* v___x_21_; 
v_cellCount_20_ = lean_unsigned_to_nat(16u);
v___x_21_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_20_);
return v___x_21_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_22_; lean_object* v___x_23_; 
v_cellCount_22_ = lean_unsigned_to_nat(16u);
v___x_23_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_22_);
return v___x_23_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_24_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
v___x_25_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__0_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v___x_25_);
lean_ctor_set(v___x_27_, 2, v___x_24_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__2_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_);
v___x_30_ = lean_st_mk_ref(v___x_29_);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2____boxed(lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
return v_res_33_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10));
v___x_61_ = l_Lean_mkAtom(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12);
v___x_63_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_64_ = lean_array_push(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14));
v___x_67_ = lean_string_utf8_byte_size(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14));
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_77_ = lean_box(0);
v___x_78_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19));
v___x_79_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16);
v___x_80_ = lean_box(2);
v___x_81_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_78_);
lean_ctor_set(v___x_81_, 3, v___x_77_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20);
v___x_83_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_84_ = lean_array_push(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21);
v___x_86_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_87_ = lean_box(2);
v___x_88_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_85_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22);
v___x_90_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_91_ = lean_array_push(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23);
v___x_93_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_94_ = lean_box(2);
v___x_95_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_93_);
lean_ctor_set(v___x_95_, 2, v___x_92_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24);
v___x_97_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_98_ = lean_array_push(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25);
v___x_100_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_101_ = lean_box(2);
v___x_102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___x_99_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26);
v___x_104_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_105_ = lean_array_push(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_106_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27);
v___x_107_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_108_ = lean_box(2);
v___x_109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_107_);
lean_ctor_set(v___x_109_, 2, v___x_106_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__28);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg___lam__0(lean_object* v_modifyTraceState_111_, lean_object* v_inst_112_, lean_object* v_f_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_apply_1(v_modifyTraceState_111_, v_f_113_);
v___x_115_ = lean_apply_2(v_inst_112_, lean_box(0), v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object* v_inst_116_, lean_object* v_inst_117_){
_start:
{
lean_object* v_modifyTraceState_118_; lean_object* v_getTraceState_119_; lean_object* v_getInheritedTraceOptions_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_130_; 
v_modifyTraceState_118_ = lean_ctor_get(v_inst_117_, 0);
v_getTraceState_119_ = lean_ctor_get(v_inst_117_, 1);
v_getInheritedTraceOptions_120_ = lean_ctor_get(v_inst_117_, 2);
v_isSharedCheck_130_ = !lean_is_exclusive(v_inst_117_);
if (v_isSharedCheck_130_ == 0)
{
v___x_122_ = v_inst_117_;
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_getInheritedTraceOptions_120_);
lean_inc(v_getTraceState_119_);
lean_inc(v_modifyTraceState_118_);
lean_dec(v_inst_117_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
lean_inc_n(v_inst_116_, 2);
v___f_124_ = lean_alloc_closure((void*)(l_Lean_instMonadTraceOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_124_, 0, v_modifyTraceState_118_);
lean_closure_set(v___f_124_, 1, v_inst_116_);
v___x_125_ = lean_apply_2(v_inst_116_, lean_box(0), v_getTraceState_119_);
v___x_126_ = lean_apply_2(v_inst_116_, lean_box(0), v_getInheritedTraceOptions_120_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 2, v___x_126_);
lean_ctor_set(v___x_122_, 1, v___x_125_);
lean_ctor_set(v___x_122_, 0, v___f_124_);
v___x_128_ = v___x_122_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___f_124_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift(lean_object* v_m_131_, lean_object* v_n_132_, lean_object* v_inst_133_, lean_object* v_inst_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_instMonadTraceOfMonadLift___redArg(v_inst_133_, v_inst_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__0(lean_object* v_toPure_136_, lean_object* v_____s_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_box(0);
v___x_139_ = lean_apply_2(v_toPure_136_, lean_box(0), v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__1(lean_object* v___x_140_, lean_object* v_toPure_141_, lean_object* v_r_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_140_);
v___x_144_ = lean_apply_2(v_toPure_141_, lean_box(0), v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__2(lean_object* v___f_145_, lean_object* v_inst_146_, lean_object* v_toBind_147_, lean_object* v___f_148_, lean_object* v_____do__lift_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_alloc_closure((void*)(l_IO_println___boxed), 4, 3);
lean_closure_set(v___x_150_, 0, lean_box(0));
lean_closure_set(v___x_150_, 1, v___f_145_);
lean_closure_set(v___x_150_, 2, v_____do__lift_149_);
v___x_151_ = lean_apply_2(v_inst_146_, lean_box(0), v___x_150_);
v___x_152_ = lean_apply_4(v_toBind_147_, lean_box(0), lean_box(0), v___x_151_, v___f_148_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__3(lean_object* v_inst_153_, lean_object* v_toBind_154_, lean_object* v___f_155_, lean_object* v_x_156_, lean_object* v_____s_157_){
_start:
{
lean_object* v_msg_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_msg_158_ = lean_ctor_get(v_x_156_, 1);
lean_inc_ref(v_msg_158_);
lean_dec_ref(v_x_156_);
v___x_159_ = lean_box(0);
v___x_160_ = lean_alloc_closure((void*)(l_Lean_MessageData_format___boxed), 3, 2);
lean_closure_set(v___x_160_, 0, v_msg_158_);
lean_closure_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_alloc_closure((void*)(l_BaseIO_toIO___boxed), 3, 2);
lean_closure_set(v___x_161_, 0, lean_box(0));
lean_closure_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_apply_2(v_inst_153_, lean_box(0), v___x_161_);
v___x_163_ = lean_apply_4(v_toBind_154_, lean_box(0), lean_box(0), v___x_162_, v___f_155_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4(lean_object* v_toPure_164_, lean_object* v___f_165_, lean_object* v_inst_166_, lean_object* v_toBind_167_, lean_object* v_inst_168_, lean_object* v___f_169_, lean_object* v_____do__lift_170_){
_start:
{
lean_object* v_traces_171_; lean_object* v___x_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_traces_171_ = lean_ctor_get(v_____do__lift_170_, 0);
v___x_172_ = lean_box(0);
v___f_173_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_173_, 0, v___x_172_);
lean_closure_set(v___f_173_, 1, v_toPure_164_);
lean_inc_n(v_toBind_167_, 2);
lean_inc(v_inst_166_);
v___f_174_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_174_, 0, v___f_165_);
lean_closure_set(v___f_174_, 1, v_inst_166_);
lean_closure_set(v___f_174_, 2, v_toBind_167_);
lean_closure_set(v___f_174_, 3, v___f_173_);
v___f_175_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__3), 5, 3);
lean_closure_set(v___f_175_, 0, v_inst_166_);
lean_closure_set(v___f_175_, 1, v_toBind_167_);
lean_closure_set(v___f_175_, 2, v___f_174_);
v___x_176_ = l_Lean_PersistentArray_forIn___redArg(v_inst_168_, v_traces_171_, v___x_172_, v___f_175_);
v___x_177_ = lean_apply_4(v_toBind_167_, lean_box(0), lean_box(0), v___x_176_, v___f_169_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4___boxed(lean_object* v_toPure_178_, lean_object* v___f_179_, lean_object* v_inst_180_, lean_object* v_toBind_181_, lean_object* v_inst_182_, lean_object* v___f_183_, lean_object* v_____do__lift_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_printTraces___redArg___lam__4(v_toPure_178_, v___f_179_, v_inst_180_, v_toBind_181_, v_inst_182_, v___f_183_, v_____do__lift_184_);
lean_dec_ref(v_____do__lift_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg(lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_inst_189_){
_start:
{
lean_object* v_toApplicative_190_; lean_object* v_toBind_191_; lean_object* v_getTraceState_192_; lean_object* v_toPure_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___x_197_; 
v_toApplicative_190_ = lean_ctor_get(v_inst_187_, 0);
v_toBind_191_ = lean_ctor_get(v_inst_187_, 1);
lean_inc_n(v_toBind_191_, 2);
v_getTraceState_192_ = lean_ctor_get(v_inst_188_, 1);
lean_inc(v_getTraceState_192_);
lean_dec_ref(v_inst_188_);
v_toPure_193_ = lean_ctor_get(v_toApplicative_190_, 1);
lean_inc_n(v_toPure_193_, 2);
v___f_194_ = ((lean_object*)(l_Lean_printTraces___redArg___closed__0));
v___f_195_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_195_, 0, v_toPure_193_);
v___f_196_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_196_, 0, v_toPure_193_);
lean_closure_set(v___f_196_, 1, v___f_194_);
lean_closure_set(v___f_196_, 2, v_inst_189_);
lean_closure_set(v___f_196_, 3, v_toBind_191_);
lean_closure_set(v___f_196_, 4, v_inst_187_);
lean_closure_set(v___f_196_, 5, v___f_195_);
v___x_197_ = lean_apply_4(v_toBind_191_, lean_box(0), lean_box(0), v_getTraceState_192_, v___f_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces(lean_object* v_m_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_printTraces___redArg(v_inst_199_, v_inst_200_, v_inst_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0(lean_object* v_x_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_unsigned_to_nat(32u);
v___x_205_ = lean_mk_empty_array_with_capacity(v___x_204_);
lean_dec_ref(v___x_205_);
v___x_206_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__2, &l_Lean_instInhabitedTraceState_default___closed__2_once, _init_l_Lean_instInhabitedTraceState_default___closed__2);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0___boxed(lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_resetTraceState___redArg___lam__0(v_x_207_);
lean_dec_ref(v_x_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg(lean_object* v_inst_210_){
_start:
{
lean_object* v_modifyTraceState_211_; lean_object* v___f_212_; lean_object* v___x_213_; 
v_modifyTraceState_211_ = lean_ctor_get(v_inst_210_, 0);
lean_inc(v_modifyTraceState_211_);
lean_dec_ref(v_inst_210_);
v___f_212_ = ((lean_object*)(l_Lean_resetTraceState___redArg___closed__0));
v___x_213_ = lean_apply_1(v_modifyTraceState_211_, v___f_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState(lean_object* v_m_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_resetTraceState___redArg(v_inst_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_m_217_, lean_object* v_query_218_, lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
lean_object* v_zero_222_; uint8_t v_isZero_223_; 
v_zero_222_ = lean_unsigned_to_nat(0u);
v_isZero_223_ = lean_nat_dec_eq(v_x_220_, v_zero_222_);
if (v_isZero_223_ == 1)
{
lean_dec(v_x_221_);
lean_dec(v_x_220_);
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v___x_224_; 
v___x_224_ = lean_box(2);
return v___x_224_;
}
else
{
lean_object* v_val_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
v_val_225_ = lean_ctor_get(v_x_219_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v_x_219_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_val_225_);
lean_dec(v_x_219_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_val_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v_keyArray_233_; lean_object* v_valueArray_234_; lean_object* v___x_235_; uint8_t v_isSome_236_; 
v_keyArray_233_ = lean_ctor_get(v_m_217_, 1);
v_valueArray_234_ = lean_ctor_get(v_m_217_, 2);
v___x_235_ = lean_array_fget_borrowed(v_keyArray_233_, v_x_221_);
v_isSome_236_ = lean_noption_is_some(v___x_235_);
if (v_isSome_236_ == 0)
{
lean_dec(v_x_220_);
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v_x_221_);
return v___x_237_;
}
else
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_x_221_);
v_val_238_ = lean_ctor_get(v_x_219_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v_x_219_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v_x_219_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_val_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_one_246_; lean_object* v_n_247_; lean_object* v___y_249_; 
v_one_246_ = lean_unsigned_to_nat(1u);
v_n_247_ = lean_nat_sub(v_x_220_, v_one_246_);
lean_dec(v_x_220_);
if (v_isSome_236_ == 0)
{
goto v___jp_255_;
}
else
{
lean_object* v___x_257_; uint8_t v_isSome_258_; 
v___x_257_ = lean_array_fget_borrowed(v_valueArray_234_, v_x_221_);
v_isSome_258_ = lean_noption_is_some(v___x_257_);
if (v_isSome_258_ == 0)
{
goto v___jp_255_;
}
else
{
lean_object* v_val_259_; uint8_t v___x_260_; 
lean_inc(v___x_235_);
v_val_259_ = lean_noption_get(v___x_235_);
v___x_260_ = lean_name_eq(v_val_259_, v_query_218_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
lean_dec(v_val_259_);
v___x_261_ = lean_array_get_size(v_keyArray_233_);
v___x_262_ = lean_nat_add(v_x_221_, v_one_246_);
lean_dec(v_x_221_);
v___x_263_ = lean_nat_dec_lt(v___x_262_, v___x_261_);
if (v___x_263_ == 0)
{
lean_dec(v___x_262_);
v_x_220_ = v_n_247_;
v_x_221_ = v_zero_222_;
goto _start;
}
else
{
v_x_220_ = v_n_247_;
v_x_221_ = v___x_262_;
goto _start;
}
}
else
{
lean_object* v_val_266_; lean_object* v___x_267_; 
lean_dec(v_n_247_);
lean_dec(v_x_219_);
lean_inc(v___x_257_);
v_val_266_ = lean_noption_get(v___x_257_);
v___x_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_267_, 0, v_x_221_);
lean_ctor_set(v___x_267_, 1, v_val_259_);
lean_ctor_set(v___x_267_, 2, v_val_266_);
return v___x_267_;
}
}
}
v___jp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_250_ = lean_array_get_size(v_keyArray_233_);
v___x_251_ = lean_nat_add(v_x_221_, v_one_246_);
lean_dec(v_x_221_);
v___x_252_ = lean_nat_dec_lt(v___x_251_, v___x_250_);
if (v___x_252_ == 0)
{
lean_dec(v___x_251_);
v_x_219_ = v___y_249_;
v_x_220_ = v_n_247_;
v_x_221_ = v_zero_222_;
goto _start;
}
else
{
v_x_219_ = v___y_249_;
v_x_220_ = v_n_247_;
v_x_221_ = v___x_251_;
goto _start;
}
}
v___jp_255_:
{
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v___x_256_; 
lean_inc(v_x_221_);
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v_x_221_);
v___y_249_ = v___x_256_;
goto v___jp_248_;
}
else
{
v___y_249_ = v_x_219_;
goto v___jp_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_m_268_, lean_object* v_query_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_268_, v_query_269_, v_x_270_, v_x_271_, v_x_272_);
lean_dec(v_query_269_);
lean_dec_ref(v_m_268_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___redArg(lean_object* v_m_274_, lean_object* v_query_275_){
_start:
{
lean_object* v_keyArray_276_; lean_object* v___x_277_; uint64_t v___y_279_; 
v_keyArray_276_ = lean_ctor_get(v_m_274_, 1);
v___x_277_ = lean_array_get_size(v_keyArray_276_);
if (lean_obj_tag(v_query_275_) == 0)
{
uint64_t v___x_294_; 
v___x_294_ = 1723ULL;
v___y_279_ = v___x_294_;
goto v___jp_278_;
}
else
{
uint64_t v_hash_295_; 
v_hash_295_ = lean_ctor_get_uint64(v_query_275_, sizeof(void*)*2);
v___y_279_ = v_hash_295_;
goto v___jp_278_;
}
v___jp_278_:
{
uint64_t v___x_280_; uint64_t v___x_281_; uint64_t v_fold_282_; uint64_t v___x_283_; uint64_t v___x_284_; uint64_t v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_280_ = 32ULL;
v___x_281_ = lean_uint64_shift_right(v___y_279_, v___x_280_);
v_fold_282_ = lean_uint64_xor(v___y_279_, v___x_281_);
v___x_283_ = 16ULL;
v___x_284_ = lean_uint64_shift_right(v_fold_282_, v___x_283_);
v___x_285_ = lean_uint64_xor(v_fold_282_, v___x_284_);
v___x_286_ = lean_uint64_to_usize(v___x_285_);
v___x_287_ = lean_usize_of_nat(v___x_277_);
v___x_288_ = ((size_t)1ULL);
v___x_289_ = lean_usize_sub(v___x_287_, v___x_288_);
v___x_290_ = lean_usize_land(v___x_286_, v___x_289_);
v___x_291_ = lean_usize_to_nat(v___x_290_);
v___x_292_ = lean_box(0);
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_274_, v_query_275_, v___x_292_, v___x_277_, v___x_291_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_296_, lean_object* v_query_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___redArg(v_m_296_, v_query_297_);
lean_dec(v_query_297_);
lean_dec_ref(v_m_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(lean_object* v_m_299_, lean_object* v_query_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___redArg(v_m_299_, v_query_300_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_index_302_; lean_object* v_key_303_; lean_object* v_value_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
v_index_302_ = lean_ctor_get(v___x_301_, 0);
v_key_303_ = lean_ctor_get(v___x_301_, 1);
v_value_304_ = lean_ctor_get(v___x_301_, 2);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_301_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_value_304_);
lean_inc(v_key_303_);
lean_inc(v_index_302_);
lean_dec(v___x_301_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_index_302_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_key_303_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_value_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
else
{
lean_object* v___x_312_; 
lean_dec(v___x_301_);
v___x_312_ = lean_box(1);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_313_, lean_object* v_query_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_m_313_, v_query_314_);
lean_dec(v_query_314_);
lean_dec_ref(v_m_313_);
return v_res_315_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(lean_object* v_m_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_m_316_, v_a_317_);
if (lean_obj_tag(v___x_318_) == 0)
{
uint8_t v___x_319_; 
lean_dec_ref_known(v___x_318_, 3);
v___x_319_ = 1;
return v___x_319_;
}
else
{
uint8_t v___x_320_; 
v___x_320_ = 0;
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___boxed(lean_object* v_m_321_, lean_object* v_a_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_m_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object* v_inherited_325_, lean_object* v_opts_326_, lean_object* v_opt_327_){
_start:
{
lean_object* v_map_333_; lean_object* v___x_334_; 
v_map_333_ = lean_ctor_get(v_opts_326_, 0);
v___x_334_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_333_, v_opt_327_);
if (lean_obj_tag(v___x_334_) == 0)
{
goto v___jp_328_;
}
else
{
lean_object* v_val_335_; 
v_val_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v___x_334_, 1);
if (lean_obj_tag(v_val_335_) == 1)
{
uint8_t v_v_336_; 
v_v_336_ = lean_ctor_get_uint8(v_val_335_, 0);
lean_dec_ref_known(v_val_335_, 0);
return v_v_336_;
}
else
{
lean_dec(v_val_335_);
goto v___jp_328_;
}
}
v___jp_328_:
{
if (lean_obj_tag(v_opt_327_) == 1)
{
lean_object* v_pre_329_; uint8_t v___x_330_; 
v_pre_329_ = lean_ctor_get(v_opt_327_, 0);
v___x_330_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_inherited_325_, v_opt_327_);
if (v___x_330_ == 0)
{
return v___x_330_;
}
else
{
v_opt_327_ = v_pre_329_;
goto _start;
}
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go___boxed(lean_object* v_inherited_337_, lean_object* v_opts_338_, lean_object* v_opt_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_337_, v_opts_338_, v_opt_339_);
lean_dec(v_opt_339_);
lean_dec_ref(v_opts_338_);
lean_dec_ref(v_inherited_337_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(lean_object* v_00_u03b2_342_, lean_object* v_m_343_, lean_object* v_a_344_){
_start:
{
uint8_t v___x_345_; 
v___x_345_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_343_, v_a_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(lean_object* v_00_u03b2_346_, lean_object* v_m_347_, lean_object* v_a_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(v_00_u03b2_346_, v_m_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_m_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(lean_object* v_00_u03b2_351_, lean_object* v_m_352_, lean_object* v_query_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_m_352_, v_query_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_355_, lean_object* v_m_356_, lean_object* v_query_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(v_00_u03b2_355_, v_m_356_, v_query_357_);
lean_dec(v_query_357_);
lean_dec_ref(v_m_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_359_, lean_object* v_m_360_, lean_object* v_query_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___redArg(v_m_360_, v_query_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_363_, lean_object* v_m_364_, lean_object* v_query_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1(v_00_u03b2_363_, v_m_364_, v_query_365_);
lean_dec(v_query_365_);
lean_dec_ref(v_m_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_367_, lean_object* v_m_368_, lean_object* v_query_369_, lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_368_, v_query_369_, v_x_370_, v_x_371_, v_x_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_375_, lean_object* v_m_376_, lean_object* v_query_377_, lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_375_, v_m_376_, v_query_377_, v_x_378_, v_x_379_, v_x_380_, v_x_381_);
lean_dec(v_query_377_);
lean_dec_ref(v_m_376_);
return v_res_382_;
}
}
LEAN_EXPORT uint8_t l_Lean_checkTraceOption(lean_object* v_inherited_386_, lean_object* v_opts_387_, lean_object* v_cls_388_){
_start:
{
uint8_t v_hasTrace_389_; 
v_hasTrace_389_ = lean_ctor_get_uint8(v_opts_387_, sizeof(void*)*1);
if (v_hasTrace_389_ == 0)
{
lean_dec(v_cls_388_);
return v_hasTrace_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_390_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_391_ = l_Lean_Name_append(v___x_390_, v_cls_388_);
v___x_392_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_386_, v_opts_387_, v___x_391_);
lean_dec(v___x_391_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkTraceOption___boxed(lean_object* v_inherited_393_, lean_object* v_opts_394_, lean_object* v_cls_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Lean_checkTraceOption(v_inherited_393_, v_opts_394_, v_cls_395_);
lean_dec_ref(v_opts_394_);
lean_dec_ref(v_inherited_393_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0(lean_object* v_toPure_398_, lean_object* v_cls_399_, lean_object* v_____do__lift_400_, lean_object* v_____do__lift_401_){
_start:
{
uint8_t v_hasTrace_402_; 
v_hasTrace_402_ = lean_ctor_get_uint8(v_____do__lift_401_, sizeof(void*)*1);
if (v_hasTrace_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_cls_399_);
v___x_403_ = lean_box(v_hasTrace_402_);
v___x_404_ = lean_apply_2(v_toPure_398_, lean_box(0), v___x_403_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_405_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_406_ = l_Lean_Name_append(v___x_405_, v_cls_399_);
v___x_407_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_400_, v_____do__lift_401_, v___x_406_);
lean_dec(v___x_406_);
v___x_408_ = lean_box(v___x_407_);
v___x_409_ = lean_apply_2(v_toPure_398_, lean_box(0), v___x_408_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0___boxed(lean_object* v_toPure_410_, lean_object* v_cls_411_, lean_object* v_____do__lift_412_, lean_object* v_____do__lift_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_isTracingEnabledFor___redArg___lam__0(v_toPure_410_, v_cls_411_, v_____do__lift_412_, v_____do__lift_413_);
lean_dec_ref(v_____do__lift_413_);
lean_dec_ref(v_____do__lift_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__1(lean_object* v_toPure_415_, lean_object* v_cls_416_, lean_object* v_toBind_417_, lean_object* v_inst_418_, lean_object* v_____do__lift_419_){
_start:
{
lean_object* v___f_420_; lean_object* v___x_421_; 
v___f_420_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_420_, 0, v_toPure_415_);
lean_closure_set(v___f_420_, 1, v_cls_416_);
lean_closure_set(v___f_420_, 2, v_____do__lift_419_);
v___x_421_ = lean_apply_4(v_toBind_417_, lean_box(0), lean_box(0), v_inst_418_, v___f_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_cls_425_){
_start:
{
lean_object* v_toApplicative_426_; lean_object* v_toBind_427_; lean_object* v_getInheritedTraceOptions_428_; lean_object* v_toPure_429_; lean_object* v___f_430_; lean_object* v___x_431_; 
v_toApplicative_426_ = lean_ctor_get(v_inst_422_, 0);
lean_inc_ref(v_toApplicative_426_);
v_toBind_427_ = lean_ctor_get(v_inst_422_, 1);
lean_inc_n(v_toBind_427_, 2);
lean_dec_ref(v_inst_422_);
v_getInheritedTraceOptions_428_ = lean_ctor_get(v_inst_423_, 2);
lean_inc(v_getInheritedTraceOptions_428_);
lean_dec_ref(v_inst_423_);
v_toPure_429_ = lean_ctor_get(v_toApplicative_426_, 1);
lean_inc(v_toPure_429_);
lean_dec_ref(v_toApplicative_426_);
v___f_430_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_430_, 0, v_toPure_429_);
lean_closure_set(v___f_430_, 1, v_cls_425_);
lean_closure_set(v___f_430_, 2, v_toBind_427_);
lean_closure_set(v___f_430_, 3, v_inst_424_);
v___x_431_ = lean_apply_4(v_toBind_427_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_428_, v___f_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor(lean_object* v_m_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_cls_436_){
_start:
{
lean_object* v_toApplicative_437_; lean_object* v_toBind_438_; lean_object* v_getInheritedTraceOptions_439_; lean_object* v_toPure_440_; lean_object* v___f_441_; lean_object* v___x_442_; 
v_toApplicative_437_ = lean_ctor_get(v_inst_433_, 0);
lean_inc_ref(v_toApplicative_437_);
v_toBind_438_ = lean_ctor_get(v_inst_433_, 1);
lean_inc_n(v_toBind_438_, 2);
lean_dec_ref(v_inst_433_);
v_getInheritedTraceOptions_439_ = lean_ctor_get(v_inst_434_, 2);
lean_inc(v_getInheritedTraceOptions_439_);
lean_dec_ref(v_inst_434_);
v_toPure_440_ = lean_ctor_get(v_toApplicative_437_, 1);
lean_inc(v_toPure_440_);
lean_dec_ref(v_toApplicative_437_);
v___f_441_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_441_, 0, v_toPure_440_);
lean_closure_set(v___f_441_, 1, v_cls_436_);
lean_closure_set(v___f_441_, 2, v_toBind_438_);
lean_closure_set(v___f_441_, 3, v_inst_435_);
v___x_442_ = lean_apply_4(v_toBind_438_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_439_, v___f_441_);
return v___x_442_;
}
}
LEAN_EXPORT uint8_t lean_is_trace_class_enabled(lean_object* v_opts_443_, lean_object* v_cls_444_){
_start:
{
uint8_t v_hasTrace_446_; 
v_hasTrace_446_ = lean_ctor_get_uint8(v_opts_443_, sizeof(void*)*1);
if (v_hasTrace_446_ == 0)
{
lean_dec(v_cls_444_);
lean_dec_ref(v_opts_443_);
return v_hasTrace_446_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_447_ = l_Lean_inheritedTraceOptions;
v___x_448_ = lean_st_ref_get(v___x_447_);
v___x_449_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_450_ = l_Lean_Name_append(v___x_449_, v_cls_444_);
v___x_451_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_448_, v_opts_443_, v___x_450_);
lean_dec(v___x_450_);
lean_dec_ref(v_opts_443_);
lean_dec(v___x_448_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object* v_opts_452_, lean_object* v_cls_453_, lean_object* v_a_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = lean_is_trace_class_enabled(v_opts_452_, v_cls_453_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object* v_toPure_457_, lean_object* v_s_458_){
_start:
{
lean_object* v_traces_459_; lean_object* v___x_460_; 
v_traces_459_ = lean_ctor_get(v_s_458_, 0);
lean_inc_ref(v_traces_459_);
lean_dec_ref(v_s_458_);
v___x_460_ = lean_apply_2(v_toPure_457_, lean_box(0), v_traces_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object* v_inst_461_, lean_object* v_inst_462_){
_start:
{
lean_object* v_toApplicative_463_; lean_object* v_toBind_464_; lean_object* v_getTraceState_465_; lean_object* v_toPure_466_; lean_object* v___f_467_; lean_object* v___x_468_; 
v_toApplicative_463_ = lean_ctor_get(v_inst_461_, 0);
lean_inc_ref(v_toApplicative_463_);
v_toBind_464_ = lean_ctor_get(v_inst_461_, 1);
lean_inc(v_toBind_464_);
lean_dec_ref(v_inst_461_);
v_getTraceState_465_ = lean_ctor_get(v_inst_462_, 1);
lean_inc(v_getTraceState_465_);
lean_dec_ref(v_inst_462_);
v_toPure_466_ = lean_ctor_get(v_toApplicative_463_, 1);
lean_inc(v_toPure_466_);
lean_dec_ref(v_toApplicative_463_);
v___f_467_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_467_, 0, v_toPure_466_);
v___x_468_ = lean_apply_4(v_toBind_464_, lean_box(0), lean_box(0), v_getTraceState_465_, v___f_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object* v_m_469_, lean_object* v_inst_470_, lean_object* v_inst_471_){
_start:
{
lean_object* v_toApplicative_472_; lean_object* v_toBind_473_; lean_object* v_getTraceState_474_; lean_object* v_toPure_475_; lean_object* v___f_476_; lean_object* v___x_477_; 
v_toApplicative_472_ = lean_ctor_get(v_inst_470_, 0);
lean_inc_ref(v_toApplicative_472_);
v_toBind_473_ = lean_ctor_get(v_inst_470_, 1);
lean_inc(v_toBind_473_);
lean_dec_ref(v_inst_470_);
v_getTraceState_474_ = lean_ctor_get(v_inst_471_, 1);
lean_inc(v_getTraceState_474_);
lean_dec_ref(v_inst_471_);
v_toPure_475_ = lean_ctor_get(v_toApplicative_472_, 1);
lean_inc(v_toPure_475_);
lean_dec_ref(v_toApplicative_472_);
v___f_476_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_476_, 0, v_toPure_475_);
v___x_477_ = lean_apply_4(v_toBind_473_, lean_box(0), lean_box(0), v_getTraceState_474_, v___f_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object* v_f_478_, lean_object* v_s_479_){
_start:
{
uint64_t v_tid_480_; lean_object* v_traces_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
v_tid_480_ = lean_ctor_get_uint64(v_s_479_, sizeof(void*)*1);
v_traces_481_ = lean_ctor_get(v_s_479_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_s_479_);
if (v_isSharedCheck_489_ == 0)
{
v___x_483_ = v_s_479_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_traces_481_);
lean_dec(v_s_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = lean_apply_1(v_f_478_, v_traces_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
lean_ctor_set_uint64(v_reuseFailAlloc_488_, sizeof(void*)*1, v_tid_480_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object* v_inst_490_, lean_object* v_f_491_){
_start:
{
lean_object* v_modifyTraceState_492_; lean_object* v___f_493_; lean_object* v___x_494_; 
v_modifyTraceState_492_ = lean_ctor_get(v_inst_490_, 0);
lean_inc(v_modifyTraceState_492_);
lean_dec_ref(v_inst_490_);
v___f_493_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_493_, 0, v_f_491_);
v___x_494_ = lean_apply_1(v_modifyTraceState_492_, v___f_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object* v_m_495_, lean_object* v_inst_496_, lean_object* v_f_497_){
_start:
{
lean_object* v_modifyTraceState_498_; lean_object* v___f_499_; lean_object* v___x_500_; 
v_modifyTraceState_498_ = lean_ctor_get(v_inst_496_, 0);
lean_inc(v_modifyTraceState_498_);
lean_dec_ref(v_inst_496_);
v___f_499_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_499_, 0, v_f_497_);
v___x_500_ = lean_apply_1(v_modifyTraceState_498_, v___f_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object* v_s_501_, lean_object* v_x_502_){
_start:
{
lean_inc_ref(v_s_501_);
return v_s_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object* v_s_503_, lean_object* v_x_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_setTraceState___redArg___lam__0(v_s_503_, v_x_504_);
lean_dec_ref(v_x_504_);
lean_dec_ref(v_s_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object* v_inst_506_, lean_object* v_s_507_){
_start:
{
lean_object* v_modifyTraceState_508_; lean_object* v___f_509_; lean_object* v___x_510_; 
v_modifyTraceState_508_ = lean_ctor_get(v_inst_506_, 0);
lean_inc(v_modifyTraceState_508_);
lean_dec_ref(v_inst_506_);
v___f_509_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_509_, 0, v_s_507_);
v___x_510_ = lean_apply_1(v_modifyTraceState_508_, v___f_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object* v_m_511_, lean_object* v_inst_512_, lean_object* v_s_513_){
_start:
{
lean_object* v_modifyTraceState_514_; lean_object* v___f_515_; lean_object* v___x_516_; 
v_modifyTraceState_514_ = lean_ctor_get(v_inst_512_, 0);
lean_inc(v_modifyTraceState_514_);
lean_dec_ref(v_inst_512_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_515_, 0, v_s_513_);
v___x_516_ = lean_apply_1(v_modifyTraceState_514_, v___f_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object* v_s_517_){
_start:
{
uint64_t v_tid_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_528_; 
v_tid_518_ = lean_ctor_get_uint64(v_s_517_, sizeof(void*)*1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_s_517_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v_s_517_, 0);
lean_dec(v_unused_529_);
v___x_520_ = v_s_517_;
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
else
{
lean_dec(v_s_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_522_ = lean_unsigned_to_nat(32u);
v___x_523_ = lean_mk_empty_array_with_capacity(v___x_522_);
lean_dec_ref(v___x_523_);
v___x_524_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__1, &l_Lean_instInhabitedTraceState_default___closed__1_once, _init_l_Lean_instInhabitedTraceState_default___closed__1);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_524_);
v___x_526_ = v___x_520_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
lean_ctor_set_uint64(v_reuseFailAlloc_527_, sizeof(void*)*1, v_tid_518_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object* v_toPure_530_, lean_object* v_oldTraces_531_, lean_object* v_____r_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_apply_2(v_toPure_530_, lean_box(0), v_oldTraces_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object* v_toPure_534_, lean_object* v_modifyTraceState_535_, lean_object* v___f_536_, lean_object* v_toBind_537_, lean_object* v_oldTraces_538_){
_start:
{
lean_object* v___f_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___f_539_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_539_, 0, v_toPure_534_);
lean_closure_set(v___f_539_, 1, v_oldTraces_538_);
v___x_540_ = lean_apply_1(v_modifyTraceState_535_, v___f_536_);
v___x_541_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_540_, v___f_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object* v_inst_543_, lean_object* v_inst_544_){
_start:
{
lean_object* v_toApplicative_545_; lean_object* v_toBind_546_; lean_object* v_modifyTraceState_547_; lean_object* v_getTraceState_548_; lean_object* v_toPure_549_; lean_object* v___f_550_; lean_object* v___f_551_; lean_object* v___f_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_toApplicative_545_ = lean_ctor_get(v_inst_543_, 0);
lean_inc_ref(v_toApplicative_545_);
v_toBind_546_ = lean_ctor_get(v_inst_543_, 1);
lean_inc_n(v_toBind_546_, 3);
lean_dec_ref(v_inst_543_);
v_modifyTraceState_547_ = lean_ctor_get(v_inst_544_, 0);
lean_inc(v_modifyTraceState_547_);
v_getTraceState_548_ = lean_ctor_get(v_inst_544_, 1);
lean_inc(v_getTraceState_548_);
lean_dec_ref(v_inst_544_);
v_toPure_549_ = lean_ctor_get(v_toApplicative_545_, 1);
lean_inc_n(v_toPure_549_, 2);
lean_dec_ref(v_toApplicative_545_);
v___f_550_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0));
v___f_551_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_551_, 0, v_toPure_549_);
lean_closure_set(v___f_551_, 1, v_modifyTraceState_547_);
lean_closure_set(v___f_551_, 2, v___f_550_);
lean_closure_set(v___f_551_, 3, v_toBind_546_);
v___f_552_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_552_, 0, v_toPure_549_);
v___x_553_ = lean_apply_4(v_toBind_546_, lean_box(0), lean_box(0), v_getTraceState_548_, v___f_552_);
v___x_554_ = lean_apply_4(v_toBind_546_, lean_box(0), lean_box(0), v___x_553_, v___f_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object* v_m_555_, lean_object* v_inst_556_, lean_object* v_inst_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_556_, v_inst_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object* v_ref_559_, lean_object* v_msg_560_, lean_object* v_s_561_){
_start:
{
uint64_t v_tid_562_; lean_object* v_traces_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_572_; 
v_tid_562_ = lean_ctor_get_uint64(v_s_561_, sizeof(void*)*1);
v_traces_563_ = lean_ctor_get(v_s_561_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v_s_561_);
if (v_isSharedCheck_572_ == 0)
{
v___x_565_ = v_s_561_;
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_traces_563_);
lean_dec(v_s_561_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v_ref_559_);
lean_ctor_set(v___x_567_, 1, v_msg_560_);
v___x_568_ = l_Lean_PersistentArray_push___redArg(v_traces_563_, v___x_567_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_568_);
v___x_570_ = v___x_565_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
lean_ctor_set_uint64(v_reuseFailAlloc_571_, sizeof(void*)*1, v_tid_562_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object* v_inst_573_, lean_object* v_ref_574_, lean_object* v_msg_575_){
_start:
{
lean_object* v_modifyTraceState_576_; lean_object* v___f_577_; lean_object* v___x_578_; 
v_modifyTraceState_576_ = lean_ctor_get(v_inst_573_, 0);
lean_inc(v_modifyTraceState_576_);
lean_dec_ref(v_inst_573_);
v___f_577_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__0), 3, 2);
lean_closure_set(v___f_577_, 0, v_ref_574_);
lean_closure_set(v___f_577_, 1, v_msg_575_);
v___x_578_ = lean_apply_1(v_modifyTraceState_576_, v___f_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_msg_581_, lean_object* v_toBind_582_, lean_object* v_ref_583_){
_start:
{
lean_object* v___f_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___f_584_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__1), 3, 2);
lean_closure_set(v___f_584_, 0, v_inst_579_);
lean_closure_set(v___f_584_, 1, v_ref_583_);
v___x_585_ = lean_apply_1(v_inst_580_, v_msg_581_);
v___x_586_ = lean_apply_4(v_toBind_582_, lean_box(0), lean_box(0), v___x_585_, v___f_584_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_inst_590_, lean_object* v_msg_591_){
_start:
{
lean_object* v_toBind_592_; lean_object* v_getRef_593_; lean_object* v___f_594_; lean_object* v___x_595_; 
v_toBind_592_ = lean_ctor_get(v_inst_587_, 1);
lean_inc_n(v_toBind_592_, 2);
lean_dec_ref(v_inst_587_);
v_getRef_593_ = lean_ctor_get(v_inst_589_, 0);
lean_inc(v_getRef_593_);
lean_dec_ref(v_inst_589_);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__2), 5, 4);
lean_closure_set(v___f_594_, 0, v_inst_588_);
lean_closure_set(v___f_594_, 1, v_inst_590_);
lean_closure_set(v___f_594_, 2, v_msg_591_);
lean_closure_set(v___f_594_, 3, v_toBind_592_);
v___x_595_ = lean_apply_4(v_toBind_592_, lean_box(0), lean_box(0), v_getRef_593_, v___f_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object* v_m_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_msg_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_addRawTrace___redArg(v_inst_597_, v_inst_598_, v_inst_599_, v_inst_600_, v_msg_601_);
return v___x_602_;
}
}
static double _init_l_Lean_addTrace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_603_; double v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_float_of_nat(v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object* v_cls_608_, lean_object* v_msg_609_, lean_object* v_ref_610_, lean_object* v_s_611_){
_start:
{
uint64_t v_tid_612_; lean_object* v_traces_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_629_; 
v_tid_612_ = lean_ctor_get_uint64(v_s_611_, sizeof(void*)*1);
v_traces_613_ = lean_ctor_get(v_s_611_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_s_611_);
if (v_isSharedCheck_629_ == 0)
{
v___x_615_ = v_s_611_;
v_isShared_616_ = v_isSharedCheck_629_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_traces_613_);
lean_dec(v_s_611_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_629_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; double v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_617_ = lean_box(0);
v___x_618_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
v___x_619_ = 0;
v___x_620_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_621_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_621_, 0, v_cls_608_);
lean_ctor_set(v___x_621_, 1, v___x_617_);
lean_ctor_set(v___x_621_, 2, v___x_620_);
lean_ctor_set_float(v___x_621_, sizeof(void*)*3, v___x_618_);
lean_ctor_set_float(v___x_621_, sizeof(void*)*3 + 8, v___x_618_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*3 + 16, v___x_619_);
v___x_622_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
v___x_623_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v_msg_609_);
lean_ctor_set(v___x_623_, 2, v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v_ref_610_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Lean_PersistentArray_push___redArg(v_traces_613_, v___x_624_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_625_);
v___x_627_ = v___x_615_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
lean_ctor_set_uint64(v_reuseFailAlloc_628_, sizeof(void*)*1, v_tid_612_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object* v_inst_630_, lean_object* v_cls_631_, lean_object* v_ref_632_, lean_object* v_msg_633_){
_start:
{
lean_object* v_modifyTraceState_634_; lean_object* v___f_635_; lean_object* v___x_636_; 
v_modifyTraceState_634_ = lean_ctor_get(v_inst_630_, 0);
lean_inc(v_modifyTraceState_634_);
lean_dec_ref(v_inst_630_);
v___f_635_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_635_, 0, v_cls_631_);
lean_closure_set(v___f_635_, 1, v_msg_633_);
lean_closure_set(v___f_635_, 2, v_ref_632_);
v___x_636_ = lean_apply_1(v_modifyTraceState_634_, v___f_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object* v_inst_637_, lean_object* v_cls_638_, lean_object* v_inst_639_, lean_object* v_msg_640_, lean_object* v_toBind_641_, lean_object* v_ref_642_){
_start:
{
lean_object* v___f_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___f_643_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__1), 4, 3);
lean_closure_set(v___f_643_, 0, v_inst_637_);
lean_closure_set(v___f_643_, 1, v_cls_638_);
lean_closure_set(v___f_643_, 2, v_ref_642_);
v___x_644_ = lean_apply_1(v_inst_639_, v_msg_640_);
v___x_645_ = lean_apply_4(v_toBind_641_, lean_box(0), lean_box(0), v___x_644_, v___f_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_cls_650_, lean_object* v_msg_651_){
_start:
{
lean_object* v_toBind_652_; lean_object* v_getRef_653_; lean_object* v___f_654_; lean_object* v___x_655_; 
v_toBind_652_ = lean_ctor_get(v_inst_646_, 1);
lean_inc_n(v_toBind_652_, 2);
lean_dec_ref(v_inst_646_);
v_getRef_653_ = lean_ctor_get(v_inst_648_, 0);
lean_inc(v_getRef_653_);
lean_dec_ref(v_inst_648_);
v___f_654_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__2), 6, 5);
lean_closure_set(v___f_654_, 0, v_inst_647_);
lean_closure_set(v___f_654_, 1, v_cls_650_);
lean_closure_set(v___f_654_, 2, v_inst_649_);
lean_closure_set(v___f_654_, 3, v_msg_651_);
lean_closure_set(v___f_654_, 4, v_toBind_652_);
v___x_655_ = lean_apply_4(v_toBind_652_, lean_box(0), lean_box(0), v_getRef_653_, v___f_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object* v_m_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_cls_661_, lean_object* v_msg_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_addTrace___redArg(v_inst_657_, v_inst_658_, v_inst_659_, v_inst_660_, v_cls_661_, v_msg_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0(lean_object* v_toPure_664_, lean_object* v_msg_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_cls_670_, uint8_t v_____do__lift_671_){
_start:
{
if (v_____do__lift_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec(v_cls_670_);
lean_dec(v_inst_669_);
lean_dec_ref(v_inst_668_);
lean_dec_ref(v_inst_667_);
lean_dec_ref(v_inst_666_);
lean_dec_ref(v_msg_665_);
v___x_672_ = lean_box(0);
v___x_673_ = lean_apply_2(v_toPure_664_, lean_box(0), v___x_672_);
return v___x_673_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v_toPure_664_);
v___x_674_ = lean_box(0);
v___x_675_ = lean_apply_1(v_msg_665_, v___x_674_);
v___x_676_ = l_Lean_addTrace___redArg(v_inst_666_, v_inst_667_, v_inst_668_, v_inst_669_, v_cls_670_, v___x_675_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object* v_toPure_677_, lean_object* v_msg_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_cls_683_, lean_object* v_____do__lift_684_){
_start:
{
uint8_t v_____do__lift_148__boxed_685_; lean_object* v_res_686_; 
v_____do__lift_148__boxed_685_ = lean_unbox(v_____do__lift_684_);
v_res_686_ = l_Lean_trace___redArg___lam__0(v_toPure_677_, v_msg_678_, v_inst_679_, v_inst_680_, v_inst_681_, v_inst_682_, v_cls_683_, v_____do__lift_148__boxed_685_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_cls_692_, lean_object* v_msg_693_){
_start:
{
lean_object* v_toApplicative_694_; lean_object* v_toBind_695_; lean_object* v_getInheritedTraceOptions_696_; lean_object* v_toPure_697_; lean_object* v___f_698_; lean_object* v___f_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_toApplicative_694_ = lean_ctor_get(v_inst_687_, 0);
v_toBind_695_ = lean_ctor_get(v_inst_687_, 1);
lean_inc_n(v_toBind_695_, 3);
v_getInheritedTraceOptions_696_ = lean_ctor_get(v_inst_688_, 2);
lean_inc(v_getInheritedTraceOptions_696_);
v_toPure_697_ = lean_ctor_get(v_toApplicative_694_, 1);
lean_inc_n(v_toPure_697_, 2);
lean_inc(v_cls_692_);
v___f_698_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_698_, 0, v_toPure_697_);
lean_closure_set(v___f_698_, 1, v_msg_693_);
lean_closure_set(v___f_698_, 2, v_inst_687_);
lean_closure_set(v___f_698_, 3, v_inst_688_);
lean_closure_set(v___f_698_, 4, v_inst_689_);
lean_closure_set(v___f_698_, 5, v_inst_690_);
lean_closure_set(v___f_698_, 6, v_cls_692_);
v___f_699_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_699_, 0, v_toPure_697_);
lean_closure_set(v___f_699_, 1, v_cls_692_);
lean_closure_set(v___f_699_, 2, v_toBind_695_);
lean_closure_set(v___f_699_, 3, v_inst_691_);
v___x_700_ = lean_apply_4(v_toBind_695_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_696_, v___f_699_);
v___x_701_ = lean_apply_4(v_toBind_695_, lean_box(0), lean_box(0), v___x_700_, v___f_698_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace(lean_object* v_m_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_cls_708_, lean_object* v_msg_709_){
_start:
{
lean_object* v_toApplicative_710_; lean_object* v_toBind_711_; lean_object* v_getInheritedTraceOptions_712_; lean_object* v_toPure_713_; lean_object* v___f_714_; lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_toApplicative_710_ = lean_ctor_get(v_inst_703_, 0);
v_toBind_711_ = lean_ctor_get(v_inst_703_, 1);
lean_inc_n(v_toBind_711_, 3);
v_getInheritedTraceOptions_712_ = lean_ctor_get(v_inst_704_, 2);
lean_inc(v_getInheritedTraceOptions_712_);
v_toPure_713_ = lean_ctor_get(v_toApplicative_710_, 1);
lean_inc_n(v_toPure_713_, 2);
lean_inc(v_cls_708_);
v___f_714_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_714_, 0, v_toPure_713_);
lean_closure_set(v___f_714_, 1, v_msg_709_);
lean_closure_set(v___f_714_, 2, v_inst_703_);
lean_closure_set(v___f_714_, 3, v_inst_704_);
lean_closure_set(v___f_714_, 4, v_inst_705_);
lean_closure_set(v___f_714_, 5, v_inst_706_);
lean_closure_set(v___f_714_, 6, v_cls_708_);
v___f_715_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_715_, 0, v_toPure_713_);
lean_closure_set(v___f_715_, 1, v_cls_708_);
lean_closure_set(v___f_715_, 2, v_toBind_711_);
lean_closure_set(v___f_715_, 3, v_inst_707_);
v___x_716_ = lean_apply_4(v_toBind_711_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_712_, v___f_715_);
v___x_717_ = lean_apply_4(v_toBind_711_, lean_box(0), lean_box(0), v___x_716_, v___f_714_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_cls_722_, lean_object* v_msg_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_addTrace___redArg(v_inst_718_, v_inst_719_, v_inst_720_, v_inst_721_, v_cls_722_, v_msg_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1(lean_object* v_toPure_725_, lean_object* v_toBind_726_, lean_object* v_mkMsg_727_, lean_object* v___f_728_, uint8_t v_____do__lift_729_){
_start:
{
if (v_____do__lift_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec(v___f_728_);
lean_dec(v_mkMsg_727_);
lean_dec(v_toBind_726_);
v___x_730_ = lean_box(0);
v___x_731_ = lean_apply_2(v_toPure_725_, lean_box(0), v___x_730_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; 
lean_dec(v_toPure_725_);
v___x_732_ = lean_apply_4(v_toBind_726_, lean_box(0), lean_box(0), v_mkMsg_727_, v___f_728_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object* v_toPure_733_, lean_object* v_toBind_734_, lean_object* v_mkMsg_735_, lean_object* v___f_736_, lean_object* v_____do__lift_737_){
_start:
{
uint8_t v_____do__lift_154__boxed_738_; lean_object* v_res_739_; 
v_____do__lift_154__boxed_738_ = lean_unbox(v_____do__lift_737_);
v_res_739_ = l_Lean_traceM___redArg___lam__1(v_toPure_733_, v_toBind_734_, v_mkMsg_735_, v___f_736_, v_____do__lift_154__boxed_738_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_cls_745_, lean_object* v_mkMsg_746_){
_start:
{
lean_object* v_toApplicative_747_; lean_object* v_toBind_748_; lean_object* v_getInheritedTraceOptions_749_; lean_object* v_toPure_750_; lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_toApplicative_747_ = lean_ctor_get(v_inst_740_, 0);
v_toBind_748_ = lean_ctor_get(v_inst_740_, 1);
lean_inc_n(v_toBind_748_, 4);
v_getInheritedTraceOptions_749_ = lean_ctor_get(v_inst_741_, 2);
lean_inc(v_getInheritedTraceOptions_749_);
v_toPure_750_ = lean_ctor_get(v_toApplicative_747_, 1);
lean_inc_n(v_toPure_750_, 2);
lean_inc(v_cls_745_);
v___f_751_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_751_, 0, v_inst_740_);
lean_closure_set(v___f_751_, 1, v_inst_741_);
lean_closure_set(v___f_751_, 2, v_inst_742_);
lean_closure_set(v___f_751_, 3, v_inst_743_);
lean_closure_set(v___f_751_, 4, v_cls_745_);
v___f_752_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_752_, 0, v_toPure_750_);
lean_closure_set(v___f_752_, 1, v_toBind_748_);
lean_closure_set(v___f_752_, 2, v_mkMsg_746_);
lean_closure_set(v___f_752_, 3, v___f_751_);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_753_, 0, v_toPure_750_);
lean_closure_set(v___f_753_, 1, v_cls_745_);
lean_closure_set(v___f_753_, 2, v_toBind_748_);
lean_closure_set(v___f_753_, 3, v_inst_744_);
v___x_754_ = lean_apply_4(v_toBind_748_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_749_, v___f_753_);
v___x_755_ = lean_apply_4(v_toBind_748_, lean_box(0), lean_box(0), v___x_754_, v___f_752_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object* v_m_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_cls_762_, lean_object* v_mkMsg_763_){
_start:
{
lean_object* v_toApplicative_764_; lean_object* v_toBind_765_; lean_object* v_getInheritedTraceOptions_766_; lean_object* v_toPure_767_; lean_object* v___f_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_toApplicative_764_ = lean_ctor_get(v_inst_757_, 0);
v_toBind_765_ = lean_ctor_get(v_inst_757_, 1);
lean_inc_n(v_toBind_765_, 4);
v_getInheritedTraceOptions_766_ = lean_ctor_get(v_inst_758_, 2);
lean_inc(v_getInheritedTraceOptions_766_);
v_toPure_767_ = lean_ctor_get(v_toApplicative_764_, 1);
lean_inc_n(v_toPure_767_, 2);
lean_inc(v_cls_762_);
v___f_768_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_768_, 0, v_inst_757_);
lean_closure_set(v___f_768_, 1, v_inst_758_);
lean_closure_set(v___f_768_, 2, v_inst_759_);
lean_closure_set(v___f_768_, 3, v_inst_760_);
lean_closure_set(v___f_768_, 4, v_cls_762_);
v___f_769_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_769_, 0, v_toPure_767_);
lean_closure_set(v___f_769_, 1, v_toBind_765_);
lean_closure_set(v___f_769_, 2, v_mkMsg_763_);
lean_closure_set(v___f_769_, 3, v___f_768_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_770_, 0, v_toPure_767_);
lean_closure_set(v___f_770_, 1, v_cls_762_);
lean_closure_set(v___f_770_, 2, v_toBind_765_);
lean_closure_set(v___f_770_, 3, v_inst_761_);
v___x_771_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_766_, v___f_770_);
v___x_772_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_771_, v___f_769_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object* v_x_773_){
_start:
{
lean_object* v_msg_774_; 
v_msg_774_ = lean_ctor_get(v_x_773_, 1);
lean_inc_ref(v_msg_774_);
return v_msg_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object* v_x_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_775_);
lean_dec_ref(v_x_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object* v_ref_777_, lean_object* v_msg_778_, lean_object* v_oldTraces_779_, lean_object* v_s_780_){
_start:
{
uint64_t v_tid_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_790_; 
v_tid_781_ = lean_ctor_get_uint64(v_s_780_, sizeof(void*)*1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_s_780_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_s_780_, 0);
lean_dec(v_unused_791_);
v___x_783_ = v_s_780_;
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
else
{
lean_dec(v_s_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_ref_777_);
lean_ctor_set(v___x_785_, 1, v_msg_778_);
v___x_786_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_779_, v___x_785_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_786_);
v___x_788_ = v___x_783_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
lean_ctor_set_uint64(v_reuseFailAlloc_789_, sizeof(void*)*1, v_tid_781_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object* v_ref_792_, lean_object* v_oldTraces_793_, lean_object* v_modifyTraceState_794_, lean_object* v_msg_795_){
_start:
{
lean_object* v___f_796_; lean_object* v___x_797_; 
v___f_796_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0), 4, 3);
lean_closure_set(v___f_796_, 0, v_ref_792_);
lean_closure_set(v___f_796_, 1, v_msg_795_);
lean_closure_set(v___f_796_, 2, v_oldTraces_793_);
v___x_797_ = lean_apply_1(v_modifyTraceState_794_, v___f_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object* v___f_817_, lean_object* v_data_818_, lean_object* v_msg_819_, lean_object* v_inst_820_, lean_object* v_toBind_821_, lean_object* v___f_822_, lean_object* v_____do__lift_823_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; size_t v_sz_826_; size_t v___x_827_; lean_object* v___x_828_; lean_object* v_msg_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_824_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_823_);
v___x_825_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v_sz_826_ = lean_array_size(v___x_824_);
v___x_827_ = ((size_t)0ULL);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_825_, v___f_817_, v_sz_826_, v___x_827_, v___x_824_);
v_msg_829_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_829_, 0, v_data_818_);
lean_ctor_set(v_msg_829_, 1, v_msg_819_);
lean_ctor_set(v_msg_829_, 2, v___x_828_);
v___x_830_ = lean_apply_1(v_inst_820_, v_msg_829_);
v___x_831_ = lean_apply_4(v_toBind_821_, lean_box(0), lean_box(0), v___x_830_, v___f_822_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object* v___f_832_, lean_object* v_data_833_, lean_object* v_msg_834_, lean_object* v_inst_835_, lean_object* v_toBind_836_, lean_object* v___f_837_, lean_object* v_____do__lift_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(v___f_832_, v_data_833_, v_msg_834_, v_inst_835_, v_toBind_836_, v___f_837_, v_____do__lift_838_);
lean_dec_ref(v_____do__lift_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object* v_ref_840_, lean_object* v_withRef_841_, lean_object* v___x_842_, lean_object* v_oldRef_843_){
_start:
{
lean_object* v_ref_844_; lean_object* v___x_845_; 
v_ref_844_ = l_Lean_replaceRef(v_ref_840_, v_oldRef_843_);
v___x_845_ = lean_apply_3(v_withRef_841_, lean_box(0), v_ref_844_, v___x_842_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object* v_ref_846_, lean_object* v_withRef_847_, lean_object* v___x_848_, lean_object* v_oldRef_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(v_ref_846_, v_withRef_847_, v___x_848_, v_oldRef_849_);
lean_dec(v_oldRef_849_);
lean_dec(v_ref_846_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_oldTraces_856_, lean_object* v_data_857_, lean_object* v_ref_858_, lean_object* v_msg_859_){
_start:
{
lean_object* v_toApplicative_860_; lean_object* v_toBind_861_; lean_object* v_modifyTraceState_862_; lean_object* v_getTraceState_863_; lean_object* v_toPure_864_; lean_object* v_getRef_865_; lean_object* v_withRef_866_; lean_object* v___f_867_; lean_object* v___x_868_; lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___f_871_; lean_object* v___x_872_; lean_object* v___f_873_; lean_object* v___x_874_; 
v_toApplicative_860_ = lean_ctor_get(v_inst_852_, 0);
lean_inc_ref(v_toApplicative_860_);
v_toBind_861_ = lean_ctor_get(v_inst_852_, 1);
lean_inc_n(v_toBind_861_, 4);
lean_dec_ref(v_inst_852_);
v_modifyTraceState_862_ = lean_ctor_get(v_inst_853_, 0);
lean_inc(v_modifyTraceState_862_);
v_getTraceState_863_ = lean_ctor_get(v_inst_853_, 1);
lean_inc(v_getTraceState_863_);
lean_dec_ref(v_inst_853_);
v_toPure_864_ = lean_ctor_get(v_toApplicative_860_, 1);
lean_inc(v_toPure_864_);
lean_dec_ref(v_toApplicative_860_);
v_getRef_865_ = lean_ctor_get(v_inst_854_, 0);
lean_inc(v_getRef_865_);
v_withRef_866_ = lean_ctor_get(v_inst_854_, 1);
lean_inc(v_withRef_866_);
lean_dec_ref(v_inst_854_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_867_, 0, v_toPure_864_);
v___x_868_ = lean_apply_4(v_toBind_861_, lean_box(0), lean_box(0), v_getTraceState_863_, v___f_867_);
v___f_869_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0));
lean_inc(v_ref_858_);
v___f_870_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2), 4, 3);
lean_closure_set(v___f_870_, 0, v_ref_858_);
lean_closure_set(v___f_870_, 1, v_oldTraces_856_);
lean_closure_set(v___f_870_, 2, v_modifyTraceState_862_);
v___f_871_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_871_, 0, v___f_869_);
lean_closure_set(v___f_871_, 1, v_data_857_);
lean_closure_set(v___f_871_, 2, v_msg_859_);
lean_closure_set(v___f_871_, 3, v_inst_855_);
lean_closure_set(v___f_871_, 4, v_toBind_861_);
lean_closure_set(v___f_871_, 5, v___f_870_);
v___x_872_ = lean_apply_4(v_toBind_861_, lean_box(0), lean_box(0), v___x_868_, v___f_871_);
v___f_873_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_873_, 0, v_ref_858_);
lean_closure_set(v___f_873_, 1, v_withRef_866_);
lean_closure_set(v___f_873_, 2, v___x_872_);
v___x_874_ = lean_apply_4(v_toBind_861_, lean_box(0), lean_box(0), v_getRef_865_, v___f_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object* v_m_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_oldTraces_880_, lean_object* v_data_881_, lean_object* v_ref_882_, lean_object* v_msg_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_876_, v_inst_877_, v_inst_878_, v_inst_879_, v_oldTraces_880_, v_data_881_, v_ref_882_, v_msg_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object* v_name_885_, lean_object* v_decl_886_, lean_object* v_ref_887_){
_start:
{
lean_object* v_defValue_889_; lean_object* v_descr_890_; lean_object* v_deprecation_x3f_891_; lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_defValue_889_ = lean_ctor_get(v_decl_886_, 0);
v_descr_890_ = lean_ctor_get(v_decl_886_, 1);
v_deprecation_x3f_891_ = lean_ctor_get(v_decl_886_, 2);
v___x_892_ = lean_alloc_ctor(1, 0, 1);
v___x_893_ = lean_unbox(v_defValue_889_);
lean_ctor_set_uint8(v___x_892_, 0, v___x_893_);
lean_inc(v_deprecation_x3f_891_);
lean_inc_ref(v_descr_890_);
lean_inc_n(v_name_885_, 2);
v___x_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_894_, 0, v_name_885_);
lean_ctor_set(v___x_894_, 1, v_ref_887_);
lean_ctor_set(v___x_894_, 2, v___x_892_);
lean_ctor_set(v___x_894_, 3, v_descr_890_);
lean_ctor_set(v___x_894_, 4, v_deprecation_x3f_891_);
v___x_895_ = lean_register_option(v_name_885_, v___x_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_903_; 
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v___x_895_, 0);
lean_dec(v_unused_904_);
v___x_897_ = v___x_895_;
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
else
{
lean_dec(v___x_895_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
lean_inc(v_defValue_889_);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v_name_885_);
lean_ctor_set(v___x_899_, 1, v_defValue_889_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_899_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_name_885_);
v_a_905_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_895_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_895_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_913_, lean_object* v_decl_914_, lean_object* v_ref_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_913_, v_decl_914_, v_ref_915_);
lean_dec_ref(v_decl_914_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_933_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_934_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_935_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_936_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_933_, v___x_934_, v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object* v_name_939_, lean_object* v_decl_940_, lean_object* v_ref_941_){
_start:
{
lean_object* v_defValue_943_; lean_object* v_descr_944_; lean_object* v_deprecation_x3f_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_defValue_943_ = lean_ctor_get(v_decl_940_, 0);
v_descr_944_ = lean_ctor_get(v_decl_940_, 1);
v_deprecation_x3f_945_ = lean_ctor_get(v_decl_940_, 2);
lean_inc(v_defValue_943_);
v___x_946_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_946_, 0, v_defValue_943_);
lean_inc(v_deprecation_x3f_945_);
lean_inc_ref(v_descr_944_);
lean_inc_n(v_name_939_, 2);
v___x_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_947_, 0, v_name_939_);
lean_ctor_set(v___x_947_, 1, v_ref_941_);
lean_ctor_set(v___x_947_, 2, v___x_946_);
lean_ctor_set(v___x_947_, 3, v_descr_944_);
lean_ctor_set(v___x_947_, 4, v_deprecation_x3f_945_);
v___x_948_ = lean_register_option(v_name_939_, v___x_947_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_956_; 
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v___x_948_, 0);
lean_dec(v_unused_957_);
v___x_950_ = v___x_948_;
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
else
{
lean_dec(v___x_948_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
lean_inc(v_defValue_943_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_name_939_);
lean_ctor_set(v___x_952_, 1, v_defValue_943_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_name_939_);
v_a_958_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_948_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_948_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_966_, lean_object* v_decl_967_, lean_object* v_ref_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_966_, v_decl_967_, v_ref_968_);
lean_dec_ref(v_decl_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_987_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_988_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_989_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_990_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_987_, v___x_988_, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1010_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_1011_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_1012_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_1013_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_1010_, v___x_1011_, v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object* v_name_1016_, lean_object* v_decl_1017_, lean_object* v_ref_1018_){
_start:
{
lean_object* v_defValue_1020_; lean_object* v_descr_1021_; lean_object* v_deprecation_x3f_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_defValue_1020_ = lean_ctor_get(v_decl_1017_, 0);
v_descr_1021_ = lean_ctor_get(v_decl_1017_, 1);
v_deprecation_x3f_1022_ = lean_ctor_get(v_decl_1017_, 2);
lean_inc(v_defValue_1020_);
v___x_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1023_, 0, v_defValue_1020_);
lean_inc(v_deprecation_x3f_1022_);
lean_inc_ref(v_descr_1021_);
lean_inc_n(v_name_1016_, 2);
v___x_1024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1024_, 0, v_name_1016_);
lean_ctor_set(v___x_1024_, 1, v_ref_1018_);
lean_ctor_set(v___x_1024_, 2, v___x_1023_);
lean_ctor_set(v___x_1024_, 3, v_descr_1021_);
lean_ctor_set(v___x_1024_, 4, v_deprecation_x3f_1022_);
v___x_1025_ = lean_register_option(v_name_1016_, v___x_1024_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1033_; 
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v___x_1025_, 0);
lean_dec(v_unused_1034_);
v___x_1027_ = v___x_1025_;
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
else
{
lean_dec(v___x_1025_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_inc(v_defValue_1020_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_name_1016_);
lean_ctor_set(v___x_1029_, 1, v_defValue_1020_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1029_);
v___x_1031_ = v___x_1027_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v_name_1016_);
v_a_1035_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1025_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1025_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1043_, lean_object* v_decl_1044_, lean_object* v_ref_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_1043_, v_decl_1044_, v_ref_1045_);
lean_dec_ref(v_decl_1044_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1064_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_1065_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_1066_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_1067_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_1064_, v___x_1065_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1087_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_1088_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_1089_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_1090_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_1087_, v___x_1088_, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4____boxed(lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
return v_res_1092_;
}
}
LEAN_EXPORT uint8_t l_Lean_trace_profiler_isExporting(lean_object* v_opts_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1094_ = l_Lean_KVMap_instValueBool;
v___x_1095_ = l_Lean_KVMap_instValueString;
v___x_1096_ = l_Lean_trace_profiler_output;
v___x_1097_ = l_Lean_Option_get_x3f___redArg(v___x_1095_, v_opts_1093_, v___x_1096_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = l_Lean_trace_profiler_serve;
v___x_1099_ = l_Lean_Option_get___redArg(v___x_1094_, v_opts_1093_, v___x_1098_);
v___x_1100_ = lean_unbox(v___x_1099_);
lean_dec(v___x_1099_);
return v___x_1100_;
}
else
{
uint8_t v___x_1101_; 
lean_dec_ref_known(v___x_1097_, 1);
v___x_1101_ = 1;
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_isExporting___boxed(lean_object* v_opts_1102_){
_start:
{
uint8_t v_res_1103_; lean_object* v_r_1104_; 
v_res_1103_ = l_Lean_trace_profiler_isExporting(v_opts_1102_);
lean_dec_ref(v_opts_1102_);
v_r_1104_ = lean_box(v_res_1103_);
return v_r_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1124_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1125_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1126_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1127_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_1124_, v___x_1125_, v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
return v_res_1129_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1130_; double v___x_1131_; 
v___x_1130_ = lean_unsigned_to_nat(1000000000u);
v___x_1131_ = lean_float_of_nat(v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object* v_toApplicative_1132_, lean_object* v_start_1133_, lean_object* v_a_1134_, lean_object* v_stop_1135_){
_start:
{
lean_object* v_toPure_1136_; double v___x_1137_; double v___x_1138_; double v___x_1139_; double v___x_1140_; double v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_toPure_1136_ = lean_ctor_get(v_toApplicative_1132_, 1);
lean_inc(v_toPure_1136_);
lean_dec_ref(v_toApplicative_1132_);
v___x_1137_ = lean_float_of_nat(v_start_1133_);
v___x_1138_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1139_ = lean_float_div(v___x_1137_, v___x_1138_);
v___x_1140_ = lean_float_of_nat(v_stop_1135_);
v___x_1141_ = lean_float_div(v___x_1140_, v___x_1138_);
v___x_1142_ = lean_box_float(v___x_1139_);
v___x_1143_ = lean_box_float(v___x_1141_);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_a_1134_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_apply_2(v_toPure_1136_, lean_box(0), v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object* v_toApplicative_1147_, lean_object* v_start_1148_, lean_object* v_toBind_1149_, lean_object* v___x_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___f_1152_; lean_object* v___x_1153_; 
v___f_1152_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1152_, 0, v_toApplicative_1147_);
lean_closure_set(v___f_1152_, 1, v_start_1148_);
lean_closure_set(v___f_1152_, 2, v_a_1151_);
v___x_1153_ = lean_apply_4(v_toBind_1149_, lean_box(0), lean_box(0), v___x_1150_, v___f_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object* v_toApplicative_1154_, lean_object* v_toBind_1155_, lean_object* v___x_1156_, lean_object* v_act_1157_, lean_object* v_start_1158_){
_start:
{
lean_object* v___f_1159_; lean_object* v___x_1160_; 
lean_inc(v_toBind_1155_);
v___f_1159_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1159_, 0, v_toApplicative_1154_);
lean_closure_set(v___f_1159_, 1, v_start_1158_);
lean_closure_set(v___f_1159_, 2, v_toBind_1155_);
lean_closure_set(v___f_1159_, 3, v___x_1156_);
v___x_1160_ = lean_apply_4(v_toBind_1155_, lean_box(0), lean_box(0), v_act_1157_, v___f_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object* v_toApplicative_1161_, lean_object* v_start_1162_, lean_object* v_a_1163_, lean_object* v_stop_1164_){
_start:
{
lean_object* v_toPure_1165_; double v___x_1166_; double v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_toPure_1165_ = lean_ctor_get(v_toApplicative_1161_, 1);
lean_inc(v_toPure_1165_);
lean_dec_ref(v_toApplicative_1161_);
v___x_1166_ = lean_float_of_nat(v_start_1162_);
v___x_1167_ = lean_float_of_nat(v_stop_1164_);
v___x_1168_ = lean_box_float(v___x_1166_);
v___x_1169_ = lean_box_float(v___x_1167_);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_a_1163_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = lean_apply_2(v_toPure_1165_, lean_box(0), v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object* v_toApplicative_1173_, lean_object* v_start_1174_, lean_object* v_toBind_1175_, lean_object* v___x_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v___f_1178_; lean_object* v___x_1179_; 
v___f_1178_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1178_, 0, v_toApplicative_1173_);
lean_closure_set(v___f_1178_, 1, v_start_1174_);
lean_closure_set(v___f_1178_, 2, v_a_1177_);
v___x_1179_ = lean_apply_4(v_toBind_1175_, lean_box(0), lean_box(0), v___x_1176_, v___f_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object* v_toApplicative_1180_, lean_object* v_toBind_1181_, lean_object* v___x_1182_, lean_object* v_act_1183_, lean_object* v_start_1184_){
_start:
{
lean_object* v___f_1185_; lean_object* v___x_1186_; 
lean_inc(v_toBind_1181_);
v___f_1185_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1185_, 0, v_toApplicative_1180_);
lean_closure_set(v___f_1185_, 1, v_start_1184_);
lean_closure_set(v___f_1185_, 2, v_toBind_1181_);
lean_closure_set(v___f_1185_, 3, v___x_1182_);
v___x_1186_ = lean_apply_4(v_toBind_1181_, lean_box(0), lean_box(0), v_act_1183_, v___f_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_opts_1191_, lean_object* v_act_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1193_ = l_Lean_KVMap_instValueBool;
v___x_1194_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1195_ = l_Lean_Option_get___redArg(v___x_1193_, v_opts_1191_, v___x_1194_);
v___x_1196_ = lean_unbox(v___x_1195_);
lean_dec(v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v_toApplicative_1197_; lean_object* v_toBind_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; 
v_toApplicative_1197_ = lean_ctor_get(v_inst_1189_, 0);
lean_inc_ref(v_toApplicative_1197_);
v_toBind_1198_ = lean_ctor_get(v_inst_1189_, 1);
lean_inc_n(v_toBind_1198_, 2);
lean_dec_ref(v_inst_1189_);
v___x_1199_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1200_ = lean_apply_2(v_inst_1190_, lean_box(0), v___x_1199_);
lean_inc(v___x_1200_);
v___f_1201_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1201_, 0, v_toApplicative_1197_);
lean_closure_set(v___f_1201_, 1, v_toBind_1198_);
lean_closure_set(v___f_1201_, 2, v___x_1200_);
lean_closure_set(v___f_1201_, 3, v_act_1192_);
v___x_1202_ = lean_apply_4(v_toBind_1198_, lean_box(0), lean_box(0), v___x_1200_, v___f_1201_);
return v___x_1202_;
}
else
{
lean_object* v_toApplicative_1203_; lean_object* v_toBind_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; 
v_toApplicative_1203_ = lean_ctor_get(v_inst_1189_, 0);
lean_inc_ref(v_toApplicative_1203_);
v_toBind_1204_ = lean_ctor_get(v_inst_1189_, 1);
lean_inc_n(v_toBind_1204_, 2);
lean_dec_ref(v_inst_1189_);
v___x_1205_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1206_ = lean_apply_2(v_inst_1190_, lean_box(0), v___x_1205_);
lean_inc(v___x_1206_);
v___f_1207_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1207_, 0, v_toApplicative_1203_);
lean_closure_set(v___f_1207_, 1, v_toBind_1204_);
lean_closure_set(v___f_1207_, 2, v___x_1206_);
lean_closure_set(v___f_1207_, 3, v_act_1192_);
v___x_1208_ = lean_apply_4(v_toBind_1204_, lean_box(0), lean_box(0), v___x_1206_, v___f_1207_);
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_opts_1211_, lean_object* v_act_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(v_inst_1209_, v_inst_1210_, v_opts_1211_, v_act_1212_);
lean_dec_ref(v_opts_1211_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object* v_00_u03b1_1214_, lean_object* v_m_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_opts_1218_, lean_object* v_act_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1220_ = l_Lean_KVMap_instValueBool;
v___x_1221_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1222_ = l_Lean_Option_get___redArg(v___x_1220_, v_opts_1218_, v___x_1221_);
v___x_1223_ = lean_unbox(v___x_1222_);
lean_dec(v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v_toApplicative_1224_; lean_object* v_toBind_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; 
v_toApplicative_1224_ = lean_ctor_get(v_inst_1216_, 0);
lean_inc_ref(v_toApplicative_1224_);
v_toBind_1225_ = lean_ctor_get(v_inst_1216_, 1);
lean_inc_n(v_toBind_1225_, 2);
lean_dec_ref(v_inst_1216_);
v___x_1226_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1227_ = lean_apply_2(v_inst_1217_, lean_box(0), v___x_1226_);
lean_inc(v___x_1227_);
v___f_1228_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1228_, 0, v_toApplicative_1224_);
lean_closure_set(v___f_1228_, 1, v_toBind_1225_);
lean_closure_set(v___f_1228_, 2, v___x_1227_);
lean_closure_set(v___f_1228_, 3, v_act_1219_);
v___x_1229_ = lean_apply_4(v_toBind_1225_, lean_box(0), lean_box(0), v___x_1227_, v___f_1228_);
return v___x_1229_;
}
else
{
lean_object* v_toApplicative_1230_; lean_object* v_toBind_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___f_1234_; lean_object* v___x_1235_; 
v_toApplicative_1230_ = lean_ctor_get(v_inst_1216_, 0);
lean_inc_ref(v_toApplicative_1230_);
v_toBind_1231_ = lean_ctor_get(v_inst_1216_, 1);
lean_inc_n(v_toBind_1231_, 2);
lean_dec_ref(v_inst_1216_);
v___x_1232_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1233_ = lean_apply_2(v_inst_1217_, lean_box(0), v___x_1232_);
lean_inc(v___x_1233_);
v___f_1234_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1234_, 0, v_toApplicative_1230_);
lean_closure_set(v___f_1234_, 1, v_toBind_1231_);
lean_closure_set(v___f_1234_, 2, v___x_1233_);
lean_closure_set(v___f_1234_, 3, v_act_1219_);
v___x_1235_ = lean_apply_4(v_toBind_1231_, lean_box(0), lean_box(0), v___x_1233_, v___f_1234_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object* v_00_u03b1_1236_, lean_object* v_m_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_opts_1240_, lean_object* v_act_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(v_00_u03b1_1236_, v_m_1237_, v_inst_1238_, v_inst_1239_, v_opts_1240_, v_act_1241_);
lean_dec_ref(v_opts_1240_);
return v_res_1242_;
}
}
static double _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0(void){
_start:
{
lean_object* v___x_1243_; double v___x_1244_; 
v___x_1243_ = lean_unsigned_to_nat(1000u);
v___x_1244_ = lean_float_of_nat(v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object* v_o_1245_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1246_ = l_Lean_KVMap_instValueBool;
v___x_1247_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1248_ = l_Lean_Option_get___redArg(v___x_1246_, v_o_1245_, v___x_1247_);
v___x_1249_ = lean_unbox(v___x_1248_);
lean_dec(v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; double v___x_1253_; double v___x_1254_; double v___x_1255_; 
v___x_1250_ = l_Lean_KVMap_instValueNat;
v___x_1251_ = l_Lean_trace_profiler_threshold;
v___x_1252_ = l_Lean_Option_get___redArg(v___x_1250_, v_o_1245_, v___x_1251_);
v___x_1253_ = lean_float_of_nat(v___x_1252_);
v___x_1254_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1255_ = lean_float_div(v___x_1253_, v___x_1254_);
return v___x_1255_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; double v___x_1259_; 
v___x_1256_ = l_Lean_KVMap_instValueNat;
v___x_1257_ = l_Lean_trace_profiler_threshold;
v___x_1258_ = l_Lean_Option_get___redArg(v___x_1256_, v_o_1245_, v___x_1257_);
v___x_1259_ = lean_float_of_nat(v___x_1258_);
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object* v_o_1260_){
_start:
{
double v_res_1261_; lean_object* v_r_1262_; 
v_res_1261_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1260_);
lean_dec_ref(v_o_1260_);
v_r_1262_ = lean_box_float(v_res_1261_);
return v_r_1262_;
}
}
static lean_object* _init_l_Lean_instMonadAlwaysExceptEIO___closed__0(void){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object* v_00_u03b5_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___closed__0, &l_Lean_instMonadAlwaysExceptEIO___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___closed__0);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object* v_inst_1266_, lean_object* v_always_1267_){
_start:
{
lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; 
lean_inc_ref(v_always_1267_);
v___f_1268_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1268_, 0, v_always_1267_);
lean_closure_set(v___f_1268_, 1, v_inst_1266_);
v___f_1269_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_1269_, 0, v_always_1267_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___f_1268_);
lean_ctor_set(v___x_1270_, 1, v___f_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object* v_m_1271_, lean_object* v_inst_1272_, lean_object* v_00_u03b5_1273_, lean_object* v_00_u03c3_1274_, lean_object* v_always_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_1272_, v_always_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object* v_always_1277_){
_start:
{
lean_object* v___f_1278_; lean_object* v___f_1279_; lean_object* v___x_1280_; 
lean_inc_ref(v_always_1277_);
v___f_1278_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1278_, 0, v_always_1277_);
v___f_1279_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1279_, 0, v_always_1277_);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___f_1278_);
lean_ctor_set(v___x_1280_, 1, v___f_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object* v_m_1281_, lean_object* v_00_u03b5_1282_, lean_object* v_00_u03c9_1283_, lean_object* v_00_u03c3_1284_, lean_object* v_always_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object* v_always_1287_){
_start:
{
lean_object* v___f_1288_; lean_object* v___f_1289_; lean_object* v___x_1290_; 
lean_inc_ref(v_always_1287_);
v___f_1288_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1288_, 0, v_always_1287_);
v___f_1289_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1289_, 0, v_always_1287_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___f_1288_);
lean_ctor_set(v___x_1290_, 1, v___f_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object* v_m_1291_, lean_object* v_00_u03b5_1292_, lean_object* v_00_u03c1_1293_, lean_object* v_always_1294_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object* v_always_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1297_, v_inst_1298_, v_inst_1299_, v_always_1296_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object* v_00_u03b1_1301_, lean_object* v_m_1302_, lean_object* v_00_u03b5_1303_, lean_object* v_00_u03c9_1304_, lean_object* v_00_u03b2_1305_, lean_object* v_always_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1307_, v_inst_1308_, v_inst_1309_, v_always_1306_);
return v___x_1310_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___lam__0(lean_object* v_x_1317_){
_start:
{
if (lean_obj_tag(v_x_1317_) == 0)
{
uint8_t v___x_1318_; 
v___x_1318_ = 2;
return v___x_1318_;
}
else
{
lean_object* v_a_1319_; uint8_t v___x_1320_; 
v_a_1319_ = lean_ctor_get(v_x_1317_, 0);
v___x_1320_ = lean_unbox(v_a_1319_);
if (v___x_1320_ == 0)
{
uint8_t v___x_1321_; 
v___x_1321_ = 1;
return v___x_1321_;
}
else
{
uint8_t v___x_1322_; 
v___x_1322_ = 0;
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object* v_x_1323_){
_start:
{
uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_res_1324_ = l_Lean_instExceptToTraceResultBool___lam__0(v_x_1323_);
lean_dec_ref(v_x_1323_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object* v_00_u03b5_1327_){
_start:
{
lean_object* v___f_1328_; 
v___f_1328_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___closed__0));
return v___f_1328_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___lam__0(lean_object* v_x_1329_){
_start:
{
if (lean_obj_tag(v_x_1329_) == 0)
{
uint8_t v___x_1330_; 
v___x_1330_ = 2;
return v___x_1330_;
}
else
{
lean_object* v_a_1331_; 
v_a_1331_ = lean_ctor_get(v_x_1329_, 0);
if (lean_obj_tag(v_a_1331_) == 0)
{
uint8_t v___x_1332_; 
v___x_1332_ = 1;
return v___x_1332_;
}
else
{
uint8_t v___x_1333_; 
v___x_1333_ = 0;
return v___x_1333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object* v_x_1334_){
_start:
{
uint8_t v_res_1335_; lean_object* v_r_1336_; 
v_res_1335_ = l_Lean_instExceptToTraceResultOption___lam__0(v_x_1334_);
lean_dec_ref(v_x_1334_);
v_r_1336_ = lean_box(v_res_1335_);
return v_r_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object* v_00_u03b1_1338_, lean_object* v_00_u03b5_1339_){
_start:
{
lean_object* v___f_1340_; 
v___f_1340_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___closed__0));
return v___f_1340_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultExpr___lam__0(lean_object* v_x_1341_){
_start:
{
if (lean_obj_tag(v_x_1341_) == 0)
{
uint8_t v___x_1342_; 
v___x_1342_ = 2;
return v___x_1342_;
}
else
{
lean_object* v_a_1343_; uint8_t v___x_1344_; 
v_a_1343_ = lean_ctor_get(v_x_1341_, 0);
v___x_1344_ = l_Lean_Expr_hasSyntheticSorry(v_a_1343_);
if (v___x_1344_ == 0)
{
uint8_t v___x_1345_; 
v___x_1345_ = 0;
return v___x_1345_;
}
else
{
uint8_t v___x_1346_; 
v___x_1346_ = 1;
return v___x_1346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___lam__0___boxed(lean_object* v_x_1347_){
_start:
{
uint8_t v_res_1348_; lean_object* v_r_1349_; 
v_res_1348_ = l_Lean_instExceptToTraceResultExpr___lam__0(v_x_1347_);
lean_dec_ref(v_x_1347_);
v_r_1349_ = lean_box(v_res_1348_);
return v_r_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr(lean_object* v_00_u03b5_1351_){
_start:
{
lean_object* v___f_1352_; 
v___f_1352_ = ((lean_object*)(l_Lean_instExceptToTraceResultExpr___closed__0));
return v___f_1352_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object* v_x_1353_){
_start:
{
if (lean_obj_tag(v_x_1353_) == 0)
{
uint8_t v___x_1354_; 
v___x_1354_ = 2;
return v___x_1354_;
}
else
{
uint8_t v___x_1355_; 
v___x_1355_ = 0;
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object* v_x_1356_){
_start:
{
uint8_t v_res_1357_; lean_object* v_r_1358_; 
v_res_1357_ = l_Lean_instExceptToTraceResult___lam__0(v_x_1356_);
lean_dec_ref(v_x_1356_);
v_r_1358_ = lean_box(v_res_1357_);
return v_r_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object* v_00_u03b1_1360_, lean_object* v_00_u03b5_1361_){
_start:
{
lean_object* v___f_1362_; 
v___f_1362_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
return v___f_1362_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___redArg(lean_object* v_inst_1363_, lean_object* v_e_1364_){
_start:
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1365_ = lean_apply_1(v_inst_1363_, v_e_1364_);
v___x_1366_ = lean_unbox(v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___redArg___boxed(lean_object* v_inst_1367_, lean_object* v_e_1368_){
_start:
{
uint8_t v_res_1369_; lean_object* v_r_1370_; 
v_res_1369_ = l_Lean_Except_toTraceResult___redArg(v_inst_1367_, v_e_1368_);
v_r_1370_ = lean_box(v_res_1369_);
return v_r_1370_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult(lean_object* v_00_u03b1_1371_, lean_object* v_00_u03b5_1372_, lean_object* v_inst_1373_, lean_object* v_e_1374_){
_start:
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = lean_apply_1(v_inst_1373_, v_e_1374_);
v___x_1376_ = lean_unbox(v___x_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b5_1378_, lean_object* v_inst_1379_, lean_object* v_e_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l_Lean_Except_toTraceResult(v_00_u03b1_1377_, v_00_u03b5_1378_, v_inst_1379_, v_e_1380_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0));
v___x_1385_ = l_Lean_stringToMessageData(v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object* v_inst_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v_toApplicative_1388_; lean_object* v_toPure_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_toApplicative_1388_ = lean_ctor_get(v_inst_1386_, 0);
lean_inc_ref(v_toApplicative_1388_);
lean_dec_ref(v_inst_1386_);
v_toPure_1389_ = lean_ctor_get(v_toApplicative_1388_, 1);
lean_inc(v_toPure_1389_);
lean_dec_ref(v_toApplicative_1388_);
v___x_1390_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1);
v___x_1391_ = lean_apply_2(v_toPure_1389_, lean_box(0), v___x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(lean_object* v_inst_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(v_inst_1392_, v_x_1393_);
lean_dec(v_x_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object* v_oldTraces_1395_, lean_object* v_s_1396_){
_start:
{
uint64_t v_tid_1397_; lean_object* v_traces_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1406_; 
v_tid_1397_ = lean_ctor_get_uint64(v_s_1396_, sizeof(void*)*1);
v_traces_1398_ = lean_ctor_get(v_s_1396_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_s_1396_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1400_ = v_s_1396_;
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_traces_1398_);
lean_dec(v_s_1396_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1395_, v_traces_1398_);
lean_dec_ref(v_traces_1398_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
lean_ctor_set_uint64(v_reuseFailAlloc_1405_, sizeof(void*)*1, v_tid_1397_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object* v_always_1407_, lean_object* v_inst_1408_, lean_object* v_fst_1409_, lean_object* v_____r_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1407_);
v___x_1412_ = l_MonadExcept_ofExcept___redArg(v_inst_1408_, v___x_1411_, v_fst_1409_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object* v_inst_1413_, lean_object* v___x_1414_, lean_object* v_fst_1415_, lean_object* v_____r_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_MonadExcept_ofExcept___redArg(v_inst_1413_, v___x_1414_, v_fst_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_, lean_object* v_inst_1421_, lean_object* v_oldTraces_1422_, lean_object* v_ref_1423_, lean_object* v_toBind_1424_, lean_object* v___f_1425_, lean_object* v_inst_1426_, lean_object* v_fst_1427_, lean_object* v_cls_1428_, uint8_t v_collapsed_1429_, lean_object* v_tag_1430_, uint8_t v___x_1431_, double v_fst_1432_, double v_snd_1433_, lean_object* v_m_1434_){
_start:
{
lean_object* v_data_1436_; lean_object* v_result_1439_; lean_object* v___x_1440_; double v___x_1441_; lean_object* v_data_1442_; 
v_result_1439_ = lean_apply_1(v_inst_1426_, v_fst_1427_);
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_result_1439_);
v___x_1441_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_1430_);
lean_inc_ref(v___x_1440_);
lean_inc(v_cls_1428_);
v_data_1442_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1442_, 0, v_cls_1428_);
lean_ctor_set(v_data_1442_, 1, v___x_1440_);
lean_ctor_set(v_data_1442_, 2, v_tag_1430_);
lean_ctor_set_float(v_data_1442_, sizeof(void*)*3, v___x_1441_);
lean_ctor_set_float(v_data_1442_, sizeof(void*)*3 + 8, v___x_1441_);
lean_ctor_set_uint8(v_data_1442_, sizeof(void*)*3 + 16, v_collapsed_1429_);
if (v___x_1431_ == 0)
{
lean_dec_ref_known(v___x_1440_, 1);
lean_dec_ref(v_tag_1430_);
lean_dec(v_cls_1428_);
v_data_1436_ = v_data_1442_;
goto v___jp_1435_;
}
else
{
lean_object* v_data_1443_; 
lean_dec_ref_known(v_data_1442_, 3);
v_data_1443_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1443_, 0, v_cls_1428_);
lean_ctor_set(v_data_1443_, 1, v___x_1440_);
lean_ctor_set(v_data_1443_, 2, v_tag_1430_);
lean_ctor_set_float(v_data_1443_, sizeof(void*)*3, v_fst_1432_);
lean_ctor_set_float(v_data_1443_, sizeof(void*)*3 + 8, v_snd_1433_);
lean_ctor_set_uint8(v_data_1443_, sizeof(void*)*3 + 16, v_collapsed_1429_);
v_data_1436_ = v_data_1443_;
goto v___jp_1435_;
}
v___jp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_1418_, v_inst_1419_, v_inst_1420_, v_inst_1421_, v_oldTraces_1422_, v_data_1436_, v_ref_1423_, v_m_1434_);
v___x_1438_ = lean_apply_4(v_toBind_1424_, lean_box(0), lean_box(0), v___x_1437_, v___f_1425_);
return v___x_1438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_1444_ = _args[0];
lean_object* v_inst_1445_ = _args[1];
lean_object* v_inst_1446_ = _args[2];
lean_object* v_inst_1447_ = _args[3];
lean_object* v_oldTraces_1448_ = _args[4];
lean_object* v_ref_1449_ = _args[5];
lean_object* v_toBind_1450_ = _args[6];
lean_object* v___f_1451_ = _args[7];
lean_object* v_inst_1452_ = _args[8];
lean_object* v_fst_1453_ = _args[9];
lean_object* v_cls_1454_ = _args[10];
lean_object* v_collapsed_1455_ = _args[11];
lean_object* v_tag_1456_ = _args[12];
lean_object* v___x_1457_ = _args[13];
lean_object* v_fst_1458_ = _args[14];
lean_object* v_snd_1459_ = _args[15];
lean_object* v_m_1460_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1461_; uint8_t v___x_608__boxed_1462_; double v_fst_609__boxed_1463_; double v_snd_610__boxed_1464_; lean_object* v_res_1465_; 
v_collapsed_boxed_1461_ = lean_unbox(v_collapsed_1455_);
v___x_608__boxed_1462_ = lean_unbox(v___x_1457_);
v_fst_609__boxed_1463_ = lean_unbox_float(v_fst_1458_);
lean_dec_ref(v_fst_1458_);
v_snd_610__boxed_1464_ = lean_unbox_float(v_snd_1459_);
lean_dec_ref(v_snd_1459_);
v_res_1465_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1444_, v_inst_1445_, v_inst_1446_, v_inst_1447_, v_oldTraces_1448_, v_ref_1449_, v_toBind_1450_, v___f_1451_, v_inst_1452_, v_fst_1453_, v_cls_1454_, v_collapsed_boxed_1461_, v_tag_1456_, v___x_608__boxed_1462_, v_fst_609__boxed_1463_, v_snd_610__boxed_1464_, v_m_1460_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(lean_object* v_always_1466_, lean_object* v_inst_1467_, lean_object* v_fst_1468_, lean_object* v_inst_1469_, lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_oldTraces_1472_, lean_object* v_toBind_1473_, lean_object* v_inst_1474_, lean_object* v_cls_1475_, uint8_t v_collapsed_1476_, lean_object* v_tag_1477_, uint8_t v___x_1478_, double v_fst_1479_, double v_snd_1480_, lean_object* v_msg_1481_, lean_object* v___f_1482_, lean_object* v_ref_1483_){
_start:
{
lean_object* v___x_1484_; lean_object* v_tryCatch_1485_; lean_object* v___f_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_inc_ref(v_always_1466_);
v___x_1484_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1466_);
v_tryCatch_1485_ = lean_ctor_get(v_always_1466_, 1);
lean_inc(v_tryCatch_1485_);
lean_dec_ref(v_always_1466_);
lean_inc_ref_n(v_fst_1468_, 2);
lean_inc_ref(v_inst_1467_);
v___f_1486_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1486_, 0, v_inst_1467_);
lean_closure_set(v___f_1486_, 1, v___x_1484_);
lean_closure_set(v___f_1486_, 2, v_fst_1468_);
v___x_1487_ = lean_box(v_collapsed_1476_);
v___x_1488_ = lean_box(v___x_1478_);
v___x_1489_ = lean_box_float(v_fst_1479_);
v___x_1490_ = lean_box_float(v_snd_1480_);
lean_inc(v_toBind_1473_);
v___f_1491_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1491_, 0, v_inst_1467_);
lean_closure_set(v___f_1491_, 1, v_inst_1469_);
lean_closure_set(v___f_1491_, 2, v_inst_1470_);
lean_closure_set(v___f_1491_, 3, v_inst_1471_);
lean_closure_set(v___f_1491_, 4, v_oldTraces_1472_);
lean_closure_set(v___f_1491_, 5, v_ref_1483_);
lean_closure_set(v___f_1491_, 6, v_toBind_1473_);
lean_closure_set(v___f_1491_, 7, v___f_1486_);
lean_closure_set(v___f_1491_, 8, v_inst_1474_);
lean_closure_set(v___f_1491_, 9, v_fst_1468_);
lean_closure_set(v___f_1491_, 10, v_cls_1475_);
lean_closure_set(v___f_1491_, 11, v___x_1487_);
lean_closure_set(v___f_1491_, 12, v_tag_1477_);
lean_closure_set(v___f_1491_, 13, v___x_1488_);
lean_closure_set(v___f_1491_, 14, v___x_1489_);
lean_closure_set(v___f_1491_, 15, v___x_1490_);
v___x_1492_ = lean_apply_1(v_msg_1481_, v_fst_1468_);
v___x_1493_ = lean_apply_3(v_tryCatch_1485_, lean_box(0), v___x_1492_, v___f_1482_);
v___x_1494_ = lean_apply_4(v_toBind_1473_, lean_box(0), lean_box(0), v___x_1493_, v___f_1491_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_always_1495_ = _args[0];
lean_object* v_inst_1496_ = _args[1];
lean_object* v_fst_1497_ = _args[2];
lean_object* v_inst_1498_ = _args[3];
lean_object* v_inst_1499_ = _args[4];
lean_object* v_inst_1500_ = _args[5];
lean_object* v_oldTraces_1501_ = _args[6];
lean_object* v_toBind_1502_ = _args[7];
lean_object* v_inst_1503_ = _args[8];
lean_object* v_cls_1504_ = _args[9];
lean_object* v_collapsed_1505_ = _args[10];
lean_object* v_tag_1506_ = _args[11];
lean_object* v___x_1507_ = _args[12];
lean_object* v_fst_1508_ = _args[13];
lean_object* v_snd_1509_ = _args[14];
lean_object* v_msg_1510_ = _args[15];
lean_object* v___f_1511_ = _args[16];
lean_object* v_ref_1512_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_1513_; uint8_t v___x_648__boxed_1514_; double v_fst_649__boxed_1515_; double v_snd_650__boxed_1516_; lean_object* v_res_1517_; 
v_collapsed_boxed_1513_ = lean_unbox(v_collapsed_1505_);
v___x_648__boxed_1514_ = lean_unbox(v___x_1507_);
v_fst_649__boxed_1515_ = lean_unbox_float(v_fst_1508_);
lean_dec_ref(v_fst_1508_);
v_snd_650__boxed_1516_ = lean_unbox_float(v_snd_1509_);
lean_dec_ref(v_snd_1509_);
v_res_1517_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(v_always_1495_, v_inst_1496_, v_fst_1497_, v_inst_1498_, v_inst_1499_, v_inst_1500_, v_oldTraces_1501_, v_toBind_1502_, v_inst_1503_, v_cls_1504_, v_collapsed_boxed_1513_, v_tag_1506_, v___x_648__boxed_1514_, v_fst_649__boxed_1515_, v_snd_650__boxed_1516_, v_msg_1510_, v___f_1511_, v_ref_1512_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_always_1522_, lean_object* v_inst_1523_, lean_object* v_cls_1524_, uint8_t v_collapsed_1525_, lean_object* v_tag_1526_, lean_object* v_opts_1527_, uint8_t v_clsEnabled_1528_, lean_object* v_oldTraces_1529_, lean_object* v_msg_1530_, lean_object* v_resStartStop_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v_snd_1533_; lean_object* v_fst_1534_; lean_object* v_fst_1535_; lean_object* v_snd_1536_; lean_object* v___f_1537_; lean_object* v___f_1538_; lean_object* v___f_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___y_1549_; double v___y_1555_; uint8_t v___x_1560_; 
v___x_1532_ = l_Lean_KVMap_instValueBool;
v_snd_1533_ = lean_ctor_get(v_resStartStop_1531_, 1);
lean_inc(v_snd_1533_);
v_fst_1534_ = lean_ctor_get(v_resStartStop_1531_, 0);
lean_inc_n(v_fst_1534_, 2);
lean_dec_ref(v_resStartStop_1531_);
v_fst_1535_ = lean_ctor_get(v_snd_1533_, 0);
lean_inc(v_fst_1535_);
v_snd_1536_ = lean_ctor_get(v_snd_1533_, 1);
lean_inc(v_snd_1536_);
lean_dec(v_snd_1533_);
lean_inc_ref_n(v_inst_1518_, 2);
v___f_1537_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1537_, 0, v_inst_1518_);
lean_inc_ref(v_oldTraces_1529_);
v___f_1538_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1538_, 0, v_oldTraces_1529_);
lean_inc_ref(v_always_1522_);
v___f_1539_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1539_, 0, v_always_1522_);
lean_closure_set(v___f_1539_, 1, v_inst_1518_);
lean_closure_set(v___f_1539_, 2, v_fst_1534_);
v___x_1540_ = l_Lean_trace_profiler;
v___x_1541_ = l_Lean_Option_get___redArg(v___x_1532_, v_opts_1527_, v___x_1540_);
v___x_1560_ = lean_unbox(v___x_1541_);
if (v___x_1560_ == 0)
{
uint8_t v___x_1561_; 
v___x_1561_ = lean_unbox(v___x_1541_);
v___y_1549_ = v___x_1561_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1563_ = l_Lean_Option_get___redArg(v___x_1532_, v_opts_1527_, v___x_1562_);
v___x_1564_ = lean_unbox(v___x_1563_);
lean_dec(v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; double v___x_1568_; double v___x_1569_; double v___x_1570_; 
v___x_1565_ = l_Lean_KVMap_instValueNat;
v___x_1566_ = l_Lean_trace_profiler_threshold;
v___x_1567_ = l_Lean_Option_get___redArg(v___x_1565_, v_opts_1527_, v___x_1566_);
v___x_1568_ = lean_float_of_nat(v___x_1567_);
v___x_1569_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1570_ = lean_float_div(v___x_1568_, v___x_1569_);
v___y_1555_ = v___x_1570_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; double v___x_1574_; 
v___x_1571_ = l_Lean_KVMap_instValueNat;
v___x_1572_ = l_Lean_trace_profiler_threshold;
v___x_1573_ = l_Lean_Option_get___redArg(v___x_1571_, v_opts_1527_, v___x_1572_);
v___x_1574_ = lean_float_of_nat(v___x_1573_);
v___y_1555_ = v___x_1574_;
goto v___jp_1554_;
}
}
v___jp_1542_:
{
lean_object* v_toBind_1543_; lean_object* v_getRef_1544_; lean_object* v___x_1545_; lean_object* v___f_1546_; lean_object* v___x_1547_; 
v_toBind_1543_ = lean_ctor_get(v_inst_1518_, 1);
lean_inc_n(v_toBind_1543_, 2);
v_getRef_1544_ = lean_ctor_get(v_inst_1520_, 0);
lean_inc(v_getRef_1544_);
v___x_1545_ = lean_box(v_collapsed_1525_);
v___f_1546_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed), 18, 17);
lean_closure_set(v___f_1546_, 0, v_always_1522_);
lean_closure_set(v___f_1546_, 1, v_inst_1518_);
lean_closure_set(v___f_1546_, 2, v_fst_1534_);
lean_closure_set(v___f_1546_, 3, v_inst_1519_);
lean_closure_set(v___f_1546_, 4, v_inst_1520_);
lean_closure_set(v___f_1546_, 5, v_inst_1521_);
lean_closure_set(v___f_1546_, 6, v_oldTraces_1529_);
lean_closure_set(v___f_1546_, 7, v_toBind_1543_);
lean_closure_set(v___f_1546_, 8, v_inst_1523_);
lean_closure_set(v___f_1546_, 9, v_cls_1524_);
lean_closure_set(v___f_1546_, 10, v___x_1545_);
lean_closure_set(v___f_1546_, 11, v_tag_1526_);
lean_closure_set(v___f_1546_, 12, v___x_1541_);
lean_closure_set(v___f_1546_, 13, v_fst_1535_);
lean_closure_set(v___f_1546_, 14, v_snd_1536_);
lean_closure_set(v___f_1546_, 15, v_msg_1530_);
lean_closure_set(v___f_1546_, 16, v___f_1537_);
v___x_1547_ = lean_apply_4(v_toBind_1543_, lean_box(0), lean_box(0), v_getRef_1544_, v___f_1546_);
return v___x_1547_;
}
v___jp_1548_:
{
if (v_clsEnabled_1528_ == 0)
{
if (v___y_1549_ == 0)
{
lean_object* v_toBind_1550_; lean_object* v_modifyTraceState_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec(v___x_1541_);
lean_dec_ref(v___f_1537_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_fst_1534_);
lean_dec(v_msg_1530_);
lean_dec_ref(v_oldTraces_1529_);
lean_dec_ref(v_tag_1526_);
lean_dec(v_cls_1524_);
lean_dec_ref(v_inst_1523_);
lean_dec_ref(v_always_1522_);
lean_dec(v_inst_1521_);
lean_dec_ref(v_inst_1520_);
v_toBind_1550_ = lean_ctor_get(v_inst_1518_, 1);
lean_inc(v_toBind_1550_);
lean_dec_ref(v_inst_1518_);
v_modifyTraceState_1551_ = lean_ctor_get(v_inst_1519_, 0);
lean_inc(v_modifyTraceState_1551_);
lean_dec_ref(v_inst_1519_);
v___x_1552_ = lean_apply_1(v_modifyTraceState_1551_, v___f_1538_);
v___x_1553_ = lean_apply_4(v_toBind_1550_, lean_box(0), lean_box(0), v___x_1552_, v___f_1539_);
return v___x_1553_;
}
else
{
lean_dec_ref(v___f_1539_);
lean_dec_ref(v___f_1538_);
goto v___jp_1542_;
}
}
else
{
lean_dec_ref(v___f_1539_);
lean_dec_ref(v___f_1538_);
goto v___jp_1542_;
}
}
v___jp_1554_:
{
double v___x_1556_; double v___x_1557_; double v___x_1558_; uint8_t v___x_1559_; 
v___x_1556_ = lean_unbox_float(v_snd_1536_);
v___x_1557_ = lean_unbox_float(v_fst_1535_);
v___x_1558_ = lean_float_sub(v___x_1556_, v___x_1557_);
v___x_1559_ = lean_float_decLt(v___y_1555_, v___x_1558_);
v___y_1549_ = v___x_1559_;
goto v___jp_1548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_always_1579_, lean_object* v_inst_1580_, lean_object* v_cls_1581_, lean_object* v_collapsed_1582_, lean_object* v_tag_1583_, lean_object* v_opts_1584_, lean_object* v_clsEnabled_1585_, lean_object* v_oldTraces_1586_, lean_object* v_msg_1587_, lean_object* v_resStartStop_1588_){
_start:
{
uint8_t v_collapsed_boxed_1589_; uint8_t v_clsEnabled_boxed_1590_; lean_object* v_res_1591_; 
v_collapsed_boxed_1589_ = lean_unbox(v_collapsed_1582_);
v_clsEnabled_boxed_1590_ = lean_unbox(v_clsEnabled_1585_);
v_res_1591_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1575_, v_inst_1576_, v_inst_1577_, v_inst_1578_, v_always_1579_, v_inst_1580_, v_cls_1581_, v_collapsed_boxed_1589_, v_tag_1583_, v_opts_1584_, v_clsEnabled_boxed_1590_, v_oldTraces_1586_, v_msg_1587_, v_resStartStop_1588_);
lean_dec_ref(v_opts_1584_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object* v_00_u03b1_1592_, lean_object* v_m_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_00_u03b5_1598_, lean_object* v_always_1599_, lean_object* v_inst_1600_, lean_object* v_cls_1601_, uint8_t v_collapsed_1602_, lean_object* v_tag_1603_, lean_object* v_opts_1604_, uint8_t v_clsEnabled_1605_, lean_object* v_oldTraces_1606_, lean_object* v_msg_1607_, lean_object* v_resStartStop_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1594_, v_inst_1595_, v_inst_1596_, v_inst_1597_, v_always_1599_, v_inst_1600_, v_cls_1601_, v_collapsed_1602_, v_tag_1603_, v_opts_1604_, v_clsEnabled_1605_, v_oldTraces_1606_, v_msg_1607_, v_resStartStop_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_1610_ = _args[0];
lean_object* v_m_1611_ = _args[1];
lean_object* v_inst_1612_ = _args[2];
lean_object* v_inst_1613_ = _args[3];
lean_object* v_inst_1614_ = _args[4];
lean_object* v_inst_1615_ = _args[5];
lean_object* v_00_u03b5_1616_ = _args[6];
lean_object* v_always_1617_ = _args[7];
lean_object* v_inst_1618_ = _args[8];
lean_object* v_cls_1619_ = _args[9];
lean_object* v_collapsed_1620_ = _args[10];
lean_object* v_tag_1621_ = _args[11];
lean_object* v_opts_1622_ = _args[12];
lean_object* v_clsEnabled_1623_ = _args[13];
lean_object* v_oldTraces_1624_ = _args[14];
lean_object* v_msg_1625_ = _args[15];
lean_object* v_resStartStop_1626_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1627_; uint8_t v_clsEnabled_boxed_1628_; lean_object* v_res_1629_; 
v_collapsed_boxed_1627_ = lean_unbox(v_collapsed_1620_);
v_clsEnabled_boxed_1628_ = lean_unbox(v_clsEnabled_1623_);
v_res_1629_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(v_00_u03b1_1610_, v_m_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_00_u03b5_1616_, v_always_1617_, v_inst_1618_, v_cls_1619_, v_collapsed_boxed_1627_, v_tag_1621_, v_opts_1622_, v_clsEnabled_boxed_1628_, v_oldTraces_1624_, v_msg_1625_, v_resStartStop_1626_);
lean_dec_ref(v_opts_1622_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_always_1634_, lean_object* v_inst_1635_, lean_object* v_cls_1636_, uint8_t v_collapsed_1637_, lean_object* v_tag_1638_, lean_object* v_opts_1639_, uint8_t v_clsEnabled_1640_, lean_object* v_oldTraces_1641_, lean_object* v_msg_1642_, lean_object* v_resStartStop_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1630_, v_inst_1631_, v_inst_1632_, v_inst_1633_, v_always_1634_, v_inst_1635_, v_cls_1636_, v_collapsed_1637_, v_tag_1638_, v_opts_1639_, v_clsEnabled_1640_, v_oldTraces_1641_, v_msg_1642_, v_resStartStop_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_inst_1647_, lean_object* v_inst_1648_, lean_object* v_always_1649_, lean_object* v_inst_1650_, lean_object* v_cls_1651_, lean_object* v_collapsed_1652_, lean_object* v_tag_1653_, lean_object* v_opts_1654_, lean_object* v_clsEnabled_1655_, lean_object* v_oldTraces_1656_, lean_object* v_msg_1657_, lean_object* v_resStartStop_1658_){
_start:
{
uint8_t v_collapsed_boxed_1659_; uint8_t v_clsEnabled_boxed_1660_; lean_object* v_res_1661_; 
v_collapsed_boxed_1659_ = lean_unbox(v_collapsed_1652_);
v_clsEnabled_boxed_1660_ = lean_unbox(v_clsEnabled_1655_);
v_res_1661_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1645_, v_inst_1646_, v_inst_1647_, v_inst_1648_, v_always_1649_, v_inst_1650_, v_cls_1651_, v_collapsed_boxed_1659_, v_tag_1653_, v_opts_1654_, v_clsEnabled_boxed_1660_, v_oldTraces_1656_, v_msg_1657_, v_resStartStop_1658_);
lean_dec_ref(v_opts_1654_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object* v_toPure_1662_, lean_object* v_ex_1663_){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_ex_1663_);
v___x_1665_ = lean_apply_2(v_toPure_1662_, lean_box(0), v___x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object* v_toPure_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1668_, 0, v_a_1667_);
v___x_1669_ = lean_apply_2(v_toPure_1666_, lean_box(0), v___x_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object* v_start_1670_, lean_object* v_a_1671_, lean_object* v_toPure_1672_, lean_object* v_stop_1673_){
_start:
{
double v___x_1674_; double v___x_1675_; double v___x_1676_; double v___x_1677_; double v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1674_ = lean_float_of_nat(v_start_1670_);
v___x_1675_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1676_ = lean_float_div(v___x_1674_, v___x_1675_);
v___x_1677_ = lean_float_of_nat(v_stop_1673_);
v___x_1678_ = lean_float_div(v___x_1677_, v___x_1675_);
v___x_1679_ = lean_box_float(v___x_1676_);
v___x_1680_ = lean_box_float(v___x_1678_);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_a_1671_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = lean_apply_2(v_toPure_1672_, lean_box(0), v___x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object* v_start_1684_, lean_object* v_toPure_1685_, lean_object* v_toBind_1686_, lean_object* v___x_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v___f_1689_; lean_object* v___x_1690_; 
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1689_, 0, v_start_1684_);
lean_closure_set(v___f_1689_, 1, v_a_1688_);
lean_closure_set(v___f_1689_, 2, v_toPure_1685_);
v___x_1690_ = lean_apply_4(v_toBind_1686_, lean_box(0), lean_box(0), v___x_1687_, v___f_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object* v_toPure_1691_, lean_object* v_toBind_1692_, lean_object* v___x_1693_, lean_object* v___x_1694_, lean_object* v_start_1695_){
_start:
{
lean_object* v___f_1696_; lean_object* v___x_1697_; 
lean_inc(v_toBind_1692_);
v___f_1696_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1696_, 0, v_start_1695_);
lean_closure_set(v___f_1696_, 1, v_toPure_1691_);
lean_closure_set(v___f_1696_, 2, v_toBind_1692_);
lean_closure_set(v___f_1696_, 3, v___x_1693_);
v___x_1697_ = lean_apply_4(v_toBind_1692_, lean_box(0), lean_box(0), v___x_1694_, v___f_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object* v_start_1698_, lean_object* v_a_1699_, lean_object* v_toPure_1700_, lean_object* v_stop_1701_){
_start:
{
double v___x_1702_; double v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1702_ = lean_float_of_nat(v_start_1698_);
v___x_1703_ = lean_float_of_nat(v_stop_1701_);
v___x_1704_ = lean_box_float(v___x_1702_);
v___x_1705_ = lean_box_float(v___x_1703_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v_a_1699_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = lean_apply_2(v_toPure_1700_, lean_box(0), v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object* v_start_1709_, lean_object* v_toPure_1710_, lean_object* v_toBind_1711_, lean_object* v___x_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v___f_1714_; lean_object* v___x_1715_; 
v___f_1714_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__6), 4, 3);
lean_closure_set(v___f_1714_, 0, v_start_1709_);
lean_closure_set(v___f_1714_, 1, v_a_1713_);
lean_closure_set(v___f_1714_, 2, v_toPure_1710_);
v___x_1715_ = lean_apply_4(v_toBind_1711_, lean_box(0), lean_box(0), v___x_1712_, v___f_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object* v_toPure_1716_, lean_object* v_toBind_1717_, lean_object* v___x_1718_, lean_object* v___x_1719_, lean_object* v_start_1720_){
_start:
{
lean_object* v___f_1721_; lean_object* v___x_1722_; 
lean_inc(v_toBind_1717_);
v___f_1721_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1721_, 0, v_start_1720_);
lean_closure_set(v___f_1721_, 1, v_toPure_1716_);
lean_closure_set(v___f_1721_, 2, v_toBind_1717_);
lean_closure_set(v___f_1721_, 3, v___x_1718_);
v___x_1722_ = lean_apply_4(v_toBind_1717_, lean_box(0), lean_box(0), v___x_1719_, v___f_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object* v_always_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_cls_1729_, uint8_t v_collapsed_1730_, lean_object* v_tag_1731_, lean_object* v_opts_1732_, uint8_t v_clsEnabled_1733_, lean_object* v_msg_1734_, lean_object* v_toPure_1735_, lean_object* v_toBind_1736_, lean_object* v_k_1737_, lean_object* v_inst_1738_, lean_object* v_oldTraces_1739_){
_start:
{
lean_object* v_tryCatch_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___f_1743_; lean_object* v___f_1744_; lean_object* v___f_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_tryCatch_1740_ = lean_ctor_get(v_always_1723_, 1);
lean_inc(v_tryCatch_1740_);
v___x_1741_ = lean_box(v_collapsed_1730_);
v___x_1742_ = lean_box(v_clsEnabled_1733_);
lean_inc_ref(v_opts_1732_);
v___f_1743_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1743_, 0, v_inst_1724_);
lean_closure_set(v___f_1743_, 1, v_inst_1725_);
lean_closure_set(v___f_1743_, 2, v_inst_1726_);
lean_closure_set(v___f_1743_, 3, v_inst_1727_);
lean_closure_set(v___f_1743_, 4, v_always_1723_);
lean_closure_set(v___f_1743_, 5, v_inst_1728_);
lean_closure_set(v___f_1743_, 6, v_cls_1729_);
lean_closure_set(v___f_1743_, 7, v___x_1741_);
lean_closure_set(v___f_1743_, 8, v_tag_1731_);
lean_closure_set(v___f_1743_, 9, v_opts_1732_);
lean_closure_set(v___f_1743_, 10, v___x_1742_);
lean_closure_set(v___f_1743_, 11, v_oldTraces_1739_);
lean_closure_set(v___f_1743_, 12, v_msg_1734_);
lean_inc_n(v_toPure_1735_, 2);
v___f_1744_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1744_, 0, v_toPure_1735_);
v___f_1745_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1745_, 0, v_toPure_1735_);
lean_inc(v_toBind_1736_);
v___x_1746_ = lean_apply_4(v_toBind_1736_, lean_box(0), lean_box(0), v_k_1737_, v___f_1745_);
v___x_1747_ = lean_apply_3(v_tryCatch_1740_, lean_box(0), v___x_1746_, v___f_1744_);
v___x_1748_ = l_Lean_KVMap_instValueBool;
v___x_1749_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1750_ = l_Lean_Option_get___redArg(v___x_1748_, v_opts_1732_, v___x_1749_);
lean_dec_ref(v_opts_1732_);
v___x_1751_ = lean_unbox(v___x_1750_);
lean_dec(v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___f_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1752_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1753_ = lean_apply_2(v_inst_1738_, lean_box(0), v___x_1752_);
lean_inc(v___x_1753_);
lean_inc_n(v_toBind_1736_, 2);
v___f_1754_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1754_, 0, v_toPure_1735_);
lean_closure_set(v___f_1754_, 1, v_toBind_1736_);
lean_closure_set(v___f_1754_, 2, v___x_1753_);
lean_closure_set(v___f_1754_, 3, v___x_1747_);
v___x_1755_ = lean_apply_4(v_toBind_1736_, lean_box(0), lean_box(0), v___x_1753_, v___f_1754_);
v___x_1756_ = lean_apply_4(v_toBind_1736_, lean_box(0), lean_box(0), v___x_1755_, v___f_1743_);
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___f_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1757_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1758_ = lean_apply_2(v_inst_1738_, lean_box(0), v___x_1757_);
lean_inc(v___x_1758_);
lean_inc_n(v_toBind_1736_, 2);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_1759_, 0, v_toPure_1735_);
lean_closure_set(v___f_1759_, 1, v_toBind_1736_);
lean_closure_set(v___f_1759_, 2, v___x_1758_);
lean_closure_set(v___f_1759_, 3, v___x_1747_);
v___x_1760_ = lean_apply_4(v_toBind_1736_, lean_box(0), lean_box(0), v___x_1758_, v___f_1759_);
v___x_1761_ = lean_apply_4(v_toBind_1736_, lean_box(0), lean_box(0), v___x_1760_, v___f_1743_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_always_1762_ = _args[0];
lean_object* v_inst_1763_ = _args[1];
lean_object* v_inst_1764_ = _args[2];
lean_object* v_inst_1765_ = _args[3];
lean_object* v_inst_1766_ = _args[4];
lean_object* v_inst_1767_ = _args[5];
lean_object* v_cls_1768_ = _args[6];
lean_object* v_collapsed_1769_ = _args[7];
lean_object* v_tag_1770_ = _args[8];
lean_object* v_opts_1771_ = _args[9];
lean_object* v_clsEnabled_1772_ = _args[10];
lean_object* v_msg_1773_ = _args[11];
lean_object* v_toPure_1774_ = _args[12];
lean_object* v_toBind_1775_ = _args[13];
lean_object* v_k_1776_ = _args[14];
lean_object* v_inst_1777_ = _args[15];
lean_object* v_oldTraces_1778_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1779_; uint8_t v_clsEnabled_boxed_1780_; lean_object* v_res_1781_; 
v_collapsed_boxed_1779_ = lean_unbox(v_collapsed_1769_);
v_clsEnabled_boxed_1780_ = lean_unbox(v_clsEnabled_1772_);
v_res_1781_ = l_Lean_withTraceNode___redArg___lam__9(v_always_1762_, v_inst_1763_, v_inst_1764_, v_inst_1765_, v_inst_1766_, v_inst_1767_, v_cls_1768_, v_collapsed_boxed_1779_, v_tag_1770_, v_opts_1771_, v_clsEnabled_boxed_1780_, v_msg_1773_, v_toPure_1774_, v_toBind_1775_, v_k_1776_, v_inst_1777_, v_oldTraces_1778_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object* v_always_1782_, lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_inst_1787_, lean_object* v_cls_1788_, uint8_t v_collapsed_1789_, lean_object* v_tag_1790_, lean_object* v_opts_1791_, lean_object* v_msg_1792_, lean_object* v_toPure_1793_, lean_object* v_toBind_1794_, lean_object* v_k_1795_, lean_object* v_inst_1796_, uint8_t v_clsEnabled_1797_){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___f_1800_; 
v___x_1798_ = lean_box(v_collapsed_1789_);
v___x_1799_ = lean_box(v_clsEnabled_1797_);
lean_inc(v_k_1795_);
lean_inc(v_toBind_1794_);
lean_inc_ref(v_opts_1791_);
lean_inc_ref(v_inst_1784_);
lean_inc_ref(v_inst_1783_);
v___f_1800_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_1800_, 0, v_always_1782_);
lean_closure_set(v___f_1800_, 1, v_inst_1783_);
lean_closure_set(v___f_1800_, 2, v_inst_1784_);
lean_closure_set(v___f_1800_, 3, v_inst_1785_);
lean_closure_set(v___f_1800_, 4, v_inst_1786_);
lean_closure_set(v___f_1800_, 5, v_inst_1787_);
lean_closure_set(v___f_1800_, 6, v_cls_1788_);
lean_closure_set(v___f_1800_, 7, v___x_1798_);
lean_closure_set(v___f_1800_, 8, v_tag_1790_);
lean_closure_set(v___f_1800_, 9, v_opts_1791_);
lean_closure_set(v___f_1800_, 10, v___x_1799_);
lean_closure_set(v___f_1800_, 11, v_msg_1792_);
lean_closure_set(v___f_1800_, 12, v_toPure_1793_);
lean_closure_set(v___f_1800_, 13, v_toBind_1794_);
lean_closure_set(v___f_1800_, 14, v_k_1795_);
lean_closure_set(v___f_1800_, 15, v_inst_1796_);
if (v_clsEnabled_1797_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1804_ = l_Lean_KVMap_instValueBool;
v___x_1805_ = l_Lean_trace_profiler;
v___x_1806_ = l_Lean_Option_get___redArg(v___x_1804_, v_opts_1791_, v___x_1805_);
lean_dec_ref(v_opts_1791_);
v___x_1807_ = lean_unbox(v___x_1806_);
lean_dec(v___x_1806_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v___f_1800_);
lean_dec(v_toBind_1794_);
lean_dec_ref(v_inst_1784_);
lean_dec_ref(v_inst_1783_);
return v_k_1795_;
}
else
{
lean_dec(v_k_1795_);
goto v___jp_1801_;
}
}
else
{
lean_dec(v_k_1795_);
lean_dec_ref(v_opts_1791_);
goto v___jp_1801_;
}
v___jp_1801_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1783_, v_inst_1784_);
v___x_1803_ = lean_apply_4(v_toBind_1794_, lean_box(0), lean_box(0), v___x_1802_, v___f_1800_);
return v___x_1803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object* v_always_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_cls_1814_, lean_object* v_collapsed_1815_, lean_object* v_tag_1816_, lean_object* v_opts_1817_, lean_object* v_msg_1818_, lean_object* v_toPure_1819_, lean_object* v_toBind_1820_, lean_object* v_k_1821_, lean_object* v_inst_1822_, lean_object* v_clsEnabled_1823_){
_start:
{
uint8_t v_collapsed_boxed_1824_; uint8_t v_clsEnabled_boxed_1825_; lean_object* v_res_1826_; 
v_collapsed_boxed_1824_ = lean_unbox(v_collapsed_1815_);
v_clsEnabled_boxed_1825_ = lean_unbox(v_clsEnabled_1823_);
v_res_1826_ = l_Lean_withTraceNode___redArg___lam__10(v_always_1808_, v_inst_1809_, v_inst_1810_, v_inst_1811_, v_inst_1812_, v_inst_1813_, v_cls_1814_, v_collapsed_boxed_1824_, v_tag_1816_, v_opts_1817_, v_msg_1818_, v_toPure_1819_, v_toBind_1820_, v_k_1821_, v_inst_1822_, v_clsEnabled_boxed_1825_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object* v_k_1827_, lean_object* v_inst_1828_, lean_object* v_toApplicative_1829_, lean_object* v_always_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_cls_1835_, uint8_t v_collapsed_1836_, lean_object* v_tag_1837_, lean_object* v_msg_1838_, lean_object* v_toBind_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_opts_1842_){
_start:
{
uint8_t v_hasTrace_1843_; 
v_hasTrace_1843_ = lean_ctor_get_uint8(v_opts_1842_, sizeof(void*)*1);
if (v_hasTrace_1843_ == 0)
{
lean_dec_ref(v_opts_1842_);
lean_dec(v_inst_1841_);
lean_dec(v_inst_1840_);
lean_dec(v_toBind_1839_);
lean_dec(v_msg_1838_);
lean_dec_ref(v_tag_1837_);
lean_dec(v_cls_1835_);
lean_dec_ref(v_inst_1834_);
lean_dec(v_inst_1833_);
lean_dec_ref(v_inst_1832_);
lean_dec_ref(v_inst_1831_);
lean_dec_ref(v_always_1830_);
lean_dec_ref(v_toApplicative_1829_);
lean_dec_ref(v_inst_1828_);
return v_k_1827_;
}
else
{
lean_object* v_getInheritedTraceOptions_1844_; lean_object* v_toPure_1845_; lean_object* v___x_1846_; lean_object* v___f_1847_; lean_object* v___f_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_getInheritedTraceOptions_1844_ = lean_ctor_get(v_inst_1828_, 2);
lean_inc(v_getInheritedTraceOptions_1844_);
v_toPure_1845_ = lean_ctor_get(v_toApplicative_1829_, 1);
lean_inc_n(v_toPure_1845_, 2);
lean_dec_ref(v_toApplicative_1829_);
v___x_1846_ = lean_box(v_collapsed_1836_);
lean_inc_n(v_toBind_1839_, 3);
lean_inc(v_cls_1835_);
v___f_1847_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_1847_, 0, v_always_1830_);
lean_closure_set(v___f_1847_, 1, v_inst_1831_);
lean_closure_set(v___f_1847_, 2, v_inst_1828_);
lean_closure_set(v___f_1847_, 3, v_inst_1832_);
lean_closure_set(v___f_1847_, 4, v_inst_1833_);
lean_closure_set(v___f_1847_, 5, v_inst_1834_);
lean_closure_set(v___f_1847_, 6, v_cls_1835_);
lean_closure_set(v___f_1847_, 7, v___x_1846_);
lean_closure_set(v___f_1847_, 8, v_tag_1837_);
lean_closure_set(v___f_1847_, 9, v_opts_1842_);
lean_closure_set(v___f_1847_, 10, v_msg_1838_);
lean_closure_set(v___f_1847_, 11, v_toPure_1845_);
lean_closure_set(v___f_1847_, 12, v_toBind_1839_);
lean_closure_set(v___f_1847_, 13, v_k_1827_);
lean_closure_set(v___f_1847_, 14, v_inst_1840_);
v___f_1848_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1848_, 0, v_toPure_1845_);
lean_closure_set(v___f_1848_, 1, v_cls_1835_);
lean_closure_set(v___f_1848_, 2, v_toBind_1839_);
lean_closure_set(v___f_1848_, 3, v_inst_1841_);
v___x_1849_ = lean_apply_4(v_toBind_1839_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1844_, v___f_1848_);
v___x_1850_ = lean_apply_4(v_toBind_1839_, lean_box(0), lean_box(0), v___x_1849_, v___f_1847_);
return v___x_1850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13___boxed(lean_object* v_k_1851_, lean_object* v_inst_1852_, lean_object* v_toApplicative_1853_, lean_object* v_always_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_inst_1858_, lean_object* v_cls_1859_, lean_object* v_collapsed_1860_, lean_object* v_tag_1861_, lean_object* v_msg_1862_, lean_object* v_toBind_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_opts_1866_){
_start:
{
uint8_t v_collapsed_boxed_1867_; lean_object* v_res_1868_; 
v_collapsed_boxed_1867_ = lean_unbox(v_collapsed_1860_);
v_res_1868_ = l_Lean_withTraceNode___redArg___lam__13(v_k_1851_, v_inst_1852_, v_toApplicative_1853_, v_always_1854_, v_inst_1855_, v_inst_1856_, v_inst_1857_, v_inst_1858_, v_cls_1859_, v_collapsed_boxed_1867_, v_tag_1861_, v_msg_1862_, v_toBind_1863_, v_inst_1864_, v_inst_1865_, v_opts_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_always_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_cls_1877_, lean_object* v_msg_1878_, lean_object* v_k_1879_, uint8_t v_collapsed_1880_, lean_object* v_tag_1881_){
_start:
{
lean_object* v_toApplicative_1882_; lean_object* v_toBind_1883_; lean_object* v___x_1884_; lean_object* v___f_1885_; lean_object* v___x_1886_; 
v_toApplicative_1882_ = lean_ctor_get(v_inst_1869_, 0);
lean_inc_ref(v_toApplicative_1882_);
v_toBind_1883_ = lean_ctor_get(v_inst_1869_, 1);
lean_inc_n(v_toBind_1883_, 2);
v___x_1884_ = lean_box(v_collapsed_1880_);
lean_inc(v_inst_1873_);
v___f_1885_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1885_, 0, v_k_1879_);
lean_closure_set(v___f_1885_, 1, v_inst_1870_);
lean_closure_set(v___f_1885_, 2, v_toApplicative_1882_);
lean_closure_set(v___f_1885_, 3, v_always_1874_);
lean_closure_set(v___f_1885_, 4, v_inst_1869_);
lean_closure_set(v___f_1885_, 5, v_inst_1871_);
lean_closure_set(v___f_1885_, 6, v_inst_1872_);
lean_closure_set(v___f_1885_, 7, v_inst_1876_);
lean_closure_set(v___f_1885_, 8, v_cls_1877_);
lean_closure_set(v___f_1885_, 9, v___x_1884_);
lean_closure_set(v___f_1885_, 10, v_tag_1881_);
lean_closure_set(v___f_1885_, 11, v_msg_1878_);
lean_closure_set(v___f_1885_, 12, v_toBind_1883_);
lean_closure_set(v___f_1885_, 13, v_inst_1875_);
lean_closure_set(v___f_1885_, 14, v_inst_1873_);
v___x_1886_ = lean_apply_4(v_toBind_1883_, lean_box(0), lean_box(0), v_inst_1873_, v___f_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_always_1892_, lean_object* v_inst_1893_, lean_object* v_inst_1894_, lean_object* v_cls_1895_, lean_object* v_msg_1896_, lean_object* v_k_1897_, lean_object* v_collapsed_1898_, lean_object* v_tag_1899_){
_start:
{
uint8_t v_collapsed_boxed_1900_; lean_object* v_res_1901_; 
v_collapsed_boxed_1900_ = lean_unbox(v_collapsed_1898_);
v_res_1901_ = l_Lean_withTraceNode___redArg(v_inst_1887_, v_inst_1888_, v_inst_1889_, v_inst_1890_, v_inst_1891_, v_always_1892_, v_inst_1893_, v_inst_1894_, v_cls_1895_, v_msg_1896_, v_k_1897_, v_collapsed_boxed_1900_, v_tag_1899_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object* v_00_u03b1_1902_, lean_object* v_m_1903_, lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_inst_1907_, lean_object* v_inst_1908_, lean_object* v_00_u03b5_1909_, lean_object* v_always_1910_, lean_object* v_inst_1911_, lean_object* v_inst_1912_, lean_object* v_cls_1913_, lean_object* v_msg_1914_, lean_object* v_k_1915_, uint8_t v_collapsed_1916_, lean_object* v_tag_1917_){
_start:
{
lean_object* v_toApplicative_1918_; lean_object* v_toBind_1919_; lean_object* v___x_1920_; lean_object* v___f_1921_; lean_object* v___x_1922_; 
v_toApplicative_1918_ = lean_ctor_get(v_inst_1904_, 0);
lean_inc_ref(v_toApplicative_1918_);
v_toBind_1919_ = lean_ctor_get(v_inst_1904_, 1);
lean_inc_n(v_toBind_1919_, 2);
v___x_1920_ = lean_box(v_collapsed_1916_);
lean_inc(v_inst_1908_);
v___f_1921_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1921_, 0, v_k_1915_);
lean_closure_set(v___f_1921_, 1, v_inst_1905_);
lean_closure_set(v___f_1921_, 2, v_toApplicative_1918_);
lean_closure_set(v___f_1921_, 3, v_always_1910_);
lean_closure_set(v___f_1921_, 4, v_inst_1904_);
lean_closure_set(v___f_1921_, 5, v_inst_1906_);
lean_closure_set(v___f_1921_, 6, v_inst_1907_);
lean_closure_set(v___f_1921_, 7, v_inst_1912_);
lean_closure_set(v___f_1921_, 8, v_cls_1913_);
lean_closure_set(v___f_1921_, 9, v___x_1920_);
lean_closure_set(v___f_1921_, 10, v_tag_1917_);
lean_closure_set(v___f_1921_, 11, v_msg_1914_);
lean_closure_set(v___f_1921_, 12, v_toBind_1919_);
lean_closure_set(v___f_1921_, 13, v_inst_1911_);
lean_closure_set(v___f_1921_, 14, v_inst_1908_);
v___x_1922_ = lean_apply_4(v_toBind_1919_, lean_box(0), lean_box(0), v_inst_1908_, v___f_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object* v_00_u03b1_1923_, lean_object* v_m_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_inst_1927_, lean_object* v_inst_1928_, lean_object* v_inst_1929_, lean_object* v_00_u03b5_1930_, lean_object* v_always_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_cls_1934_, lean_object* v_msg_1935_, lean_object* v_k_1936_, lean_object* v_collapsed_1937_, lean_object* v_tag_1938_){
_start:
{
uint8_t v_collapsed_boxed_1939_; lean_object* v_res_1940_; 
v_collapsed_boxed_1939_ = lean_unbox(v_collapsed_1937_);
v_res_1940_ = l_Lean_withTraceNode(v_00_u03b1_1923_, v_m_1924_, v_inst_1925_, v_inst_1926_, v_inst_1927_, v_inst_1928_, v_inst_1929_, v_00_u03b5_1930_, v_always_1931_, v_inst_1932_, v_inst_1933_, v_cls_1934_, v_msg_1935_, v_k_1936_, v_collapsed_boxed_1939_, v_tag_1938_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object* v_self_1941_){
_start:
{
lean_object* v_fst_1942_; 
v_fst_1942_ = lean_ctor_get(v_self_1941_, 0);
lean_inc(v_fst_1942_);
return v_fst_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object* v_self_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_1943_);
lean_dec_ref(v_self_1943_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object* v_toPure_1945_, lean_object* v_x_1946_){
_start:
{
if (lean_obj_tag(v_x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v_a_1947_ = lean_ctor_get(v_x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v_x_1946_, 1);
v___x_1948_ = l_Lean_Exception_toMessageData(v_a_1947_);
v___x_1949_ = lean_apply_2(v_toPure_1945_, lean_box(0), v___x_1948_);
return v___x_1949_;
}
else
{
lean_object* v_a_1950_; lean_object* v_snd_1951_; lean_object* v___x_1952_; 
v_a_1950_ = lean_ctor_get(v_x_1946_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v_x_1946_, 1);
v_snd_1951_ = lean_ctor_get(v_a_1950_, 1);
lean_inc(v_snd_1951_);
lean_dec(v_a_1950_);
v___x_1952_ = lean_apply_2(v_toPure_1945_, lean_box(0), v_snd_1951_);
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object* v_toPure_1953_, lean_object* v_ex_1954_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v_ex_1954_);
v___x_1956_ = lean_apply_2(v_toPure_1953_, lean_box(0), v___x_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object* v_toPure_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_a_1958_);
v___x_1960_ = lean_apply_2(v_toPure_1957_, lean_box(0), v___x_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_inst_1963_, lean_object* v_inst_1964_, lean_object* v_inst_1965_, lean_object* v___f_1966_, lean_object* v_cls_1967_, uint8_t v_collapsed_1968_, lean_object* v_tag_1969_, lean_object* v_opts_1970_, uint8_t v_clsEnabled_1971_, lean_object* v_oldTraces_1972_, lean_object* v_msg_1973_, lean_object* v_resStartStop_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1961_, v_inst_1962_, v_inst_1963_, v_inst_1964_, v_inst_1965_, v___f_1966_, v_cls_1967_, v_collapsed_1968_, v_tag_1969_, v_opts_1970_, v_clsEnabled_1971_, v_oldTraces_1972_, v_msg_1973_, v_resStartStop_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3___boxed(lean_object* v_inst_1976_, lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v___f_1981_, lean_object* v_cls_1982_, lean_object* v_collapsed_1983_, lean_object* v_tag_1984_, lean_object* v_opts_1985_, lean_object* v_clsEnabled_1986_, lean_object* v_oldTraces_1987_, lean_object* v_msg_1988_, lean_object* v_resStartStop_1989_){
_start:
{
uint8_t v_collapsed_boxed_1990_; uint8_t v_clsEnabled_boxed_1991_; lean_object* v_res_1992_; 
v_collapsed_boxed_1990_ = lean_unbox(v_collapsed_1983_);
v_clsEnabled_boxed_1991_ = lean_unbox(v_clsEnabled_1986_);
v_res_1992_ = l_Lean_withTraceNode_x27___redArg___lam__3(v_inst_1976_, v_inst_1977_, v_inst_1978_, v_inst_1979_, v_inst_1980_, v___f_1981_, v_cls_1982_, v_collapsed_boxed_1990_, v_tag_1984_, v_opts_1985_, v_clsEnabled_boxed_1991_, v_oldTraces_1987_, v_msg_1988_, v_resStartStop_1989_);
lean_dec_ref(v_opts_1985_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object* v_start_1993_, lean_object* v_a_1994_, lean_object* v_toPure_1995_, lean_object* v_stop_1996_){
_start:
{
double v___x_1997_; double v___x_1998_; double v___x_1999_; double v___x_2000_; double v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_1997_ = lean_float_of_nat(v_start_1993_);
v___x_1998_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1999_ = lean_float_div(v___x_1997_, v___x_1998_);
v___x_2000_ = lean_float_of_nat(v_stop_1996_);
v___x_2001_ = lean_float_div(v___x_2000_, v___x_1998_);
v___x_2002_ = lean_box_float(v___x_1999_);
v___x_2003_ = lean_box_float(v___x_2001_);
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v_a_1994_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_apply_2(v_toPure_1995_, lean_box(0), v___x_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object* v_start_2007_, lean_object* v_toPure_2008_, lean_object* v_toBind_2009_, lean_object* v___x_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v___f_2012_; lean_object* v___x_2013_; 
v___f_2012_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__5), 4, 3);
lean_closure_set(v___f_2012_, 0, v_start_2007_);
lean_closure_set(v___f_2012_, 1, v_a_2011_);
lean_closure_set(v___f_2012_, 2, v_toPure_2008_);
v___x_2013_ = lean_apply_4(v_toBind_2009_, lean_box(0), lean_box(0), v___x_2010_, v___f_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object* v_toPure_2014_, lean_object* v_toBind_2015_, lean_object* v___x_2016_, lean_object* v___x_2017_, lean_object* v_start_2018_){
_start:
{
lean_object* v___f_2019_; lean_object* v___x_2020_; 
lean_inc(v_toBind_2015_);
v___f_2019_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__6), 5, 4);
lean_closure_set(v___f_2019_, 0, v_start_2018_);
lean_closure_set(v___f_2019_, 1, v_toPure_2014_);
lean_closure_set(v___f_2019_, 2, v_toBind_2015_);
lean_closure_set(v___f_2019_, 3, v___x_2016_);
v___x_2020_ = lean_apply_4(v_toBind_2015_, lean_box(0), lean_box(0), v___x_2017_, v___f_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object* v_start_2021_, lean_object* v_a_2022_, lean_object* v_toPure_2023_, lean_object* v_stop_2024_){
_start:
{
double v___x_2025_; double v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2025_ = lean_float_of_nat(v_start_2021_);
v___x_2026_ = lean_float_of_nat(v_stop_2024_);
v___x_2027_ = lean_box_float(v___x_2025_);
v___x_2028_ = lean_box_float(v___x_2026_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2027_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_a_2022_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_apply_2(v_toPure_2023_, lean_box(0), v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object* v_start_2032_, lean_object* v_toPure_2033_, lean_object* v_toBind_2034_, lean_object* v___x_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___f_2037_; lean_object* v___x_2038_; 
v___f_2037_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__8), 4, 3);
lean_closure_set(v___f_2037_, 0, v_start_2032_);
lean_closure_set(v___f_2037_, 1, v_a_2036_);
lean_closure_set(v___f_2037_, 2, v_toPure_2033_);
v___x_2038_ = lean_apply_4(v_toBind_2034_, lean_box(0), lean_box(0), v___x_2035_, v___f_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object* v_toPure_2039_, lean_object* v_toBind_2040_, lean_object* v___x_2041_, lean_object* v___x_2042_, lean_object* v_start_2043_){
_start:
{
lean_object* v___f_2044_; lean_object* v___x_2045_; 
lean_inc(v_toBind_2040_);
v___f_2044_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__9), 5, 4);
lean_closure_set(v___f_2044_, 0, v_start_2043_);
lean_closure_set(v___f_2044_, 1, v_toPure_2039_);
lean_closure_set(v___f_2044_, 2, v_toBind_2040_);
lean_closure_set(v___f_2044_, 3, v___x_2041_);
v___x_2045_ = lean_apply_4(v_toBind_2040_, lean_box(0), lean_box(0), v___x_2042_, v___f_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_inst_2050_, lean_object* v___f_2051_, lean_object* v_cls_2052_, uint8_t v_collapsed_2053_, lean_object* v_tag_2054_, lean_object* v_opts_2055_, uint8_t v_clsEnabled_2056_, lean_object* v_msg_2057_, lean_object* v_toBind_2058_, lean_object* v_k_2059_, lean_object* v___f_2060_, lean_object* v___f_2061_, lean_object* v_inst_2062_, lean_object* v_toPure_2063_, lean_object* v_oldTraces_2064_){
_start:
{
lean_object* v_tryCatch_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___f_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_tryCatch_2065_ = lean_ctor_get(v_inst_2046_, 1);
lean_inc(v_tryCatch_2065_);
v___x_2066_ = lean_box(v_collapsed_2053_);
v___x_2067_ = lean_box(v_clsEnabled_2056_);
lean_inc_ref(v_opts_2055_);
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_2068_, 0, v_inst_2047_);
lean_closure_set(v___f_2068_, 1, v_inst_2048_);
lean_closure_set(v___f_2068_, 2, v_inst_2049_);
lean_closure_set(v___f_2068_, 3, v_inst_2050_);
lean_closure_set(v___f_2068_, 4, v_inst_2046_);
lean_closure_set(v___f_2068_, 5, v___f_2051_);
lean_closure_set(v___f_2068_, 6, v_cls_2052_);
lean_closure_set(v___f_2068_, 7, v___x_2066_);
lean_closure_set(v___f_2068_, 8, v_tag_2054_);
lean_closure_set(v___f_2068_, 9, v_opts_2055_);
lean_closure_set(v___f_2068_, 10, v___x_2067_);
lean_closure_set(v___f_2068_, 11, v_oldTraces_2064_);
lean_closure_set(v___f_2068_, 12, v_msg_2057_);
lean_inc(v_toBind_2058_);
v___x_2069_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v_k_2059_, v___f_2060_);
v___x_2070_ = lean_apply_3(v_tryCatch_2065_, lean_box(0), v___x_2069_, v___f_2061_);
v___x_2071_ = l_Lean_KVMap_instValueBool;
v___x_2072_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2073_ = l_Lean_Option_get___redArg(v___x_2071_, v_opts_2055_, v___x_2072_);
lean_dec_ref(v_opts_2055_);
v___x_2074_ = lean_unbox(v___x_2073_);
lean_dec(v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2075_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_2076_ = lean_apply_2(v_inst_2062_, lean_box(0), v___x_2075_);
lean_inc(v___x_2076_);
lean_inc_n(v_toBind_2058_, 2);
v___f_2077_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__7), 5, 4);
lean_closure_set(v___f_2077_, 0, v_toPure_2063_);
lean_closure_set(v___f_2077_, 1, v_toBind_2058_);
lean_closure_set(v___f_2077_, 2, v___x_2076_);
lean_closure_set(v___f_2077_, 3, v___x_2070_);
v___x_2078_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2076_, v___f_2077_);
v___x_2079_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2078_, v___f_2068_);
return v___x_2079_;
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2080_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_2081_ = lean_apply_2(v_inst_2062_, lean_box(0), v___x_2080_);
lean_inc(v___x_2081_);
lean_inc_n(v_toBind_2058_, 2);
v___f_2082_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__10), 5, 4);
lean_closure_set(v___f_2082_, 0, v_toPure_2063_);
lean_closure_set(v___f_2082_, 1, v_toBind_2058_);
lean_closure_set(v___f_2082_, 2, v___x_2081_);
lean_closure_set(v___f_2082_, 3, v___x_2070_);
v___x_2083_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2081_, v___f_2082_);
v___x_2084_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2083_, v___f_2068_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_2085_ = _args[0];
lean_object* v_inst_2086_ = _args[1];
lean_object* v_inst_2087_ = _args[2];
lean_object* v_inst_2088_ = _args[3];
lean_object* v_inst_2089_ = _args[4];
lean_object* v___f_2090_ = _args[5];
lean_object* v_cls_2091_ = _args[6];
lean_object* v_collapsed_2092_ = _args[7];
lean_object* v_tag_2093_ = _args[8];
lean_object* v_opts_2094_ = _args[9];
lean_object* v_clsEnabled_2095_ = _args[10];
lean_object* v_msg_2096_ = _args[11];
lean_object* v_toBind_2097_ = _args[12];
lean_object* v_k_2098_ = _args[13];
lean_object* v___f_2099_ = _args[14];
lean_object* v___f_2100_ = _args[15];
lean_object* v_inst_2101_ = _args[16];
lean_object* v_toPure_2102_ = _args[17];
lean_object* v_oldTraces_2103_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_2104_; uint8_t v_clsEnabled_boxed_2105_; lean_object* v_res_2106_; 
v_collapsed_boxed_2104_ = lean_unbox(v_collapsed_2092_);
v_clsEnabled_boxed_2105_ = lean_unbox(v_clsEnabled_2095_);
v_res_2106_ = l_Lean_withTraceNode_x27___redArg___lam__11(v_inst_2085_, v_inst_2086_, v_inst_2087_, v_inst_2088_, v_inst_2089_, v___f_2090_, v_cls_2091_, v_collapsed_boxed_2104_, v_tag_2093_, v_opts_2094_, v_clsEnabled_boxed_2105_, v_msg_2096_, v_toBind_2097_, v_k_2098_, v___f_2099_, v___f_2100_, v_inst_2101_, v_toPure_2102_, v_oldTraces_2103_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object* v_inst_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v___f_2112_, lean_object* v_cls_2113_, uint8_t v_collapsed_2114_, lean_object* v_tag_2115_, lean_object* v_opts_2116_, lean_object* v_msg_2117_, lean_object* v_toBind_2118_, lean_object* v_k_2119_, lean_object* v___f_2120_, lean_object* v___f_2121_, lean_object* v_inst_2122_, lean_object* v_toPure_2123_, uint8_t v_clsEnabled_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___f_2127_; 
v___x_2125_ = lean_box(v_collapsed_2114_);
v___x_2126_ = lean_box(v_clsEnabled_2124_);
lean_inc(v_k_2119_);
lean_inc(v_toBind_2118_);
lean_inc_ref(v_opts_2116_);
lean_inc_ref(v_inst_2109_);
lean_inc_ref(v_inst_2108_);
v___f_2127_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__11___boxed), 19, 18);
lean_closure_set(v___f_2127_, 0, v_inst_2107_);
lean_closure_set(v___f_2127_, 1, v_inst_2108_);
lean_closure_set(v___f_2127_, 2, v_inst_2109_);
lean_closure_set(v___f_2127_, 3, v_inst_2110_);
lean_closure_set(v___f_2127_, 4, v_inst_2111_);
lean_closure_set(v___f_2127_, 5, v___f_2112_);
lean_closure_set(v___f_2127_, 6, v_cls_2113_);
lean_closure_set(v___f_2127_, 7, v___x_2125_);
lean_closure_set(v___f_2127_, 8, v_tag_2115_);
lean_closure_set(v___f_2127_, 9, v_opts_2116_);
lean_closure_set(v___f_2127_, 10, v___x_2126_);
lean_closure_set(v___f_2127_, 11, v_msg_2117_);
lean_closure_set(v___f_2127_, 12, v_toBind_2118_);
lean_closure_set(v___f_2127_, 13, v_k_2119_);
lean_closure_set(v___f_2127_, 14, v___f_2120_);
lean_closure_set(v___f_2127_, 15, v___f_2121_);
lean_closure_set(v___f_2127_, 16, v_inst_2122_);
lean_closure_set(v___f_2127_, 17, v_toPure_2123_);
if (v_clsEnabled_2124_ == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2131_ = l_Lean_KVMap_instValueBool;
v___x_2132_ = l_Lean_trace_profiler;
v___x_2133_ = l_Lean_Option_get___redArg(v___x_2131_, v_opts_2116_, v___x_2132_);
lean_dec_ref(v_opts_2116_);
v___x_2134_ = lean_unbox(v___x_2133_);
lean_dec(v___x_2133_);
if (v___x_2134_ == 0)
{
lean_dec_ref(v___f_2127_);
lean_dec(v_toBind_2118_);
lean_dec_ref(v_inst_2109_);
lean_dec_ref(v_inst_2108_);
return v_k_2119_;
}
else
{
lean_dec(v_k_2119_);
goto v___jp_2128_;
}
}
else
{
lean_dec(v_k_2119_);
lean_dec_ref(v_opts_2116_);
goto v___jp_2128_;
}
v___jp_2128_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_2108_, v_inst_2109_);
v___x_2130_ = lean_apply_4(v_toBind_2118_, lean_box(0), lean_box(0), v___x_2129_, v___f_2127_);
return v___x_2130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_inst_2135_ = _args[0];
lean_object* v_inst_2136_ = _args[1];
lean_object* v_inst_2137_ = _args[2];
lean_object* v_inst_2138_ = _args[3];
lean_object* v_inst_2139_ = _args[4];
lean_object* v___f_2140_ = _args[5];
lean_object* v_cls_2141_ = _args[6];
lean_object* v_collapsed_2142_ = _args[7];
lean_object* v_tag_2143_ = _args[8];
lean_object* v_opts_2144_ = _args[9];
lean_object* v_msg_2145_ = _args[10];
lean_object* v_toBind_2146_ = _args[11];
lean_object* v_k_2147_ = _args[12];
lean_object* v___f_2148_ = _args[13];
lean_object* v___f_2149_ = _args[14];
lean_object* v_inst_2150_ = _args[15];
lean_object* v_toPure_2151_ = _args[16];
lean_object* v_clsEnabled_2152_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2153_; uint8_t v_clsEnabled_boxed_2154_; lean_object* v_res_2155_; 
v_collapsed_boxed_2153_ = lean_unbox(v_collapsed_2142_);
v_clsEnabled_boxed_2154_ = lean_unbox(v_clsEnabled_2152_);
v_res_2155_ = l_Lean_withTraceNode_x27___redArg___lam__12(v_inst_2135_, v_inst_2136_, v_inst_2137_, v_inst_2138_, v_inst_2139_, v___f_2140_, v_cls_2141_, v_collapsed_boxed_2153_, v_tag_2143_, v_opts_2144_, v_msg_2145_, v_toBind_2146_, v_k_2147_, v___f_2148_, v___f_2149_, v_inst_2150_, v_toPure_2151_, v_clsEnabled_boxed_2154_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object* v_k_2156_, lean_object* v_inst_2157_, lean_object* v_inst_2158_, lean_object* v_inst_2159_, lean_object* v_inst_2160_, lean_object* v_inst_2161_, lean_object* v___f_2162_, lean_object* v_cls_2163_, uint8_t v_collapsed_2164_, lean_object* v_tag_2165_, lean_object* v_msg_2166_, lean_object* v_toBind_2167_, lean_object* v___f_2168_, lean_object* v___f_2169_, lean_object* v_inst_2170_, lean_object* v_toPure_2171_, lean_object* v___f_2172_, lean_object* v_opts_2173_){
_start:
{
uint8_t v_hasTrace_2174_; 
v_hasTrace_2174_ = lean_ctor_get_uint8(v_opts_2173_, sizeof(void*)*1);
if (v_hasTrace_2174_ == 0)
{
lean_dec_ref(v_opts_2173_);
lean_dec(v___f_2172_);
lean_dec(v_toPure_2171_);
lean_dec(v_inst_2170_);
lean_dec(v___f_2169_);
lean_dec(v___f_2168_);
lean_dec(v_toBind_2167_);
lean_dec(v_msg_2166_);
lean_dec_ref(v_tag_2165_);
lean_dec(v_cls_2163_);
lean_dec_ref(v___f_2162_);
lean_dec(v_inst_2161_);
lean_dec_ref(v_inst_2160_);
lean_dec_ref(v_inst_2159_);
lean_dec_ref(v_inst_2158_);
lean_dec_ref(v_inst_2157_);
return v_k_2156_;
}
else
{
lean_object* v_getInheritedTraceOptions_2175_; lean_object* v___x_2176_; lean_object* v___f_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v_getInheritedTraceOptions_2175_ = lean_ctor_get(v_inst_2157_, 2);
lean_inc(v_getInheritedTraceOptions_2175_);
v___x_2176_ = lean_box(v_collapsed_2164_);
lean_inc_n(v_toBind_2167_, 2);
v___f_2177_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_2177_, 0, v_inst_2158_);
lean_closure_set(v___f_2177_, 1, v_inst_2159_);
lean_closure_set(v___f_2177_, 2, v_inst_2157_);
lean_closure_set(v___f_2177_, 3, v_inst_2160_);
lean_closure_set(v___f_2177_, 4, v_inst_2161_);
lean_closure_set(v___f_2177_, 5, v___f_2162_);
lean_closure_set(v___f_2177_, 6, v_cls_2163_);
lean_closure_set(v___f_2177_, 7, v___x_2176_);
lean_closure_set(v___f_2177_, 8, v_tag_2165_);
lean_closure_set(v___f_2177_, 9, v_opts_2173_);
lean_closure_set(v___f_2177_, 10, v_msg_2166_);
lean_closure_set(v___f_2177_, 11, v_toBind_2167_);
lean_closure_set(v___f_2177_, 12, v_k_2156_);
lean_closure_set(v___f_2177_, 13, v___f_2168_);
lean_closure_set(v___f_2177_, 14, v___f_2169_);
lean_closure_set(v___f_2177_, 15, v_inst_2170_);
lean_closure_set(v___f_2177_, 16, v_toPure_2171_);
v___x_2178_ = lean_apply_4(v_toBind_2167_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2175_, v___f_2172_);
v___x_2179_ = lean_apply_4(v_toBind_2167_, lean_box(0), lean_box(0), v___x_2178_, v___f_2177_);
return v___x_2179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_k_2180_ = _args[0];
lean_object* v_inst_2181_ = _args[1];
lean_object* v_inst_2182_ = _args[2];
lean_object* v_inst_2183_ = _args[3];
lean_object* v_inst_2184_ = _args[4];
lean_object* v_inst_2185_ = _args[5];
lean_object* v___f_2186_ = _args[6];
lean_object* v_cls_2187_ = _args[7];
lean_object* v_collapsed_2188_ = _args[8];
lean_object* v_tag_2189_ = _args[9];
lean_object* v_msg_2190_ = _args[10];
lean_object* v_toBind_2191_ = _args[11];
lean_object* v___f_2192_ = _args[12];
lean_object* v___f_2193_ = _args[13];
lean_object* v_inst_2194_ = _args[14];
lean_object* v_toPure_2195_ = _args[15];
lean_object* v___f_2196_ = _args[16];
lean_object* v_opts_2197_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2198_; lean_object* v_res_2199_; 
v_collapsed_boxed_2198_ = lean_unbox(v_collapsed_2188_);
v_res_2199_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_k_2180_, v_inst_2181_, v_inst_2182_, v_inst_2183_, v_inst_2184_, v_inst_2185_, v___f_2186_, v_cls_2187_, v_collapsed_boxed_2198_, v_tag_2189_, v_msg_2190_, v_toBind_2191_, v___f_2192_, v___f_2193_, v_inst_2194_, v_toPure_2195_, v___f_2196_, v_opts_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object* v_inst_2201_, lean_object* v_inst_2202_, lean_object* v_inst_2203_, lean_object* v_inst_2204_, lean_object* v_inst_2205_, lean_object* v_inst_2206_, lean_object* v_inst_2207_, lean_object* v_cls_2208_, lean_object* v_k_2209_, uint8_t v_collapsed_2210_, lean_object* v_tag_2211_){
_start:
{
lean_object* v_toApplicative_2212_; lean_object* v_toFunctor_2213_; lean_object* v_toBind_2214_; lean_object* v_toPure_2215_; lean_object* v_map_2216_; lean_object* v___f_2217_; lean_object* v_msg_2218_; lean_object* v___f_2219_; lean_object* v___f_2220_; lean_object* v___f_2221_; lean_object* v___f_2222_; lean_object* v___x_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_toApplicative_2212_ = lean_ctor_get(v_inst_2201_, 0);
v_toFunctor_2213_ = lean_ctor_get(v_toApplicative_2212_, 0);
v_toBind_2214_ = lean_ctor_get(v_inst_2201_, 1);
lean_inc_n(v_toBind_2214_, 3);
v_toPure_2215_ = lean_ctor_get(v_toApplicative_2212_, 1);
lean_inc_n(v_toPure_2215_, 5);
v_map_2216_ = lean_ctor_get(v_toFunctor_2213_, 0);
lean_inc(v_map_2216_);
v___f_2217_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2218_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2218_, 0, v_toPure_2215_);
lean_inc(v_inst_2205_);
lean_inc(v_cls_2208_);
v___f_2219_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2219_, 0, v_toPure_2215_);
lean_closure_set(v___f_2219_, 1, v_cls_2208_);
lean_closure_set(v___f_2219_, 2, v_toBind_2214_);
lean_closure_set(v___f_2219_, 3, v_inst_2205_);
v___f_2220_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2220_, 0, v_toPure_2215_);
v___f_2221_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2221_, 0, v_toPure_2215_);
v___f_2222_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2223_ = lean_box(v_collapsed_2210_);
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2224_, 0, v_k_2209_);
lean_closure_set(v___f_2224_, 1, v_inst_2202_);
lean_closure_set(v___f_2224_, 2, v_inst_2206_);
lean_closure_set(v___f_2224_, 3, v_inst_2201_);
lean_closure_set(v___f_2224_, 4, v_inst_2203_);
lean_closure_set(v___f_2224_, 5, v_inst_2204_);
lean_closure_set(v___f_2224_, 6, v___f_2222_);
lean_closure_set(v___f_2224_, 7, v_cls_2208_);
lean_closure_set(v___f_2224_, 8, v___x_2223_);
lean_closure_set(v___f_2224_, 9, v_tag_2211_);
lean_closure_set(v___f_2224_, 10, v_msg_2218_);
lean_closure_set(v___f_2224_, 11, v_toBind_2214_);
lean_closure_set(v___f_2224_, 12, v___f_2221_);
lean_closure_set(v___f_2224_, 13, v___f_2220_);
lean_closure_set(v___f_2224_, 14, v_inst_2207_);
lean_closure_set(v___f_2224_, 15, v_toPure_2215_);
lean_closure_set(v___f_2224_, 16, v___f_2219_);
v___x_2225_ = lean_apply_4(v_toBind_2214_, lean_box(0), lean_box(0), v_inst_2205_, v___f_2224_);
v___x_2226_ = lean_apply_4(v_map_2216_, lean_box(0), lean_box(0), v___f_2217_, v___x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object* v_inst_2227_, lean_object* v_inst_2228_, lean_object* v_inst_2229_, lean_object* v_inst_2230_, lean_object* v_inst_2231_, lean_object* v_inst_2232_, lean_object* v_inst_2233_, lean_object* v_cls_2234_, lean_object* v_k_2235_, lean_object* v_collapsed_2236_, lean_object* v_tag_2237_){
_start:
{
uint8_t v_collapsed_boxed_2238_; lean_object* v_res_2239_; 
v_collapsed_boxed_2238_ = lean_unbox(v_collapsed_2236_);
v_res_2239_ = l_Lean_withTraceNode_x27___redArg(v_inst_2227_, v_inst_2228_, v_inst_2229_, v_inst_2230_, v_inst_2231_, v_inst_2232_, v_inst_2233_, v_cls_2234_, v_k_2235_, v_collapsed_boxed_2238_, v_tag_2237_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object* v_00_u03b1_2240_, lean_object* v_m_2241_, lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v_inst_2244_, lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v_inst_2247_, lean_object* v_inst_2248_, lean_object* v_cls_2249_, lean_object* v_k_2250_, uint8_t v_collapsed_2251_, lean_object* v_tag_2252_){
_start:
{
lean_object* v_toApplicative_2253_; lean_object* v_toFunctor_2254_; lean_object* v_toBind_2255_; lean_object* v_toPure_2256_; lean_object* v_map_2257_; lean_object* v___f_2258_; lean_object* v_msg_2259_; lean_object* v___f_2260_; lean_object* v___f_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; lean_object* v___f_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_toApplicative_2253_ = lean_ctor_get(v_inst_2242_, 0);
v_toFunctor_2254_ = lean_ctor_get(v_toApplicative_2253_, 0);
v_toBind_2255_ = lean_ctor_get(v_inst_2242_, 1);
lean_inc_n(v_toBind_2255_, 3);
v_toPure_2256_ = lean_ctor_get(v_toApplicative_2253_, 1);
lean_inc_n(v_toPure_2256_, 5);
v_map_2257_ = lean_ctor_get(v_toFunctor_2254_, 0);
lean_inc(v_map_2257_);
v___f_2258_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2259_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2259_, 0, v_toPure_2256_);
lean_inc(v_inst_2246_);
lean_inc(v_cls_2249_);
v___f_2260_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2260_, 0, v_toPure_2256_);
lean_closure_set(v___f_2260_, 1, v_cls_2249_);
lean_closure_set(v___f_2260_, 2, v_toBind_2255_);
lean_closure_set(v___f_2260_, 3, v_inst_2246_);
v___f_2261_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2261_, 0, v_toPure_2256_);
v___f_2262_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2262_, 0, v_toPure_2256_);
v___f_2263_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2264_ = lean_box(v_collapsed_2251_);
v___f_2265_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2265_, 0, v_k_2250_);
lean_closure_set(v___f_2265_, 1, v_inst_2243_);
lean_closure_set(v___f_2265_, 2, v_inst_2247_);
lean_closure_set(v___f_2265_, 3, v_inst_2242_);
lean_closure_set(v___f_2265_, 4, v_inst_2244_);
lean_closure_set(v___f_2265_, 5, v_inst_2245_);
lean_closure_set(v___f_2265_, 6, v___f_2263_);
lean_closure_set(v___f_2265_, 7, v_cls_2249_);
lean_closure_set(v___f_2265_, 8, v___x_2264_);
lean_closure_set(v___f_2265_, 9, v_tag_2252_);
lean_closure_set(v___f_2265_, 10, v_msg_2259_);
lean_closure_set(v___f_2265_, 11, v_toBind_2255_);
lean_closure_set(v___f_2265_, 12, v___f_2262_);
lean_closure_set(v___f_2265_, 13, v___f_2261_);
lean_closure_set(v___f_2265_, 14, v_inst_2248_);
lean_closure_set(v___f_2265_, 15, v_toPure_2256_);
lean_closure_set(v___f_2265_, 16, v___f_2260_);
v___x_2266_ = lean_apply_4(v_toBind_2255_, lean_box(0), lean_box(0), v_inst_2246_, v___f_2265_);
v___x_2267_ = lean_apply_4(v_map_2257_, lean_box(0), lean_box(0), v___f_2258_, v___x_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object* v_00_u03b1_2268_, lean_object* v_m_2269_, lean_object* v_inst_2270_, lean_object* v_inst_2271_, lean_object* v_inst_2272_, lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_cls_2277_, lean_object* v_k_2278_, lean_object* v_collapsed_2279_, lean_object* v_tag_2280_){
_start:
{
uint8_t v_collapsed_boxed_2281_; lean_object* v_res_2282_; 
v_collapsed_boxed_2281_ = lean_unbox(v_collapsed_2279_);
v_res_2282_ = l_Lean_withTraceNode_x27(v_00_u03b1_2268_, v_m_2269_, v_inst_2270_, v_inst_2271_, v_inst_2272_, v_inst_2273_, v_inst_2274_, v_inst_2275_, v_inst_2276_, v_cls_2277_, v_k_2278_, v_collapsed_boxed_2281_, v_tag_2280_);
return v_res_2282_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__4(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__3));
v___x_2292_ = l_Lean_mkAtom(v___x_2291_);
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__5(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__4, &l_Lean_registerTraceClass___auto__1___closed__4_once, _init_l_Lean_registerTraceClass___auto__1___closed__4);
v___x_2294_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2295_ = lean_array_push(v___x_2294_, v___x_2293_);
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__6(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2296_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__5, &l_Lean_registerTraceClass___auto__1___closed__5_once, _init_l_Lean_registerTraceClass___auto__1___closed__5);
v___x_2297_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__2));
v___x_2298_ = lean_box(2);
v___x_2299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v___x_2297_);
lean_ctor_set(v___x_2299_, 2, v___x_2296_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__7(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__6, &l_Lean_registerTraceClass___auto__1___closed__6_once, _init_l_Lean_registerTraceClass___auto__1___closed__6);
v___x_2301_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_2302_ = lean_array_push(v___x_2301_, v___x_2300_);
return v___x_2302_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2303_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__7, &l_Lean_registerTraceClass___auto__1___closed__7_once, _init_l_Lean_registerTraceClass___auto__1___closed__7);
v___x_2304_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_2305_ = lean_box(2);
v___x_2306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v___x_2304_);
lean_ctor_set(v___x_2306_, 2, v___x_2303_);
return v___x_2306_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2307_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__8, &l_Lean_registerTraceClass___auto__1___closed__8_once, _init_l_Lean_registerTraceClass___auto__1___closed__8);
v___x_2308_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2309_ = lean_array_push(v___x_2308_, v___x_2307_);
return v___x_2309_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2310_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__9, &l_Lean_registerTraceClass___auto__1___closed__9_once, _init_l_Lean_registerTraceClass___auto__1___closed__9);
v___x_2311_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2312_ = lean_box(2);
v___x_2313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
lean_ctor_set(v___x_2313_, 1, v___x_2311_);
lean_ctor_set(v___x_2313_, 2, v___x_2310_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__11(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__10, &l_Lean_registerTraceClass___auto__1___closed__10_once, _init_l_Lean_registerTraceClass___auto__1___closed__10);
v___x_2315_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2316_ = lean_array_push(v___x_2315_, v___x_2314_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2317_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__11, &l_Lean_registerTraceClass___auto__1___closed__11_once, _init_l_Lean_registerTraceClass___auto__1___closed__11);
v___x_2318_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_2319_ = lean_box(2);
v___x_2320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
lean_ctor_set(v___x_2320_, 1, v___x_2318_);
lean_ctor_set(v___x_2320_, 2, v___x_2317_);
return v___x_2320_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__12, &l_Lean_registerTraceClass___auto__1___closed__12_once, _init_l_Lean_registerTraceClass___auto__1___closed__12);
v___x_2322_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2323_ = lean_array_push(v___x_2322_, v___x_2321_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2324_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__13, &l_Lean_registerTraceClass___auto__1___closed__13_once, _init_l_Lean_registerTraceClass___auto__1___closed__13);
v___x_2325_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_2326_ = lean_box(2);
v___x_2327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2325_);
lean_ctor_set(v___x_2327_, 2, v___x_2324_);
return v___x_2327_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1(void){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__14, &l_Lean_registerTraceClass___auto__1___closed__14_once, _init_l_Lean_registerTraceClass___auto__1___closed__14);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object* v_b_2329_, lean_object* v_acc_2330_, lean_object* v_i_2331_){
_start:
{
lean_object* v___y_2333_; lean_object* v_keyArray_2341_; lean_object* v_valueArray_2342_; lean_object* v___x_2343_; uint8_t v___x_2344_; 
v_keyArray_2341_ = lean_ctor_get(v_b_2329_, 1);
v_valueArray_2342_ = lean_ctor_get(v_b_2329_, 2);
v___x_2343_ = lean_array_get_size(v_keyArray_2341_);
v___x_2344_ = lean_nat_dec_lt(v_i_2331_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_dec(v_i_2331_);
return v_acc_2330_;
}
else
{
lean_object* v___x_2345_; uint8_t v_isSome_2346_; 
v___x_2345_ = lean_array_fget_borrowed(v_keyArray_2341_, v_i_2331_);
v_isSome_2346_ = lean_noption_is_some(v___x_2345_);
if (v_isSome_2346_ == 0)
{
goto v___jp_2337_;
}
else
{
lean_object* v___x_2347_; uint8_t v_isSome_2348_; 
v___x_2347_ = lean_array_fget_borrowed(v_valueArray_2342_, v_i_2331_);
v_isSome_2348_ = lean_noption_is_some(v___x_2347_);
if (v_isSome_2348_ == 0)
{
goto v___jp_2337_;
}
else
{
lean_object* v_val_2349_; lean_object* v_val_2350_; lean_object* v_i_2352_; lean_object* v___x_2357_; 
lean_inc(v___x_2345_);
v_val_2349_ = lean_noption_get(v___x_2345_);
lean_inc(v___x_2347_);
v_val_2350_ = lean_noption_get(v___x_2347_);
v___x_2357_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___redArg(v_acc_2330_, v_val_2349_);
switch(lean_obj_tag(v___x_2357_))
{
case 0:
{
lean_object* v_index_2358_; lean_object* v_size_2359_; lean_object* v___x_2360_; 
v_index_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_index_2358_);
lean_dec_ref_known(v___x_2357_, 3);
v_size_2359_ = lean_ctor_get(v_acc_2330_, 0);
lean_inc(v_size_2359_);
v___x_2360_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2330_, v_size_2359_, v_index_2358_, v_val_2349_, v_val_2350_);
lean_dec(v_index_2358_);
v___y_2333_ = v___x_2360_;
goto v___jp_2332_;
}
case 1:
{
lean_object* v_index_2361_; 
v_index_2361_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_index_2361_);
lean_dec_ref_known(v___x_2357_, 1);
v_i_2352_ = v_index_2361_;
goto v___jp_2351_;
}
default: 
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2330_, v___x_2362_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_index_2364_; 
v_index_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_index_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v_i_2352_ = v_index_2364_;
goto v___jp_2351_;
}
else
{
lean_dec(v_val_2350_);
lean_dec(v_val_2349_);
v___y_2333_ = v_acc_2330_;
goto v___jp_2332_;
}
}
}
v___jp_2351_:
{
lean_object* v_size_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_size_2353_ = lean_ctor_get(v_acc_2330_, 0);
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = lean_nat_add(v_size_2353_, v___x_2354_);
v___x_2356_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2330_, v___x_2355_, v_i_2352_, v_val_2349_, v_val_2350_);
lean_dec(v_i_2352_);
v___y_2333_ = v___x_2356_;
goto v___jp_2332_;
}
}
}
}
v___jp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_unsigned_to_nat(1u);
v___x_2335_ = lean_nat_add(v_i_2331_, v___x_2334_);
lean_dec(v_i_2331_);
v_acc_2330_ = v___y_2333_;
v_i_2331_ = v___x_2335_;
goto _start;
}
v___jp_2337_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_unsigned_to_nat(1u);
v___x_2339_ = lean_nat_add(v_i_2331_, v___x_2338_);
lean_dec(v_i_2331_);
v_i_2331_ = v___x_2339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_b_2365_, lean_object* v_acc_2366_, lean_object* v_i_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_b_2365_, v_acc_2366_, v_i_2367_);
lean_dec_ref(v_b_2365_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object* v_init_2369_, lean_object* v_b_2370_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_unsigned_to_nat(0u);
v___x_2372_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_b_2370_, v_init_2369_, v___x_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0___redArg___boxed(lean_object* v_init_2373_, lean_object* v_b_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_init_2373_, v_b_2374_);
lean_dec_ref(v_b_2374_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0___redArg(lean_object* v_m_2376_){
_start:
{
lean_object* v_keyArray_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v_cellCount_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v_target_2384_; lean_object* v___x_2385_; 
v_keyArray_2377_ = lean_ctor_get(v_m_2376_, 1);
v___x_2378_ = lean_array_get_size(v_keyArray_2377_);
v___x_2379_ = lean_unsigned_to_nat(2u);
v_cellCount_2380_ = lean_nat_mul(v___x_2378_, v___x_2379_);
v___x_2381_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2380_);
v___x_2382_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2380_);
v___x_2383_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2380_);
v_target_2384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2384_, 0, v___x_2381_);
lean_ctor_set(v_target_2384_, 1, v___x_2382_);
lean_ctor_set(v_target_2384_, 2, v___x_2383_);
v___x_2385_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_target_2384_, v_m_2376_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0___redArg___boxed(lean_object* v_m_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0___redArg(v_m_2386_);
lean_dec_ref(v_m_2386_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object* v_traceClassName_2391_, uint8_t v_inherited_2392_, lean_object* v_ref_2393_){
_start:
{
lean_object* v___x_2395_; lean_object* v_optionName_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2395_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v_optionName_2396_ = l_Lean_Name_append(v___x_2395_, v_traceClassName_2391_);
v___x_2397_ = ((lean_object*)(l_Lean_registerTraceClass___closed__0));
v___x_2398_ = ((lean_object*)(l_Lean_registerTraceClass___closed__1));
v___x_2399_ = lean_box(0);
lean_inc_n(v_optionName_2396_, 2);
v___x_2400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2400_, 0, v_optionName_2396_);
lean_ctor_set(v___x_2400_, 1, v_ref_2393_);
lean_ctor_set(v___x_2400_, 2, v___x_2397_);
lean_ctor_set(v___x_2400_, 3, v___x_2398_);
lean_ctor_set(v___x_2400_, 4, v___x_2399_);
v___x_2401_ = lean_register_option(v_optionName_2396_, v___x_2400_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2479_; 
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v___x_2401_, 0);
lean_dec(v_unused_2480_);
v___x_2403_ = v___x_2401_;
v_isShared_2404_ = v_isSharedCheck_2479_;
goto v_resetjp_2402_;
}
else
{
lean_dec(v___x_2401_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2479_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
if (v_inherited_2392_ == 0)
{
lean_object* v___x_2405_; lean_object* v___x_2407_; 
lean_dec(v_optionName_2396_);
v___x_2405_ = lean_box(0);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2405_);
v___x_2407_ = v___x_2403_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
else
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___y_2412_; lean_object* v___x_2417_; lean_object* v___y_2419_; lean_object* v_i_2420_; lean_object* v___y_2426_; lean_object* v___y_2436_; lean_object* v_i_2437_; lean_object* v___x_2452_; 
v___x_2409_ = l_Lean_inheritedTraceOptions;
v___x_2410_ = lean_st_ref_take(v___x_2409_);
v___x_2417_ = lean_box(0);
v___x_2452_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___redArg(v___x_2410_, v_optionName_2396_);
switch(lean_obj_tag(v___x_2452_))
{
case 0:
{
lean_dec_ref_known(v___x_2452_, 3);
lean_dec(v_optionName_2396_);
v___y_2412_ = v___x_2410_;
goto v___jp_2411_;
}
case 1:
{
lean_object* v_index_2453_; lean_object* v_size_2454_; lean_object* v_keyArray_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v_index_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_index_2453_);
lean_dec_ref_known(v___x_2452_, 1);
v_size_2454_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_size_2454_);
v_keyArray_2455_ = lean_ctor_get(v___x_2410_, 1);
lean_inc_ref(v_keyArray_2455_);
v___x_2456_ = lean_unsigned_to_nat(1u);
v___x_2457_ = lean_nat_add(v_size_2454_, v___x_2456_);
lean_dec(v_size_2454_);
v___x_2458_ = lean_array_get_size(v_keyArray_2455_);
lean_dec_ref(v_keyArray_2455_);
v___x_2459_ = lean_nat_dec_lt(v___x_2457_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_dec(v___x_2457_);
lean_dec(v_index_2453_);
goto v___jp_2442_;
}
else
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2460_ = lean_unsigned_to_nat(4u);
v___x_2461_ = lean_nat_mul(v___x_2457_, v___x_2460_);
v___x_2462_ = lean_unsigned_to_nat(3u);
v___x_2463_ = lean_nat_mul(v___x_2458_, v___x_2462_);
v___x_2464_ = lean_nat_dec_le(v___x_2461_, v___x_2463_);
lean_dec(v___x_2463_);
lean_dec(v___x_2461_);
if (v___x_2464_ == 0)
{
lean_dec(v___x_2457_);
lean_dec(v_index_2453_);
goto v___jp_2442_;
}
else
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2410_, v___x_2457_, v_index_2453_, v_optionName_2396_, v___x_2417_);
lean_dec(v_index_2453_);
v___y_2412_ = v___x_2465_;
goto v___jp_2411_;
}
}
}
default: 
{
lean_object* v_size_2466_; lean_object* v_keyArray_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v_size_2466_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_size_2466_);
v_keyArray_2467_ = lean_ctor_get(v___x_2410_, 1);
lean_inc_ref(v_keyArray_2467_);
v___x_2468_ = lean_unsigned_to_nat(1u);
v___x_2469_ = lean_nat_add(v_size_2466_, v___x_2468_);
lean_dec(v_size_2466_);
v___x_2470_ = lean_array_get_size(v_keyArray_2467_);
lean_dec_ref(v_keyArray_2467_);
v___x_2471_ = lean_nat_dec_lt(v___x_2469_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
lean_dec(v___x_2469_);
v___x_2472_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2410_);
lean_dec(v___x_2410_);
v___y_2426_ = v___x_2472_;
goto v___jp_2425_;
}
else
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2473_ = lean_unsigned_to_nat(4u);
v___x_2474_ = lean_nat_mul(v___x_2469_, v___x_2473_);
lean_dec(v___x_2469_);
v___x_2475_ = lean_unsigned_to_nat(3u);
v___x_2476_ = lean_nat_mul(v___x_2470_, v___x_2475_);
v___x_2477_ = lean_nat_dec_le(v___x_2474_, v___x_2476_);
lean_dec(v___x_2476_);
lean_dec(v___x_2474_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2410_);
lean_dec(v___x_2410_);
v___y_2426_ = v___x_2478_;
goto v___jp_2425_;
}
else
{
v___y_2426_ = v___x_2410_;
goto v___jp_2425_;
}
}
}
}
v___jp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = lean_st_ref_put(v___x_2409_, v___y_2412_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2413_);
v___x_2415_ = v___x_2403_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
v___jp_2418_:
{
lean_object* v_size_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v_size_2421_ = lean_ctor_get(v___y_2419_, 0);
v___x_2422_ = lean_unsigned_to_nat(1u);
v___x_2423_ = lean_nat_add(v_size_2421_, v___x_2422_);
v___x_2424_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2419_, v___x_2423_, v_i_2420_, v_optionName_2396_, v___x_2417_);
lean_dec(v_i_2420_);
v___y_2412_ = v___x_2424_;
goto v___jp_2411_;
}
v___jp_2425_:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___redArg(v___y_2426_, v_optionName_2396_);
switch(lean_obj_tag(v___x_2427_))
{
case 0:
{
lean_object* v_index_2428_; lean_object* v_size_2429_; lean_object* v___x_2430_; 
v_index_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_index_2428_);
lean_dec_ref_known(v___x_2427_, 3);
v_size_2429_ = lean_ctor_get(v___y_2426_, 0);
lean_inc(v_size_2429_);
v___x_2430_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2426_, v_size_2429_, v_index_2428_, v_optionName_2396_, v___x_2417_);
lean_dec(v_index_2428_);
v___y_2412_ = v___x_2430_;
goto v___jp_2411_;
}
case 1:
{
lean_object* v_index_2431_; 
v_index_2431_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_index_2431_);
lean_dec_ref_known(v___x_2427_, 1);
v___y_2419_ = v___y_2426_;
v_i_2420_ = v_index_2431_;
goto v___jp_2418_;
}
default: 
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_unsigned_to_nat(0u);
v___x_2433_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2426_, v___x_2432_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_index_2434_; 
v_index_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_index_2434_);
lean_dec_ref_known(v___x_2433_, 1);
v___y_2419_ = v___y_2426_;
v_i_2420_ = v_index_2434_;
goto v___jp_2418_;
}
else
{
lean_dec(v_optionName_2396_);
v___y_2412_ = v___y_2426_;
goto v___jp_2411_;
}
}
}
}
v___jp_2435_:
{
lean_object* v_size_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v_size_2438_ = lean_ctor_get(v___y_2436_, 0);
v___x_2439_ = lean_unsigned_to_nat(1u);
v___x_2440_ = lean_nat_add(v_size_2438_, v___x_2439_);
v___x_2441_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2436_, v___x_2440_, v_i_2437_, v_optionName_2396_, v___x_2417_);
lean_dec(v_i_2437_);
v___y_2412_ = v___x_2441_;
goto v___jp_2411_;
}
v___jp_2442_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2410_);
lean_dec(v___x_2410_);
v___x_2444_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_spec__1___redArg(v___x_2443_, v_optionName_2396_);
switch(lean_obj_tag(v___x_2444_))
{
case 0:
{
lean_object* v_index_2445_; lean_object* v_size_2446_; lean_object* v___x_2447_; 
v_index_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_index_2445_);
lean_dec_ref_known(v___x_2444_, 3);
v_size_2446_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_size_2446_);
v___x_2447_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2443_, v_size_2446_, v_index_2445_, v_optionName_2396_, v___x_2417_);
lean_dec(v_index_2445_);
v___y_2412_ = v___x_2447_;
goto v___jp_2411_;
}
case 1:
{
lean_object* v_index_2448_; 
v_index_2448_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_index_2448_);
lean_dec_ref_known(v___x_2444_, 1);
v___y_2436_ = v___x_2443_;
v_i_2437_ = v_index_2448_;
goto v___jp_2435_;
}
default: 
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_unsigned_to_nat(0u);
v___x_2450_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2443_, v___x_2449_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_index_2451_; 
v_index_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_index_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v___y_2436_ = v___x_2443_;
v_i_2437_ = v_index_2451_;
goto v___jp_2435_;
}
else
{
lean_dec(v_optionName_2396_);
v___y_2412_ = v___x_2443_;
goto v___jp_2411_;
}
}
}
}
}
}
}
else
{
lean_dec(v_optionName_2396_);
return v___x_2401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object* v_traceClassName_2481_, lean_object* v_inherited_2482_, lean_object* v_ref_2483_, lean_object* v_a_2484_){
_start:
{
uint8_t v_inherited_boxed_2485_; lean_object* v_res_2486_; 
v_inherited_boxed_2485_ = lean_unbox(v_inherited_2482_);
v_res_2486_ = l_Lean_registerTraceClass(v_traceClassName_2481_, v_inherited_boxed_2485_, v_ref_2483_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0(lean_object* v_00_u03b2_2487_, lean_object* v_m_2488_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0___redArg(v_m_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0___boxed(lean_object* v_00_u03b2_2490_, lean_object* v_m_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0(v_00_u03b2_2490_, v_m_2491_);
lean_dec_ref(v_m_2491_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object* v_00_u03b2_2493_, lean_object* v_init_2494_, lean_object* v_b_2495_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_init_2494_, v_b_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2497_, lean_object* v_init_2498_, lean_object* v_b_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0(v_00_u03b2_2497_, v_init_2498_, v_b_2499_);
lean_dec_ref(v_b_2499_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2501_, lean_object* v_b_2502_, lean_object* v_acc_2503_, lean_object* v_i_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_b_2502_, v_acc_2503_, v_i_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2506_, lean_object* v_b_2507_, lean_object* v_acc_2508_, lean_object* v_i_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(v_00_u03b2_2506_, v_b_2507_, v_acc_2508_, v_i_2509_);
lean_dec_ref(v_b_2507_);
return v_res_2510_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_2521_ = l_String_toRawSubstring_x27(v___x_2520_);
return v___x_2521_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13));
v___x_2528_ = l_String_toRawSubstring_x27(v___x_2527_);
return v___x_2528_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18));
v___x_2534_ = l_String_toRawSubstring_x27(v___x_2533_);
return v___x_2534_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31(void){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Array_mkArray0(lean_box(0));
return v___x_2562_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40));
v___x_2589_ = l_String_toRawSubstring_x27(v___x_2588_);
return v___x_2589_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57));
v___x_2625_ = l_String_toRawSubstring_x27(v___x_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object* v_id_2647_, lean_object* v_s_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v_msg_2748_; lean_object* v_quotContext_2749_; lean_object* v_currMacroScope_2750_; lean_object* v_ref_2751_; lean_object* v___y_2752_; lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
lean_inc(v_s_2648_);
v___x_2798_ = l_Lean_Syntax_getKind(v_s_2648_);
v___x_2799_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49));
v___x_2800_ = lean_name_eq(v___x_2798_, v___x_2799_);
lean_dec(v___x_2798_);
if (v___x_2800_ == 0)
{
lean_object* v_quotContext_2801_; lean_object* v_currMacroScope_2802_; lean_object* v_ref_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v_quotContext_2801_ = lean_ctor_get(v_a_2649_, 1);
v_currMacroScope_2802_ = lean_ctor_get(v_a_2649_, 2);
v_ref_2803_ = lean_ctor_get(v_a_2649_, 5);
v___x_2804_ = l_Lean_SourceInfo_fromRef(v_ref_2803_, v___x_2800_);
v___x_2805_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51));
v___x_2806_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52));
v___x_2807_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
lean_inc_n(v___x_2804_, 8);
v___x_2808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2804_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2810_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2811_ = lean_box(0);
lean_inc_n(v_currMacroScope_2802_, 3);
lean_inc_n(v_quotContext_2801_, 3);
v___x_2812_ = l_Lean_addMacroScope(v_quotContext_2801_, v___x_2811_, v_currMacroScope_2802_);
v___x_2813_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55));
v___x_2814_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2804_);
lean_ctor_set(v___x_2814_, 1, v___x_2810_);
lean_ctor_set(v___x_2814_, 2, v___x_2812_);
lean_ctor_set(v___x_2814_, 3, v___x_2813_);
v___x_2815_ = l_Lean_Syntax_node1(v___x_2804_, v___x_2809_, v___x_2814_);
v___x_2816_ = l_Lean_Syntax_node2(v___x_2804_, v___x_2806_, v___x_2808_, v___x_2815_);
v___x_2817_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56));
v___x_2818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2804_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2820_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58);
v___x_2821_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59));
v___x_2822_ = l_Lean_addMacroScope(v_quotContext_2801_, v___x_2821_, v_currMacroScope_2802_);
v___x_2823_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64));
v___x_2824_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2804_);
lean_ctor_set(v___x_2824_, 1, v___x_2820_);
lean_ctor_set(v___x_2824_, 2, v___x_2822_);
lean_ctor_set(v___x_2824_, 3, v___x_2823_);
v___x_2825_ = l_Lean_Syntax_node1(v___x_2804_, v___x_2819_, v___x_2824_);
v___x_2826_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2804_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = l_Lean_Syntax_node5(v___x_2804_, v___x_2805_, v___x_2816_, v_s_2648_, v___x_2818_, v___x_2825_, v___x_2827_);
v_msg_2748_ = v___x_2828_;
v_quotContext_2749_ = v_quotContext_2801_;
v_currMacroScope_2750_ = v_currMacroScope_2802_;
v_ref_2751_ = v_ref_2803_;
v___y_2752_ = v_a_2650_;
goto v___jp_2747_;
}
else
{
lean_object* v_quotContext_2829_; lean_object* v_currMacroScope_2830_; lean_object* v_ref_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v_quotContext_2829_ = lean_ctor_get(v_a_2649_, 1);
v_currMacroScope_2830_ = lean_ctor_get(v_a_2649_, 2);
v_ref_2831_ = lean_ctor_get(v_a_2649_, 5);
v___x_2832_ = 0;
v___x_2833_ = l_Lean_SourceInfo_fromRef(v_ref_2831_, v___x_2832_);
v___x_2834_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66));
v___x_2835_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67));
lean_inc(v___x_2833_);
v___x_2836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2833_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = l_Lean_Syntax_node2(v___x_2833_, v___x_2834_, v___x_2836_, v_s_2648_);
lean_inc(v_currMacroScope_2830_);
lean_inc(v_quotContext_2829_);
v_msg_2748_ = v___x_2837_;
v_quotContext_2749_ = v_quotContext_2829_;
v_currMacroScope_2750_ = v_currMacroScope_2830_;
v_ref_2751_ = v_ref_2831_;
v___y_2752_ = v_a_2650_;
goto v___jp_2747_;
}
v___jp_2651_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_inc_n(v___y_2669_, 8);
lean_inc(v___y_2660_);
lean_inc_n(v___y_2654_, 30);
v___x_2676_ = l_Lean_Syntax_node5(v___y_2654_, v___y_2660_, v___y_2655_, v___y_2669_, v___y_2669_, v___y_2666_, v___y_2675_);
lean_inc(v___y_2667_);
v___x_2677_ = l_Lean_Syntax_node1(v___y_2654_, v___y_2667_, v___x_2676_);
lean_inc(v___y_2658_);
v___x_2678_ = l_Lean_Syntax_node4(v___y_2654_, v___y_2658_, v___y_2664_, v___y_2669_, v___y_2665_, v___x_2677_);
lean_inc_n(v___y_2657_, 3);
v___x_2679_ = l_Lean_Syntax_node2(v___y_2654_, v___y_2657_, v___x_2678_, v___y_2669_);
v___x_2680_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0));
lean_inc_ref_n(v___y_2671_, 7);
lean_inc_ref_n(v___y_2661_, 7);
lean_inc_ref_n(v___y_2668_, 10);
v___x_2681_ = l_Lean_Name_mkStr4(v___y_2668_, v___y_2661_, v___y_2671_, v___x_2680_);
v___x_2682_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1));
v___x_2683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___y_2654_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2));
v___x_2685_ = l_Lean_Name_mkStr4(v___y_2668_, v___y_2661_, v___y_2671_, v___x_2684_);
v___x_2686_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3));
v___x_2687_ = l_Lean_Name_mkStr4(v___y_2668_, v___y_2661_, v___y_2671_, v___x_2686_);
v___x_2688_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4));
v___x_2689_ = l_Lean_Name_mkStr4(v___y_2668_, v___y_2661_, v___y_2671_, v___x_2688_);
v___x_2690_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
v___x_2691_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___y_2654_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2693_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2694_ = lean_box(0);
lean_inc_n(v___y_2672_, 2);
lean_inc_n(v___y_2653_, 2);
v___x_2695_ = l_Lean_addMacroScope(v___y_2653_, v___x_2694_, v___y_2672_);
v___x_2696_ = l_Lean_Name_mkStr1(v___y_2668_);
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
lean_inc_n(v___y_2656_, 2);
v___x_2698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v___y_2656_);
v___x_2699_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2699_, 0, v___y_2654_);
lean_ctor_set(v___x_2699_, 1, v___x_2693_);
lean_ctor_set(v___x_2699_, 2, v___x_2695_);
lean_ctor_set(v___x_2699_, 3, v___x_2698_);
v___x_2700_ = l_Lean_Syntax_node1(v___y_2654_, v___x_2692_, v___x_2699_);
v___x_2701_ = l_Lean_Syntax_node2(v___y_2654_, v___x_2689_, v___x_2691_, v___x_2700_);
v___x_2702_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9));
v___x_2703_ = l_Lean_Name_mkStr4(v___y_2668_, v___y_2661_, v___y_2671_, v___x_2702_);
v___x_2704_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10));
v___x_2705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___y_2654_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11));
v___x_2707_ = l_Lean_Name_mkStr4(v___y_2668_, v___y_2661_, v___y_2671_, v___x_2706_);
v___x_2708_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12));
v___x_2709_ = l_Lean_Name_mkStr4(v___y_2668_, v___y_2661_, v___y_2671_, v___x_2708_);
v___x_2710_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14);
v___x_2711_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2712_ = l_Lean_Name_mkStr2(v___y_2668_, v___x_2711_);
lean_inc(v___x_2712_);
v___x_2713_ = l_Lean_addMacroScope(v___y_2653_, v___x_2712_, v___y_2672_);
v___x_2714_ = lean_box(0);
v___x_2715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2712_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v___y_2656_);
v___x_2717_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2717_, 0, v___y_2654_);
lean_ctor_set(v___x_2717_, 1, v___x_2710_);
lean_ctor_set(v___x_2717_, 2, v___x_2713_);
lean_ctor_set(v___x_2717_, 3, v___x_2716_);
lean_inc(v___y_2663_);
lean_inc_n(v___y_2662_, 4);
v___x_2718_ = l_Lean_Syntax_node1(v___y_2654_, v___y_2662_, v___y_2663_);
lean_inc(v___x_2709_);
v___x_2719_ = l_Lean_Syntax_node2(v___y_2654_, v___x_2709_, v___x_2717_, v___x_2718_);
lean_inc(v___x_2707_);
v___x_2720_ = l_Lean_Syntax_node1(v___y_2654_, v___x_2707_, v___x_2719_);
v___x_2721_ = l_Lean_Syntax_node2(v___y_2654_, v___x_2703_, v___x_2705_, v___x_2720_);
v___x_2722_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___y_2654_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = l_Lean_Syntax_node3(v___y_2654_, v___x_2687_, v___x_2701_, v___x_2721_, v___x_2723_);
v___x_2725_ = l_Lean_Syntax_node2(v___y_2654_, v___x_2685_, v___y_2669_, v___x_2724_);
v___x_2726_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17));
v___x_2727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___y_2654_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19);
v___x_2729_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20));
v___x_2730_ = l_Lean_Name_mkStr2(v___y_2668_, v___x_2729_);
lean_inc(v___x_2730_);
v___x_2731_ = l_Lean_addMacroScope(v___y_2653_, v___x_2730_, v___y_2672_);
v___x_2732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2730_);
lean_ctor_set(v___x_2732_, 1, v___x_2714_);
v___x_2733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v___y_2656_);
v___x_2734_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2734_, 0, v___y_2654_);
lean_ctor_set(v___x_2734_, 1, v___x_2728_);
lean_ctor_set(v___x_2734_, 2, v___x_2731_);
lean_ctor_set(v___x_2734_, 3, v___x_2733_);
v___x_2735_ = l_Lean_Syntax_node2(v___y_2654_, v___y_2662_, v___y_2663_, v___y_2659_);
v___x_2736_ = l_Lean_Syntax_node2(v___y_2654_, v___x_2709_, v___x_2734_, v___x_2735_);
v___x_2737_ = l_Lean_Syntax_node1(v___y_2654_, v___x_2707_, v___x_2736_);
v___x_2738_ = l_Lean_Syntax_node2(v___y_2654_, v___y_2657_, v___x_2737_, v___y_2669_);
v___x_2739_ = l_Lean_Syntax_node1(v___y_2654_, v___y_2662_, v___x_2738_);
lean_inc_n(v___y_2673_, 2);
v___x_2740_ = l_Lean_Syntax_node1(v___y_2654_, v___y_2673_, v___x_2739_);
v___x_2741_ = l_Lean_Syntax_node6(v___y_2654_, v___x_2681_, v___x_2683_, v___x_2725_, v___x_2727_, v___x_2740_, v___y_2669_, v___y_2669_);
v___x_2742_ = l_Lean_Syntax_node2(v___y_2654_, v___y_2657_, v___x_2741_, v___y_2669_);
v___x_2743_ = l_Lean_Syntax_node2(v___y_2654_, v___y_2662_, v___x_2679_, v___x_2742_);
v___x_2744_ = l_Lean_Syntax_node1(v___y_2654_, v___y_2673_, v___x_2743_);
lean_inc(v___y_2674_);
v___x_2745_ = l_Lean_Syntax_node2(v___y_2654_, v___y_2674_, v___y_2652_, v___x_2744_);
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
lean_ctor_set(v___x_2746_, 1, v___y_2670_);
return v___x_2746_;
}
v___jp_2747_:
{
uint8_t v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2753_ = 0;
v___x_2754_ = l_Lean_SourceInfo_fromRef(v_ref_2751_, v___x_2753_);
v___x_2755_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0));
v___x_2756_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1));
v___x_2757_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__0));
v___x_2758_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22));
v___x_2759_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23));
lean_inc_n(v___x_2754_, 7);
v___x_2760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2754_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25));
v___x_2762_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2763_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27));
v___x_2764_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2765_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
v___x_2766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2754_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31);
v___x_2768_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2754_);
lean_ctor_set(v___x_2768_, 1, v___x_2762_);
lean_ctor_set(v___x_2768_, 2, v___x_2767_);
v___x_2769_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33));
lean_inc_ref(v___x_2768_);
v___x_2770_ = l_Lean_Syntax_node1(v___x_2754_, v___x_2769_, v___x_2768_);
v___x_2771_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35));
v___x_2772_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37));
v___x_2773_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39));
v___x_2774_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41);
v___x_2775_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42));
lean_inc(v_currMacroScope_2750_);
lean_inc(v_quotContext_2749_);
v___x_2776_ = l_Lean_addMacroScope(v_quotContext_2749_, v___x_2775_, v_currMacroScope_2750_);
v___x_2777_ = lean_box(0);
v___x_2778_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2754_);
lean_ctor_set(v___x_2778_, 1, v___x_2774_);
lean_ctor_set(v___x_2778_, 2, v___x_2776_);
lean_ctor_set(v___x_2778_, 3, v___x_2777_);
lean_inc_ref(v___x_2778_);
v___x_2779_ = l_Lean_Syntax_node1(v___x_2754_, v___x_2773_, v___x_2778_);
v___x_2780_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43));
v___x_2781_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2754_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = l_Lean_Syntax_getId(v_id_2647_);
v___x_2783_ = l_Lean_Name_eraseMacroScopes(v___x_2782_);
lean_dec(v___x_2782_);
lean_inc(v___x_2783_);
v___x_2784_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2777_, v___x_2783_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_quoteNameMk(v___x_2783_);
v___y_2652_ = v___x_2760_;
v___y_2653_ = v_quotContext_2749_;
v___y_2654_ = v___x_2754_;
v___y_2655_ = v___x_2779_;
v___y_2656_ = v___x_2777_;
v___y_2657_ = v___x_2763_;
v___y_2658_ = v___x_2764_;
v___y_2659_ = v_msg_2748_;
v___y_2660_ = v___x_2772_;
v___y_2661_ = v___x_2756_;
v___y_2662_ = v___x_2762_;
v___y_2663_ = v___x_2778_;
v___y_2664_ = v___x_2766_;
v___y_2665_ = v___x_2770_;
v___y_2666_ = v___x_2781_;
v___y_2667_ = v___x_2771_;
v___y_2668_ = v___x_2755_;
v___y_2669_ = v___x_2768_;
v___y_2670_ = v___y_2752_;
v___y_2671_ = v___x_2757_;
v___y_2672_ = v_currMacroScope_2750_;
v___y_2673_ = v___x_2761_;
v___y_2674_ = v___x_2758_;
v___y_2675_ = v___x_2785_;
goto v___jp_2651_;
}
else
{
lean_object* v_val_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
lean_dec(v___x_2783_);
v_val_2786_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_val_2786_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2787_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45));
v___x_2788_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46));
v___x_2789_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47));
v___x_2790_ = lean_string_intercalate(v___x_2789_, v_val_2786_);
v___x_2791_ = lean_string_append(v___x_2788_, v___x_2790_);
lean_dec_ref(v___x_2790_);
v___x_2792_ = lean_box(2);
v___x_2793_ = l_Lean_Syntax_mkNameLit(v___x_2791_, v___x_2792_);
v___x_2794_ = lean_unsigned_to_nat(1u);
v___x_2795_ = lean_mk_empty_array_with_capacity(v___x_2794_);
v___x_2796_ = lean_array_push(v___x_2795_, v___x_2793_);
v___x_2797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2792_);
lean_ctor_set(v___x_2797_, 1, v___x_2787_);
lean_ctor_set(v___x_2797_, 2, v___x_2796_);
v___y_2652_ = v___x_2760_;
v___y_2653_ = v_quotContext_2749_;
v___y_2654_ = v___x_2754_;
v___y_2655_ = v___x_2779_;
v___y_2656_ = v___x_2777_;
v___y_2657_ = v___x_2763_;
v___y_2658_ = v___x_2764_;
v___y_2659_ = v_msg_2748_;
v___y_2660_ = v___x_2772_;
v___y_2661_ = v___x_2756_;
v___y_2662_ = v___x_2762_;
v___y_2663_ = v___x_2778_;
v___y_2664_ = v___x_2766_;
v___y_2665_ = v___x_2770_;
v___y_2666_ = v___x_2781_;
v___y_2667_ = v___x_2771_;
v___y_2668_ = v___x_2755_;
v___y_2669_ = v___x_2768_;
v___y_2670_ = v___y_2752_;
v___y_2671_ = v___x_2757_;
v___y_2672_ = v_currMacroScope_2750_;
v___y_2673_ = v___x_2761_;
v___y_2674_ = v___x_2758_;
v___y_2675_ = v___x_2797_;
goto v___jp_2651_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object* v_id_2838_, lean_object* v_s_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v_id_2838_, v_s_2839_, v_a_2840_, v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_id_2838_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object* v_x_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v___x_2900_; uint8_t v___x_2901_; 
v___x_2900_ = ((lean_object*)(l_Lean_doElemTrace_x5b___x5d_____00__closed__1));
lean_inc(v_x_2897_);
v___x_2901_ = l_Lean_Syntax_isOfKind(v_x_2897_, v___x_2900_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
lean_dec(v_x_2897_);
v___x_2902_ = lean_box(1);
v___x_2903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
lean_ctor_set(v___x_2903_, 1, v_a_2899_);
return v___x_2903_;
}
else
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v_a_2909_; lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
v___x_2904_ = lean_unsigned_to_nat(1u);
v___x_2905_ = l_Lean_Syntax_getArg(v_x_2897_, v___x_2904_);
v___x_2906_ = lean_unsigned_to_nat(3u);
v___x_2907_ = l_Lean_Syntax_getArg(v_x_2897_, v___x_2906_);
lean_dec(v_x_2897_);
v___x_2908_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v___x_2905_, v___x_2907_, v_a_2898_, v_a_2899_);
lean_dec(v___x_2905_);
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
v_a_2910_ = lean_ctor_get(v___x_2908_, 1);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2908_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_inc(v_a_2909_);
lean_dec(v___x_2908_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2909_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object* v_x_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(v_x_2918_, v_a_2919_, v_a_2920_);
lean_dec_ref(v_a_2919_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_always_2926_, lean_object* v_inst_2927_, lean_object* v_cls_2928_, uint8_t v_collapsed_2929_, lean_object* v_tag_2930_, lean_object* v_opts_2931_, uint8_t v_clsEnabled_2932_, lean_object* v_oldTraces_2933_, lean_object* v_ref_2934_, lean_object* v_msg_2935_, lean_object* v_resStartStop_2936_){
_start:
{
lean_object* v___x_2937_; lean_object* v_snd_2938_; lean_object* v_fst_2939_; lean_object* v_fst_2940_; lean_object* v_snd_2941_; lean_object* v___f_2942_; lean_object* v___f_2943_; lean_object* v_data_2945_; lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___y_2961_; double v___y_2967_; uint8_t v___x_2972_; 
v___x_2937_ = l_Lean_KVMap_instValueBool;
v_snd_2938_ = lean_ctor_get(v_resStartStop_2936_, 1);
lean_inc(v_snd_2938_);
v_fst_2939_ = lean_ctor_get(v_resStartStop_2936_, 0);
lean_inc_n(v_fst_2939_, 2);
lean_dec_ref(v_resStartStop_2936_);
v_fst_2940_ = lean_ctor_get(v_snd_2938_, 0);
lean_inc(v_fst_2940_);
v_snd_2941_ = lean_ctor_get(v_snd_2938_, 1);
lean_inc(v_snd_2941_);
lean_dec(v_snd_2938_);
lean_inc_ref(v_oldTraces_2933_);
v___f_2942_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2942_, 0, v_oldTraces_2933_);
lean_inc_ref(v_inst_2922_);
v___f_2943_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2943_, 0, v_always_2926_);
lean_closure_set(v___f_2943_, 1, v_inst_2922_);
lean_closure_set(v___f_2943_, 2, v_fst_2939_);
v___x_2949_ = l_Lean_trace_profiler;
v___x_2950_ = l_Lean_Option_get___redArg(v___x_2937_, v_opts_2931_, v___x_2949_);
v___x_2972_ = lean_unbox(v___x_2950_);
if (v___x_2972_ == 0)
{
uint8_t v___x_2973_; 
v___x_2973_ = lean_unbox(v___x_2950_);
v___y_2961_ = v___x_2973_;
goto v___jp_2960_;
}
else
{
lean_object* v___x_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; 
v___x_2974_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2975_ = l_Lean_Option_get___redArg(v___x_2937_, v_opts_2931_, v___x_2974_);
v___x_2976_ = lean_unbox(v___x_2975_);
lean_dec(v___x_2975_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; double v___x_2980_; double v___x_2981_; double v___x_2982_; 
v___x_2977_ = l_Lean_KVMap_instValueNat;
v___x_2978_ = l_Lean_trace_profiler_threshold;
v___x_2979_ = l_Lean_Option_get___redArg(v___x_2977_, v_opts_2931_, v___x_2978_);
v___x_2980_ = lean_float_of_nat(v___x_2979_);
v___x_2981_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_2982_ = lean_float_div(v___x_2980_, v___x_2981_);
v___y_2967_ = v___x_2982_;
goto v___jp_2966_;
}
else
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; double v___x_2986_; 
v___x_2983_ = l_Lean_KVMap_instValueNat;
v___x_2984_ = l_Lean_trace_profiler_threshold;
v___x_2985_ = l_Lean_Option_get___redArg(v___x_2983_, v_opts_2931_, v___x_2984_);
v___x_2986_ = lean_float_of_nat(v___x_2985_);
v___y_2967_ = v___x_2986_;
goto v___jp_2966_;
}
}
v___jp_2944_:
{
lean_object* v_toBind_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_toBind_2946_ = lean_ctor_get(v_inst_2922_, 1);
lean_inc(v_toBind_2946_);
v___x_2947_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_2922_, v_inst_2923_, v_inst_2924_, v_inst_2925_, v_oldTraces_2933_, v_data_2945_, v_ref_2934_, v_msg_2935_);
v___x_2948_ = lean_apply_4(v_toBind_2946_, lean_box(0), lean_box(0), v___x_2947_, v___f_2943_);
return v___x_2948_;
}
v___jp_2951_:
{
lean_object* v_result_2952_; lean_object* v___x_2953_; double v___x_2954_; lean_object* v_data_2955_; uint8_t v___x_2956_; 
v_result_2952_ = lean_apply_1(v_inst_2927_, v_fst_2939_);
v___x_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_result_2952_);
v___x_2954_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_2930_);
lean_inc_ref(v___x_2953_);
lean_inc(v_cls_2928_);
v_data_2955_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2955_, 0, v_cls_2928_);
lean_ctor_set(v_data_2955_, 1, v___x_2953_);
lean_ctor_set(v_data_2955_, 2, v_tag_2930_);
lean_ctor_set_float(v_data_2955_, sizeof(void*)*3, v___x_2954_);
lean_ctor_set_float(v_data_2955_, sizeof(void*)*3 + 8, v___x_2954_);
lean_ctor_set_uint8(v_data_2955_, sizeof(void*)*3 + 16, v_collapsed_2929_);
v___x_2956_ = lean_unbox(v___x_2950_);
lean_dec(v___x_2950_);
if (v___x_2956_ == 0)
{
lean_dec_ref_known(v___x_2953_, 1);
lean_dec(v_snd_2941_);
lean_dec(v_fst_2940_);
lean_dec_ref(v_tag_2930_);
lean_dec(v_cls_2928_);
v_data_2945_ = v_data_2955_;
goto v___jp_2944_;
}
else
{
lean_object* v_data_2957_; double v___x_2958_; double v___x_2959_; 
lean_dec_ref_known(v_data_2955_, 3);
v_data_2957_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2957_, 0, v_cls_2928_);
lean_ctor_set(v_data_2957_, 1, v___x_2953_);
lean_ctor_set(v_data_2957_, 2, v_tag_2930_);
v___x_2958_ = lean_unbox_float(v_fst_2940_);
lean_dec(v_fst_2940_);
lean_ctor_set_float(v_data_2957_, sizeof(void*)*3, v___x_2958_);
v___x_2959_ = lean_unbox_float(v_snd_2941_);
lean_dec(v_snd_2941_);
lean_ctor_set_float(v_data_2957_, sizeof(void*)*3 + 8, v___x_2959_);
lean_ctor_set_uint8(v_data_2957_, sizeof(void*)*3 + 16, v_collapsed_2929_);
v_data_2945_ = v_data_2957_;
goto v___jp_2944_;
}
}
v___jp_2960_:
{
if (v_clsEnabled_2932_ == 0)
{
if (v___y_2961_ == 0)
{
lean_object* v_toBind_2962_; lean_object* v_modifyTraceState_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v___x_2950_);
lean_dec(v_snd_2941_);
lean_dec(v_fst_2940_);
lean_dec(v_fst_2939_);
lean_dec_ref(v_msg_2935_);
lean_dec(v_ref_2934_);
lean_dec_ref(v_oldTraces_2933_);
lean_dec_ref(v_tag_2930_);
lean_dec(v_cls_2928_);
lean_dec_ref(v_inst_2927_);
lean_dec(v_inst_2925_);
lean_dec_ref(v_inst_2924_);
v_toBind_2962_ = lean_ctor_get(v_inst_2922_, 1);
lean_inc(v_toBind_2962_);
lean_dec_ref(v_inst_2922_);
v_modifyTraceState_2963_ = lean_ctor_get(v_inst_2923_, 0);
lean_inc(v_modifyTraceState_2963_);
lean_dec_ref(v_inst_2923_);
v___x_2964_ = lean_apply_1(v_modifyTraceState_2963_, v___f_2942_);
v___x_2965_ = lean_apply_4(v_toBind_2962_, lean_box(0), lean_box(0), v___x_2964_, v___f_2943_);
return v___x_2965_;
}
else
{
lean_dec_ref(v___f_2942_);
goto v___jp_2951_;
}
}
else
{
lean_dec_ref(v___f_2942_);
goto v___jp_2951_;
}
}
v___jp_2966_:
{
double v___x_2968_; double v___x_2969_; double v___x_2970_; uint8_t v___x_2971_; 
v___x_2968_ = lean_unbox_float(v_snd_2941_);
v___x_2969_ = lean_unbox_float(v_fst_2940_);
v___x_2970_ = lean_float_sub(v___x_2968_, v___x_2969_);
v___x_2971_ = lean_float_decLt(v___y_2967_, v___x_2970_);
v___y_2961_ = v___x_2971_;
goto v___jp_2960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_inst_2990_, lean_object* v_always_2991_, lean_object* v_inst_2992_, lean_object* v_cls_2993_, lean_object* v_collapsed_2994_, lean_object* v_tag_2995_, lean_object* v_opts_2996_, lean_object* v_clsEnabled_2997_, lean_object* v_oldTraces_2998_, lean_object* v_ref_2999_, lean_object* v_msg_3000_, lean_object* v_resStartStop_3001_){
_start:
{
uint8_t v_collapsed_boxed_3002_; uint8_t v_clsEnabled_boxed_3003_; lean_object* v_res_3004_; 
v_collapsed_boxed_3002_ = lean_unbox(v_collapsed_2994_);
v_clsEnabled_boxed_3003_ = lean_unbox(v_clsEnabled_2997_);
v_res_3004_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2987_, v_inst_2988_, v_inst_2989_, v_inst_2990_, v_always_2991_, v_inst_2992_, v_cls_2993_, v_collapsed_boxed_3002_, v_tag_2995_, v_opts_2996_, v_clsEnabled_boxed_3003_, v_oldTraces_2998_, v_ref_2999_, v_msg_3000_, v_resStartStop_3001_);
lean_dec_ref(v_opts_2996_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object* v_00_u03b1_3005_, lean_object* v_m_3006_, lean_object* v_inst_3007_, lean_object* v_inst_3008_, lean_object* v_00_u03b5_3009_, lean_object* v_inst_3010_, lean_object* v_inst_3011_, lean_object* v_always_3012_, lean_object* v_inst_3013_, lean_object* v_cls_3014_, uint8_t v_collapsed_3015_, lean_object* v_tag_3016_, lean_object* v_opts_3017_, uint8_t v_clsEnabled_3018_, lean_object* v_oldTraces_3019_, lean_object* v_ref_3020_, lean_object* v_msg_3021_, lean_object* v_resStartStop_3022_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_3007_, v_inst_3008_, v_inst_3010_, v_inst_3011_, v_always_3012_, v_inst_3013_, v_cls_3014_, v_collapsed_3015_, v_tag_3016_, v_opts_3017_, v_clsEnabled_3018_, v_oldTraces_3019_, v_ref_3020_, v_msg_3021_, v_resStartStop_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_3024_ = _args[0];
lean_object* v_m_3025_ = _args[1];
lean_object* v_inst_3026_ = _args[2];
lean_object* v_inst_3027_ = _args[3];
lean_object* v_00_u03b5_3028_ = _args[4];
lean_object* v_inst_3029_ = _args[5];
lean_object* v_inst_3030_ = _args[6];
lean_object* v_always_3031_ = _args[7];
lean_object* v_inst_3032_ = _args[8];
lean_object* v_cls_3033_ = _args[9];
lean_object* v_collapsed_3034_ = _args[10];
lean_object* v_tag_3035_ = _args[11];
lean_object* v_opts_3036_ = _args[12];
lean_object* v_clsEnabled_3037_ = _args[13];
lean_object* v_oldTraces_3038_ = _args[14];
lean_object* v_ref_3039_ = _args[15];
lean_object* v_msg_3040_ = _args[16];
lean_object* v_resStartStop_3041_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3042_; uint8_t v_clsEnabled_boxed_3043_; lean_object* v_res_3044_; 
v_collapsed_boxed_3042_ = lean_unbox(v_collapsed_3034_);
v_clsEnabled_boxed_3043_ = lean_unbox(v_clsEnabled_3037_);
v_res_3044_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(v_00_u03b1_3024_, v_m_3025_, v_inst_3026_, v_inst_3027_, v_00_u03b5_3028_, v_inst_3029_, v_inst_3030_, v_always_3031_, v_inst_3032_, v_cls_3033_, v_collapsed_boxed_3042_, v_tag_3035_, v_opts_3036_, v_clsEnabled_boxed_3043_, v_oldTraces_3038_, v_ref_3039_, v_msg_3040_, v_resStartStop_3041_);
lean_dec_ref(v_opts_3036_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object* v_inst_3045_, lean_object* v_____do__lift_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_apply_1(v_inst_3045_, v_____do__lift_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object* v_inst_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_always_3052_, lean_object* v_inst_3053_, lean_object* v_cls_3054_, uint8_t v_collapsed_3055_, lean_object* v_tag_3056_, lean_object* v_opts_3057_, uint8_t v_clsEnabled_3058_, lean_object* v_oldTraces_3059_, lean_object* v_ref_3060_, lean_object* v_msg_3061_, lean_object* v_resStartStop_3062_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_3048_, v_inst_3049_, v_inst_3050_, v_inst_3051_, v_always_3052_, v_inst_3053_, v_cls_3054_, v_collapsed_3055_, v_tag_3056_, v_opts_3057_, v_clsEnabled_3058_, v_oldTraces_3059_, v_ref_3060_, v_msg_3061_, v_resStartStop_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object* v_inst_3064_, lean_object* v_inst_3065_, lean_object* v_inst_3066_, lean_object* v_inst_3067_, lean_object* v_always_3068_, lean_object* v_inst_3069_, lean_object* v_cls_3070_, lean_object* v_collapsed_3071_, lean_object* v_tag_3072_, lean_object* v_opts_3073_, lean_object* v_clsEnabled_3074_, lean_object* v_oldTraces_3075_, lean_object* v_ref_3076_, lean_object* v_msg_3077_, lean_object* v_resStartStop_3078_){
_start:
{
uint8_t v_collapsed_boxed_3079_; uint8_t v_clsEnabled_boxed_3080_; lean_object* v_res_3081_; 
v_collapsed_boxed_3079_ = lean_unbox(v_collapsed_3071_);
v_clsEnabled_boxed_3080_ = lean_unbox(v_clsEnabled_3074_);
v_res_3081_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_3064_, v_inst_3065_, v_inst_3066_, v_inst_3067_, v_always_3068_, v_inst_3069_, v_cls_3070_, v_collapsed_boxed_3079_, v_tag_3072_, v_opts_3073_, v_clsEnabled_boxed_3080_, v_oldTraces_3075_, v_ref_3076_, v_msg_3077_, v_resStartStop_3078_);
lean_dec_ref(v_opts_3073_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object* v_always_3082_, lean_object* v_inst_3083_, lean_object* v_inst_3084_, lean_object* v_inst_3085_, lean_object* v_inst_3086_, lean_object* v_inst_3087_, lean_object* v_cls_3088_, uint8_t v_collapsed_3089_, lean_object* v_tag_3090_, lean_object* v_opts_3091_, uint8_t v_clsEnabled_3092_, lean_object* v_oldTraces_3093_, lean_object* v_ref_3094_, lean_object* v_toPure_3095_, lean_object* v_toBind_3096_, lean_object* v_k_3097_, lean_object* v_inst_3098_, lean_object* v_msg_3099_){
_start:
{
lean_object* v_tryCatch_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___f_3103_; lean_object* v___f_3104_; lean_object* v___f_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_tryCatch_3100_ = lean_ctor_get(v_always_3082_, 1);
lean_inc(v_tryCatch_3100_);
v___x_3101_ = lean_box(v_collapsed_3089_);
v___x_3102_ = lean_box(v_clsEnabled_3092_);
lean_inc_ref(v_opts_3091_);
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__1___boxed), 15, 14);
lean_closure_set(v___f_3103_, 0, v_inst_3083_);
lean_closure_set(v___f_3103_, 1, v_inst_3084_);
lean_closure_set(v___f_3103_, 2, v_inst_3085_);
lean_closure_set(v___f_3103_, 3, v_inst_3086_);
lean_closure_set(v___f_3103_, 4, v_always_3082_);
lean_closure_set(v___f_3103_, 5, v_inst_3087_);
lean_closure_set(v___f_3103_, 6, v_cls_3088_);
lean_closure_set(v___f_3103_, 7, v___x_3101_);
lean_closure_set(v___f_3103_, 8, v_tag_3090_);
lean_closure_set(v___f_3103_, 9, v_opts_3091_);
lean_closure_set(v___f_3103_, 10, v___x_3102_);
lean_closure_set(v___f_3103_, 11, v_oldTraces_3093_);
lean_closure_set(v___f_3103_, 12, v_ref_3094_);
lean_closure_set(v___f_3103_, 13, v_msg_3099_);
lean_inc_n(v_toPure_3095_, 2);
v___f_3104_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3104_, 0, v_toPure_3095_);
v___f_3105_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3105_, 0, v_toPure_3095_);
lean_inc(v_toBind_3096_);
v___x_3106_ = lean_apply_4(v_toBind_3096_, lean_box(0), lean_box(0), v_k_3097_, v___f_3105_);
v___x_3107_ = lean_apply_3(v_tryCatch_3100_, lean_box(0), v___x_3106_, v___f_3104_);
v___x_3108_ = l_Lean_KVMap_instValueBool;
v___x_3109_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3110_ = l_Lean_Option_get___redArg(v___x_3108_, v_opts_3091_, v___x_3109_);
lean_dec_ref(v_opts_3091_);
v___x_3111_ = lean_unbox(v___x_3110_);
lean_dec(v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___f_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3112_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_3113_ = lean_apply_2(v_inst_3098_, lean_box(0), v___x_3112_);
lean_inc(v___x_3113_);
lean_inc_n(v_toBind_3096_, 2);
v___f_3114_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3114_, 0, v_toPure_3095_);
lean_closure_set(v___f_3114_, 1, v_toBind_3096_);
lean_closure_set(v___f_3114_, 2, v___x_3113_);
lean_closure_set(v___f_3114_, 3, v___x_3107_);
v___x_3115_ = lean_apply_4(v_toBind_3096_, lean_box(0), lean_box(0), v___x_3113_, v___f_3114_);
v___x_3116_ = lean_apply_4(v_toBind_3096_, lean_box(0), lean_box(0), v___x_3115_, v___f_3103_);
return v___x_3116_;
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___f_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3117_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_3118_ = lean_apply_2(v_inst_3098_, lean_box(0), v___x_3117_);
lean_inc(v___x_3118_);
lean_inc_n(v_toBind_3096_, 2);
v___f_3119_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_3119_, 0, v_toPure_3095_);
lean_closure_set(v___f_3119_, 1, v_toBind_3096_);
lean_closure_set(v___f_3119_, 2, v___x_3118_);
lean_closure_set(v___f_3119_, 3, v___x_3107_);
v___x_3120_ = lean_apply_4(v_toBind_3096_, lean_box(0), lean_box(0), v___x_3118_, v___f_3119_);
v___x_3121_ = lean_apply_4(v_toBind_3096_, lean_box(0), lean_box(0), v___x_3120_, v___f_3103_);
return v___x_3121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_3122_ = _args[0];
lean_object* v_inst_3123_ = _args[1];
lean_object* v_inst_3124_ = _args[2];
lean_object* v_inst_3125_ = _args[3];
lean_object* v_inst_3126_ = _args[4];
lean_object* v_inst_3127_ = _args[5];
lean_object* v_cls_3128_ = _args[6];
lean_object* v_collapsed_3129_ = _args[7];
lean_object* v_tag_3130_ = _args[8];
lean_object* v_opts_3131_ = _args[9];
lean_object* v_clsEnabled_3132_ = _args[10];
lean_object* v_oldTraces_3133_ = _args[11];
lean_object* v_ref_3134_ = _args[12];
lean_object* v_toPure_3135_ = _args[13];
lean_object* v_toBind_3136_ = _args[14];
lean_object* v_k_3137_ = _args[15];
lean_object* v_inst_3138_ = _args[16];
lean_object* v_msg_3139_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3140_; uint8_t v_clsEnabled_boxed_3141_; lean_object* v_res_3142_; 
v_collapsed_boxed_3140_ = lean_unbox(v_collapsed_3129_);
v_clsEnabled_boxed_3141_ = lean_unbox(v_clsEnabled_3132_);
v_res_3142_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_always_3122_, v_inst_3123_, v_inst_3124_, v_inst_3125_, v_inst_3126_, v_inst_3127_, v_cls_3128_, v_collapsed_boxed_3140_, v_tag_3130_, v_opts_3131_, v_clsEnabled_boxed_3141_, v_oldTraces_3133_, v_ref_3134_, v_toPure_3135_, v_toBind_3136_, v_k_3137_, v_inst_3138_, v_msg_3139_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object* v_always_3143_, lean_object* v_inst_3144_, lean_object* v_inst_3145_, lean_object* v_inst_3146_, lean_object* v_inst_3147_, lean_object* v_inst_3148_, lean_object* v_cls_3149_, uint8_t v_collapsed_3150_, lean_object* v_tag_3151_, lean_object* v_opts_3152_, uint8_t v_clsEnabled_3153_, lean_object* v_oldTraces_3154_, lean_object* v_toPure_3155_, lean_object* v_toBind_3156_, lean_object* v_k_3157_, lean_object* v_inst_3158_, lean_object* v_msg_3159_, lean_object* v___f_3160_, lean_object* v_withRef_3161_, lean_object* v_getRef_3162_, lean_object* v_ref_3163_){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___f_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___f_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3164_ = lean_box(v_collapsed_3150_);
v___x_3165_ = lean_box(v_clsEnabled_3153_);
lean_inc_n(v_toBind_3156_, 3);
lean_inc(v_ref_3163_);
v___f_3166_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__10___boxed), 18, 17);
lean_closure_set(v___f_3166_, 0, v_always_3143_);
lean_closure_set(v___f_3166_, 1, v_inst_3144_);
lean_closure_set(v___f_3166_, 2, v_inst_3145_);
lean_closure_set(v___f_3166_, 3, v_inst_3146_);
lean_closure_set(v___f_3166_, 4, v_inst_3147_);
lean_closure_set(v___f_3166_, 5, v_inst_3148_);
lean_closure_set(v___f_3166_, 6, v_cls_3149_);
lean_closure_set(v___f_3166_, 7, v___x_3164_);
lean_closure_set(v___f_3166_, 8, v_tag_3151_);
lean_closure_set(v___f_3166_, 9, v_opts_3152_);
lean_closure_set(v___f_3166_, 10, v___x_3165_);
lean_closure_set(v___f_3166_, 11, v_oldTraces_3154_);
lean_closure_set(v___f_3166_, 12, v_ref_3163_);
lean_closure_set(v___f_3166_, 13, v_toPure_3155_);
lean_closure_set(v___f_3166_, 14, v_toBind_3156_);
lean_closure_set(v___f_3166_, 15, v_k_3157_);
lean_closure_set(v___f_3166_, 16, v_inst_3158_);
v___x_3167_ = lean_box(0);
v___x_3168_ = lean_apply_1(v_msg_3159_, v___x_3167_);
v___x_3169_ = lean_apply_4(v_toBind_3156_, lean_box(0), lean_box(0), v___x_3168_, v___f_3160_);
v___f_3170_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3170_, 0, v_ref_3163_);
lean_closure_set(v___f_3170_, 1, v_withRef_3161_);
lean_closure_set(v___f_3170_, 2, v___x_3169_);
v___x_3171_ = lean_apply_4(v_toBind_3156_, lean_box(0), lean_box(0), v_getRef_3162_, v___f_3170_);
v___x_3172_ = lean_apply_4(v_toBind_3156_, lean_box(0), lean_box(0), v___x_3171_, v___f_3166_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_3173_ = _args[0];
lean_object* v_inst_3174_ = _args[1];
lean_object* v_inst_3175_ = _args[2];
lean_object* v_inst_3176_ = _args[3];
lean_object* v_inst_3177_ = _args[4];
lean_object* v_inst_3178_ = _args[5];
lean_object* v_cls_3179_ = _args[6];
lean_object* v_collapsed_3180_ = _args[7];
lean_object* v_tag_3181_ = _args[8];
lean_object* v_opts_3182_ = _args[9];
lean_object* v_clsEnabled_3183_ = _args[10];
lean_object* v_oldTraces_3184_ = _args[11];
lean_object* v_toPure_3185_ = _args[12];
lean_object* v_toBind_3186_ = _args[13];
lean_object* v_k_3187_ = _args[14];
lean_object* v_inst_3188_ = _args[15];
lean_object* v_msg_3189_ = _args[16];
lean_object* v___f_3190_ = _args[17];
lean_object* v_withRef_3191_ = _args[18];
lean_object* v_getRef_3192_ = _args[19];
lean_object* v_ref_3193_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_3194_; uint8_t v_clsEnabled_boxed_3195_; lean_object* v_res_3196_; 
v_collapsed_boxed_3194_ = lean_unbox(v_collapsed_3180_);
v_clsEnabled_boxed_3195_ = lean_unbox(v_clsEnabled_3183_);
v_res_3196_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_always_3173_, v_inst_3174_, v_inst_3175_, v_inst_3176_, v_inst_3177_, v_inst_3178_, v_cls_3179_, v_collapsed_boxed_3194_, v_tag_3181_, v_opts_3182_, v_clsEnabled_boxed_3195_, v_oldTraces_3184_, v_toPure_3185_, v_toBind_3186_, v_k_3187_, v_inst_3188_, v_msg_3189_, v___f_3190_, v_withRef_3191_, v_getRef_3192_, v_ref_3193_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object* v_inst_3197_, lean_object* v_always_3198_, lean_object* v_inst_3199_, lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_inst_3202_, lean_object* v_cls_3203_, uint8_t v_collapsed_3204_, lean_object* v_tag_3205_, lean_object* v_opts_3206_, uint8_t v_clsEnabled_3207_, lean_object* v_toPure_3208_, lean_object* v_toBind_3209_, lean_object* v_k_3210_, lean_object* v_inst_3211_, lean_object* v_msg_3212_, lean_object* v___f_3213_, lean_object* v_oldTraces_3214_){
_start:
{
lean_object* v_getRef_3215_; lean_object* v_withRef_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; 
v_getRef_3215_ = lean_ctor_get(v_inst_3197_, 0);
lean_inc_n(v_getRef_3215_, 2);
v_withRef_3216_ = lean_ctor_get(v_inst_3197_, 1);
lean_inc(v_withRef_3216_);
v___x_3217_ = lean_box(v_collapsed_3204_);
v___x_3218_ = lean_box(v_clsEnabled_3207_);
lean_inc(v_toBind_3209_);
v___f_3219_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__3___boxed), 21, 20);
lean_closure_set(v___f_3219_, 0, v_always_3198_);
lean_closure_set(v___f_3219_, 1, v_inst_3199_);
lean_closure_set(v___f_3219_, 2, v_inst_3200_);
lean_closure_set(v___f_3219_, 3, v_inst_3197_);
lean_closure_set(v___f_3219_, 4, v_inst_3201_);
lean_closure_set(v___f_3219_, 5, v_inst_3202_);
lean_closure_set(v___f_3219_, 6, v_cls_3203_);
lean_closure_set(v___f_3219_, 7, v___x_3217_);
lean_closure_set(v___f_3219_, 8, v_tag_3205_);
lean_closure_set(v___f_3219_, 9, v_opts_3206_);
lean_closure_set(v___f_3219_, 10, v___x_3218_);
lean_closure_set(v___f_3219_, 11, v_oldTraces_3214_);
lean_closure_set(v___f_3219_, 12, v_toPure_3208_);
lean_closure_set(v___f_3219_, 13, v_toBind_3209_);
lean_closure_set(v___f_3219_, 14, v_k_3210_);
lean_closure_set(v___f_3219_, 15, v_inst_3211_);
lean_closure_set(v___f_3219_, 16, v_msg_3212_);
lean_closure_set(v___f_3219_, 17, v___f_3213_);
lean_closure_set(v___f_3219_, 18, v_withRef_3216_);
lean_closure_set(v___f_3219_, 19, v_getRef_3215_);
v___x_3220_ = lean_apply_4(v_toBind_3209_, lean_box(0), lean_box(0), v_getRef_3215_, v___f_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_3221_ = _args[0];
lean_object* v_always_3222_ = _args[1];
lean_object* v_inst_3223_ = _args[2];
lean_object* v_inst_3224_ = _args[3];
lean_object* v_inst_3225_ = _args[4];
lean_object* v_inst_3226_ = _args[5];
lean_object* v_cls_3227_ = _args[6];
lean_object* v_collapsed_3228_ = _args[7];
lean_object* v_tag_3229_ = _args[8];
lean_object* v_opts_3230_ = _args[9];
lean_object* v_clsEnabled_3231_ = _args[10];
lean_object* v_toPure_3232_ = _args[11];
lean_object* v_toBind_3233_ = _args[12];
lean_object* v_k_3234_ = _args[13];
lean_object* v_inst_3235_ = _args[14];
lean_object* v_msg_3236_ = _args[15];
lean_object* v___f_3237_ = _args[16];
lean_object* v_oldTraces_3238_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3239_; uint8_t v_clsEnabled_boxed_3240_; lean_object* v_res_3241_; 
v_collapsed_boxed_3239_ = lean_unbox(v_collapsed_3228_);
v_clsEnabled_boxed_3240_ = lean_unbox(v_clsEnabled_3231_);
v_res_3241_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3221_, v_always_3222_, v_inst_3223_, v_inst_3224_, v_inst_3225_, v_inst_3226_, v_cls_3227_, v_collapsed_boxed_3239_, v_tag_3229_, v_opts_3230_, v_clsEnabled_boxed_3240_, v_toPure_3232_, v_toBind_3233_, v_k_3234_, v_inst_3235_, v_msg_3236_, v___f_3237_, v_oldTraces_3238_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object* v_inst_3242_, lean_object* v_always_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_cls_3248_, uint8_t v_collapsed_3249_, lean_object* v_tag_3250_, lean_object* v_opts_3251_, lean_object* v_toPure_3252_, lean_object* v_toBind_3253_, lean_object* v_k_3254_, lean_object* v_inst_3255_, lean_object* v_msg_3256_, lean_object* v___f_3257_, uint8_t v_clsEnabled_3258_){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___f_3261_; 
v___x_3259_ = lean_box(v_collapsed_3249_);
v___x_3260_ = lean_box(v_clsEnabled_3258_);
lean_inc(v_k_3254_);
lean_inc(v_toBind_3253_);
lean_inc_ref(v_opts_3251_);
lean_inc_ref(v_inst_3245_);
lean_inc_ref(v_inst_3244_);
v___f_3261_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__2___boxed), 18, 17);
lean_closure_set(v___f_3261_, 0, v_inst_3242_);
lean_closure_set(v___f_3261_, 1, v_always_3243_);
lean_closure_set(v___f_3261_, 2, v_inst_3244_);
lean_closure_set(v___f_3261_, 3, v_inst_3245_);
lean_closure_set(v___f_3261_, 4, v_inst_3246_);
lean_closure_set(v___f_3261_, 5, v_inst_3247_);
lean_closure_set(v___f_3261_, 6, v_cls_3248_);
lean_closure_set(v___f_3261_, 7, v___x_3259_);
lean_closure_set(v___f_3261_, 8, v_tag_3250_);
lean_closure_set(v___f_3261_, 9, v_opts_3251_);
lean_closure_set(v___f_3261_, 10, v___x_3260_);
lean_closure_set(v___f_3261_, 11, v_toPure_3252_);
lean_closure_set(v___f_3261_, 12, v_toBind_3253_);
lean_closure_set(v___f_3261_, 13, v_k_3254_);
lean_closure_set(v___f_3261_, 14, v_inst_3255_);
lean_closure_set(v___f_3261_, 15, v_msg_3256_);
lean_closure_set(v___f_3261_, 16, v___f_3257_);
if (v_clsEnabled_3258_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; 
v___x_3265_ = l_Lean_KVMap_instValueBool;
v___x_3266_ = l_Lean_trace_profiler;
v___x_3267_ = l_Lean_Option_get___redArg(v___x_3265_, v_opts_3251_, v___x_3266_);
lean_dec_ref(v_opts_3251_);
v___x_3268_ = lean_unbox(v___x_3267_);
lean_dec(v___x_3267_);
if (v___x_3268_ == 0)
{
lean_dec_ref(v___f_3261_);
lean_dec(v_toBind_3253_);
lean_dec_ref(v_inst_3245_);
lean_dec_ref(v_inst_3244_);
return v_k_3254_;
}
else
{
lean_dec(v_k_3254_);
goto v___jp_3262_;
}
}
else
{
lean_dec(v_k_3254_);
lean_dec_ref(v_opts_3251_);
goto v___jp_3262_;
}
v___jp_3262_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3244_, v_inst_3245_);
v___x_3264_ = lean_apply_4(v_toBind_3253_, lean_box(0), lean_box(0), v___x_3263_, v___f_3261_);
return v___x_3264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_3269_ = _args[0];
lean_object* v_always_3270_ = _args[1];
lean_object* v_inst_3271_ = _args[2];
lean_object* v_inst_3272_ = _args[3];
lean_object* v_inst_3273_ = _args[4];
lean_object* v_inst_3274_ = _args[5];
lean_object* v_cls_3275_ = _args[6];
lean_object* v_collapsed_3276_ = _args[7];
lean_object* v_tag_3277_ = _args[8];
lean_object* v_opts_3278_ = _args[9];
lean_object* v_toPure_3279_ = _args[10];
lean_object* v_toBind_3280_ = _args[11];
lean_object* v_k_3281_ = _args[12];
lean_object* v_inst_3282_ = _args[13];
lean_object* v_msg_3283_ = _args[14];
lean_object* v___f_3284_ = _args[15];
lean_object* v_clsEnabled_3285_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3286_; uint8_t v_clsEnabled_boxed_3287_; lean_object* v_res_3288_; 
v_collapsed_boxed_3286_ = lean_unbox(v_collapsed_3276_);
v_clsEnabled_boxed_3287_ = lean_unbox(v_clsEnabled_3285_);
v_res_3288_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3269_, v_always_3270_, v_inst_3271_, v_inst_3272_, v_inst_3273_, v_inst_3274_, v_cls_3275_, v_collapsed_boxed_3286_, v_tag_3277_, v_opts_3278_, v_toPure_3279_, v_toBind_3280_, v_k_3281_, v_inst_3282_, v_msg_3283_, v___f_3284_, v_clsEnabled_boxed_3287_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object* v_k_3289_, lean_object* v_inst_3290_, lean_object* v_toApplicative_3291_, lean_object* v_inst_3292_, lean_object* v_always_3293_, lean_object* v_inst_3294_, lean_object* v_inst_3295_, lean_object* v_inst_3296_, lean_object* v_cls_3297_, uint8_t v_collapsed_3298_, lean_object* v_tag_3299_, lean_object* v_toBind_3300_, lean_object* v_inst_3301_, lean_object* v_msg_3302_, lean_object* v___f_3303_, lean_object* v_inst_3304_, lean_object* v_opts_3305_){
_start:
{
uint8_t v_hasTrace_3306_; 
v_hasTrace_3306_ = lean_ctor_get_uint8(v_opts_3305_, sizeof(void*)*1);
if (v_hasTrace_3306_ == 0)
{
lean_dec_ref(v_opts_3305_);
lean_dec(v_inst_3304_);
lean_dec(v___f_3303_);
lean_dec(v_msg_3302_);
lean_dec(v_inst_3301_);
lean_dec(v_toBind_3300_);
lean_dec_ref(v_tag_3299_);
lean_dec(v_cls_3297_);
lean_dec_ref(v_inst_3296_);
lean_dec(v_inst_3295_);
lean_dec_ref(v_inst_3294_);
lean_dec_ref(v_always_3293_);
lean_dec_ref(v_inst_3292_);
lean_dec_ref(v_toApplicative_3291_);
lean_dec_ref(v_inst_3290_);
return v_k_3289_;
}
else
{
lean_object* v_getInheritedTraceOptions_3307_; lean_object* v_toPure_3308_; lean_object* v___x_3309_; lean_object* v___f_3310_; lean_object* v___f_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v_getInheritedTraceOptions_3307_ = lean_ctor_get(v_inst_3290_, 2);
lean_inc(v_getInheritedTraceOptions_3307_);
v_toPure_3308_ = lean_ctor_get(v_toApplicative_3291_, 1);
lean_inc_n(v_toPure_3308_, 2);
lean_dec_ref(v_toApplicative_3291_);
v___x_3309_ = lean_box(v_collapsed_3298_);
lean_inc_n(v_toBind_3300_, 3);
lean_inc(v_cls_3297_);
v___f_3310_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_3310_, 0, v_inst_3292_);
lean_closure_set(v___f_3310_, 1, v_always_3293_);
lean_closure_set(v___f_3310_, 2, v_inst_3294_);
lean_closure_set(v___f_3310_, 3, v_inst_3290_);
lean_closure_set(v___f_3310_, 4, v_inst_3295_);
lean_closure_set(v___f_3310_, 5, v_inst_3296_);
lean_closure_set(v___f_3310_, 6, v_cls_3297_);
lean_closure_set(v___f_3310_, 7, v___x_3309_);
lean_closure_set(v___f_3310_, 8, v_tag_3299_);
lean_closure_set(v___f_3310_, 9, v_opts_3305_);
lean_closure_set(v___f_3310_, 10, v_toPure_3308_);
lean_closure_set(v___f_3310_, 11, v_toBind_3300_);
lean_closure_set(v___f_3310_, 12, v_k_3289_);
lean_closure_set(v___f_3310_, 13, v_inst_3301_);
lean_closure_set(v___f_3310_, 14, v_msg_3302_);
lean_closure_set(v___f_3310_, 15, v___f_3303_);
v___f_3311_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3311_, 0, v_toPure_3308_);
lean_closure_set(v___f_3311_, 1, v_cls_3297_);
lean_closure_set(v___f_3311_, 2, v_toBind_3300_);
lean_closure_set(v___f_3311_, 3, v_inst_3304_);
v___x_3312_ = lean_apply_4(v_toBind_3300_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3307_, v___f_3311_);
v___x_3313_ = lean_apply_4(v_toBind_3300_, lean_box(0), lean_box(0), v___x_3312_, v___f_3310_);
return v___x_3313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_k_3314_ = _args[0];
lean_object* v_inst_3315_ = _args[1];
lean_object* v_toApplicative_3316_ = _args[2];
lean_object* v_inst_3317_ = _args[3];
lean_object* v_always_3318_ = _args[4];
lean_object* v_inst_3319_ = _args[5];
lean_object* v_inst_3320_ = _args[6];
lean_object* v_inst_3321_ = _args[7];
lean_object* v_cls_3322_ = _args[8];
lean_object* v_collapsed_3323_ = _args[9];
lean_object* v_tag_3324_ = _args[10];
lean_object* v_toBind_3325_ = _args[11];
lean_object* v_inst_3326_ = _args[12];
lean_object* v_msg_3327_ = _args[13];
lean_object* v___f_3328_ = _args[14];
lean_object* v_inst_3329_ = _args[15];
lean_object* v_opts_3330_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3331_; lean_object* v_res_3332_; 
v_collapsed_boxed_3331_ = lean_unbox(v_collapsed_3323_);
v_res_3332_ = l_Lean_withTraceNodeBefore___redArg___lam__7(v_k_3314_, v_inst_3315_, v_toApplicative_3316_, v_inst_3317_, v_always_3318_, v_inst_3319_, v_inst_3320_, v_inst_3321_, v_cls_3322_, v_collapsed_boxed_3331_, v_tag_3324_, v_toBind_3325_, v_inst_3326_, v_msg_3327_, v___f_3328_, v_inst_3329_, v_opts_3330_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object* v_inst_3333_, lean_object* v_inst_3334_, lean_object* v_inst_3335_, lean_object* v_inst_3336_, lean_object* v_inst_3337_, lean_object* v_always_3338_, lean_object* v_inst_3339_, lean_object* v_inst_3340_, lean_object* v_cls_3341_, lean_object* v_msg_3342_, lean_object* v_k_3343_, uint8_t v_collapsed_3344_, lean_object* v_tag_3345_){
_start:
{
lean_object* v_toApplicative_3346_; lean_object* v_toBind_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; lean_object* v___f_3350_; lean_object* v___x_3351_; 
v_toApplicative_3346_ = lean_ctor_get(v_inst_3333_, 0);
lean_inc_ref(v_toApplicative_3346_);
v_toBind_3347_ = lean_ctor_get(v_inst_3333_, 1);
lean_inc_n(v_toBind_3347_, 2);
lean_inc(v_inst_3336_);
v___f_3348_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3348_, 0, v_inst_3336_);
v___x_3349_ = lean_box(v_collapsed_3344_);
lean_inc(v_inst_3337_);
v___f_3350_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3350_, 0, v_k_3343_);
lean_closure_set(v___f_3350_, 1, v_inst_3334_);
lean_closure_set(v___f_3350_, 2, v_toApplicative_3346_);
lean_closure_set(v___f_3350_, 3, v_inst_3335_);
lean_closure_set(v___f_3350_, 4, v_always_3338_);
lean_closure_set(v___f_3350_, 5, v_inst_3333_);
lean_closure_set(v___f_3350_, 6, v_inst_3336_);
lean_closure_set(v___f_3350_, 7, v_inst_3340_);
lean_closure_set(v___f_3350_, 8, v_cls_3341_);
lean_closure_set(v___f_3350_, 9, v___x_3349_);
lean_closure_set(v___f_3350_, 10, v_tag_3345_);
lean_closure_set(v___f_3350_, 11, v_toBind_3347_);
lean_closure_set(v___f_3350_, 12, v_inst_3339_);
lean_closure_set(v___f_3350_, 13, v_msg_3342_);
lean_closure_set(v___f_3350_, 14, v___f_3348_);
lean_closure_set(v___f_3350_, 15, v_inst_3337_);
v___x_3351_ = lean_apply_4(v_toBind_3347_, lean_box(0), lean_box(0), v_inst_3337_, v___f_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object* v_inst_3352_, lean_object* v_inst_3353_, lean_object* v_inst_3354_, lean_object* v_inst_3355_, lean_object* v_inst_3356_, lean_object* v_always_3357_, lean_object* v_inst_3358_, lean_object* v_inst_3359_, lean_object* v_cls_3360_, lean_object* v_msg_3361_, lean_object* v_k_3362_, lean_object* v_collapsed_3363_, lean_object* v_tag_3364_){
_start:
{
uint8_t v_collapsed_boxed_3365_; lean_object* v_res_3366_; 
v_collapsed_boxed_3365_ = lean_unbox(v_collapsed_3363_);
v_res_3366_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3352_, v_inst_3353_, v_inst_3354_, v_inst_3355_, v_inst_3356_, v_always_3357_, v_inst_3358_, v_inst_3359_, v_cls_3360_, v_msg_3361_, v_k_3362_, v_collapsed_boxed_3365_, v_tag_3364_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object* v_00_u03b1_3367_, lean_object* v_m_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_00_u03b5_3371_, lean_object* v_inst_3372_, lean_object* v_inst_3373_, lean_object* v_inst_3374_, lean_object* v_always_3375_, lean_object* v_inst_3376_, lean_object* v_inst_3377_, lean_object* v_cls_3378_, lean_object* v_msg_3379_, lean_object* v_k_3380_, uint8_t v_collapsed_3381_, lean_object* v_tag_3382_){
_start:
{
lean_object* v_toApplicative_3383_; lean_object* v_toBind_3384_; lean_object* v___f_3385_; lean_object* v___x_3386_; lean_object* v___f_3387_; lean_object* v___x_3388_; 
v_toApplicative_3383_ = lean_ctor_get(v_inst_3369_, 0);
lean_inc_ref(v_toApplicative_3383_);
v_toBind_3384_ = lean_ctor_get(v_inst_3369_, 1);
lean_inc_n(v_toBind_3384_, 2);
lean_inc(v_inst_3373_);
v___f_3385_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3385_, 0, v_inst_3373_);
v___x_3386_ = lean_box(v_collapsed_3381_);
lean_inc(v_inst_3374_);
v___f_3387_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3387_, 0, v_k_3380_);
lean_closure_set(v___f_3387_, 1, v_inst_3370_);
lean_closure_set(v___f_3387_, 2, v_toApplicative_3383_);
lean_closure_set(v___f_3387_, 3, v_inst_3372_);
lean_closure_set(v___f_3387_, 4, v_always_3375_);
lean_closure_set(v___f_3387_, 5, v_inst_3369_);
lean_closure_set(v___f_3387_, 6, v_inst_3373_);
lean_closure_set(v___f_3387_, 7, v_inst_3377_);
lean_closure_set(v___f_3387_, 8, v_cls_3378_);
lean_closure_set(v___f_3387_, 9, v___x_3386_);
lean_closure_set(v___f_3387_, 10, v_tag_3382_);
lean_closure_set(v___f_3387_, 11, v_toBind_3384_);
lean_closure_set(v___f_3387_, 12, v_inst_3376_);
lean_closure_set(v___f_3387_, 13, v_msg_3379_);
lean_closure_set(v___f_3387_, 14, v___f_3385_);
lean_closure_set(v___f_3387_, 15, v_inst_3374_);
v___x_3388_ = lean_apply_4(v_toBind_3384_, lean_box(0), lean_box(0), v_inst_3374_, v___f_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object* v_00_u03b1_3389_, lean_object* v_m_3390_, lean_object* v_inst_3391_, lean_object* v_inst_3392_, lean_object* v_00_u03b5_3393_, lean_object* v_inst_3394_, lean_object* v_inst_3395_, lean_object* v_inst_3396_, lean_object* v_always_3397_, lean_object* v_inst_3398_, lean_object* v_inst_3399_, lean_object* v_cls_3400_, lean_object* v_msg_3401_, lean_object* v_k_3402_, lean_object* v_collapsed_3403_, lean_object* v_tag_3404_){
_start:
{
uint8_t v_collapsed_boxed_3405_; lean_object* v_res_3406_; 
v_collapsed_boxed_3405_ = lean_unbox(v_collapsed_3403_);
v_res_3406_ = l_Lean_withTraceNodeBefore(v_00_u03b1_3389_, v_m_3390_, v_inst_3391_, v_inst_3392_, v_00_u03b5_3393_, v_inst_3394_, v_inst_3395_, v_inst_3396_, v_always_3397_, v_inst_3398_, v_inst_3399_, v_cls_3400_, v_msg_3401_, v_k_3402_, v_collapsed_boxed_3405_, v_tag_3404_);
return v_res_3406_;
}
}
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__0(lean_object* v_x_3407_, lean_object* v_x_3408_){
_start:
{
lean_object* v_fst_3409_; lean_object* v_fst_3410_; lean_object* v_fst_3411_; lean_object* v_fst_3412_; uint8_t v___x_3413_; 
v_fst_3409_ = lean_ctor_get(v_x_3407_, 0);
v_fst_3410_ = lean_ctor_get(v_x_3408_, 0);
v_fst_3411_ = lean_ctor_get(v_fst_3409_, 0);
v_fst_3412_ = lean_ctor_get(v_fst_3410_, 0);
v___x_3413_ = lean_nat_dec_lt(v_fst_3411_, v_fst_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0___boxed(lean_object* v_x_3414_, lean_object* v_x_3415_){
_start:
{
uint8_t v_res_3416_; lean_object* v_r_3417_; 
v_res_3416_ = l_Lean_addTraceAsMessages___redArg___lam__0(v_x_3414_, v_x_3415_);
lean_dec_ref(v_x_3415_);
lean_dec_ref(v_x_3414_);
v_r_3417_ = lean_box(v_res_3416_);
return v_r_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1(lean_object* v_toApplicative_3418_, lean_object* v_____s_3419_){
_start:
{
lean_object* v_toPure_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_toPure_3420_ = lean_ctor_get(v_toApplicative_3418_, 1);
lean_inc(v_toPure_3420_);
lean_dec_ref(v_toApplicative_3418_);
v___x_3421_ = lean_box(0);
v___x_3422_ = lean_apply_2(v_toPure_3420_, lean_box(0), v___x_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object* v_x1_3423_, lean_object* v_x2_3424_, lean_object* v_x3_3425_){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3426_, 0, v_x2_3424_);
lean_ctor_set(v___x_3426_, 1, v_x3_3425_);
v___x_3427_ = lean_array_push(v_x1_3423_, v___x_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object* v_toApplicative_3428_, lean_object* v___x_3429_, lean_object* v_r_3430_){
_start:
{
lean_object* v_toPure_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v_toPure_3431_ = lean_ctor_get(v_toApplicative_3428_, 1);
lean_inc(v_toPure_3431_);
lean_dec_ref(v_toApplicative_3428_);
v___x_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3429_);
v___x_3433_ = lean_apply_2(v_toPure_3431_, lean_box(0), v___x_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object* v_____do__lift_3434_, lean_object* v___x_3435_, lean_object* v_fst_3436_, lean_object* v_snd_3437_, lean_object* v_logMessage_3438_, lean_object* v_toBind_3439_, lean_object* v___f_3440_, lean_object* v_____do__lift_3441_){
_start:
{
uint8_t v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3442_ = 0;
v___x_3443_ = l_Lean_Elab_mkMessageCore(v_____do__lift_3434_, v_____do__lift_3441_, v___x_3435_, v___x_3442_, v_fst_3436_, v_snd_3437_);
v___x_3444_ = lean_apply_1(v_logMessage_3438_, v___x_3443_);
v___x_3445_ = lean_apply_4(v_toBind_3439_, lean_box(0), lean_box(0), v___x_3444_, v___f_3440_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object* v_____do__lift_3446_, lean_object* v___x_3447_, lean_object* v_fst_3448_, lean_object* v_snd_3449_, lean_object* v_logMessage_3450_, lean_object* v_toBind_3451_, lean_object* v___f_3452_, lean_object* v_____do__lift_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_addTraceAsMessages___redArg___lam__4(v_____do__lift_3446_, v___x_3447_, v_fst_3448_, v_snd_3449_, v_logMessage_3450_, v_toBind_3451_, v___f_3452_, v_____do__lift_3453_);
lean_dec(v_snd_3449_);
lean_dec(v_fst_3448_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object* v___x_3455_, lean_object* v_fst_3456_, lean_object* v_snd_3457_, lean_object* v_logMessage_3458_, lean_object* v_toBind_3459_, lean_object* v___f_3460_, lean_object* v_toMonadFileMap_3461_, lean_object* v_____do__lift_3462_){
_start:
{
lean_object* v___f_3463_; lean_object* v___x_3464_; 
lean_inc(v_toBind_3459_);
v___f_3463_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_3463_, 0, v_____do__lift_3462_);
lean_closure_set(v___f_3463_, 1, v___x_3455_);
lean_closure_set(v___f_3463_, 2, v_fst_3456_);
lean_closure_set(v___f_3463_, 3, v_snd_3457_);
lean_closure_set(v___f_3463_, 4, v_logMessage_3458_);
lean_closure_set(v___f_3463_, 5, v_toBind_3459_);
lean_closure_set(v___f_3463_, 6, v___f_3460_);
v___x_3464_ = lean_apply_4(v_toBind_3459_, lean_box(0), lean_box(0), v_toMonadFileMap_3461_, v___f_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object* v___x_3465_, uint8_t v___x_3466_, lean_object* v_inst_3467_, lean_object* v_toBind_3468_, lean_object* v___f_3469_, lean_object* v_a_3470_, lean_object* v_x_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_fst_3473_; lean_object* v_snd_3474_; lean_object* v_fst_3475_; lean_object* v_snd_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3496_; 
v_fst_3473_ = lean_ctor_get(v_a_3470_, 0);
lean_inc(v_fst_3473_);
v_snd_3474_ = lean_ctor_get(v_a_3470_, 1);
lean_inc(v_snd_3474_);
lean_dec_ref(v_a_3470_);
v_fst_3475_ = lean_ctor_get(v_fst_3473_, 0);
v_snd_3476_ = lean_ctor_get(v_fst_3473_, 1);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_fst_3473_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3478_ = v_fst_3473_;
v_isShared_3479_ = v_isSharedCheck_3496_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_snd_3476_);
lean_inc(v_fst_3475_);
lean_dec(v_fst_3473_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3496_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; double v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v_toMonadFileMap_3485_; lean_object* v_getFileName_3486_; lean_object* v_logMessage_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3480_ = lean_box(0);
v___x_3481_ = lean_box(0);
v___x_3482_ = lean_float_of_nat(v___x_3465_);
v___x_3483_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_3484_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3484_, 0, v___x_3480_);
lean_ctor_set(v___x_3484_, 1, v___x_3481_);
lean_ctor_set(v___x_3484_, 2, v___x_3483_);
lean_ctor_set_float(v___x_3484_, sizeof(void*)*3, v___x_3482_);
lean_ctor_set_float(v___x_3484_, sizeof(void*)*3 + 8, v___x_3482_);
lean_ctor_set_uint8(v___x_3484_, sizeof(void*)*3 + 16, v___x_3466_);
v_toMonadFileMap_3485_ = lean_ctor_get(v_inst_3467_, 0);
lean_inc(v_toMonadFileMap_3485_);
v_getFileName_3486_ = lean_ctor_get(v_inst_3467_, 2);
lean_inc(v_getFileName_3486_);
v_logMessage_3487_ = lean_ctor_get(v_inst_3467_, 4);
lean_inc(v_logMessage_3487_);
lean_dec_ref(v_inst_3467_);
v___x_3488_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_3489_ = l_Lean_MessageData_nil;
v___x_3490_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3484_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
lean_ctor_set(v___x_3490_, 2, v_snd_3474_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set_tag(v___x_3478_, 8);
lean_ctor_set(v___x_3478_, 1, v___x_3490_);
lean_ctor_set(v___x_3478_, 0, v___x_3488_);
v___x_3492_ = v___x_3478_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___f_3493_; lean_object* v___x_3494_; 
lean_inc(v_toBind_3468_);
v___f_3493_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__5), 8, 7);
lean_closure_set(v___f_3493_, 0, v___x_3492_);
lean_closure_set(v___f_3493_, 1, v_fst_3475_);
lean_closure_set(v___f_3493_, 2, v_snd_3476_);
lean_closure_set(v___f_3493_, 3, v_logMessage_3487_);
lean_closure_set(v___f_3493_, 4, v_toBind_3468_);
lean_closure_set(v___f_3493_, 5, v___f_3469_);
lean_closure_set(v___f_3493_, 6, v_toMonadFileMap_3485_);
v___x_3494_ = lean_apply_4(v_toBind_3468_, lean_box(0), lean_box(0), v_getFileName_3486_, v___f_3493_);
return v___x_3494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object* v___x_3497_, lean_object* v___x_3498_, lean_object* v_inst_3499_, lean_object* v_toBind_3500_, lean_object* v___f_3501_, lean_object* v_a_3502_, lean_object* v_x_3503_, lean_object* v___y_3504_){
_start:
{
uint8_t v___x_2242__boxed_3505_; lean_object* v_res_3506_; 
v___x_2242__boxed_3505_ = lean_unbox(v___x_3498_);
v_res_3506_ = l_Lean_addTraceAsMessages___redArg___lam__6(v___x_3497_, v___x_2242__boxed_3505_, v_inst_3499_, v_toBind_3500_, v___f_3501_, v_a_3502_, v_x_3503_, v___y_3504_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object* v___f_3507_, lean_object* v_toApplicative_3508_, uint8_t v___x_3509_, lean_object* v_inst_3510_, lean_object* v_toBind_3511_, lean_object* v_inst_3512_, lean_object* v___f_3513_, lean_object* v___f_3514_, lean_object* v_____s_3515_){
_start:
{
lean_object* v_size_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___y_3522_; lean_object* v___x_3531_; lean_object* v___y_3533_; lean_object* v___y_3534_; uint8_t v___x_3536_; 
v_size_3516_ = lean_ctor_get(v_____s_3515_, 0);
v___x_3517_ = lean_mk_empty_array_with_capacity(v_size_3516_);
v___x_3518_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v___x_3519_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_3518_, v___f_3507_, v___x_3517_, v_____s_3515_);
v___x_3520_ = lean_unsigned_to_nat(0u);
v___x_3531_ = lean_array_get_size(v___x_3519_);
v___x_3536_ = lean_nat_dec_eq(v___x_3531_, v___x_3520_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___y_3540_; uint8_t v___x_3542_; 
v___x_3537_ = lean_unsigned_to_nat(1u);
v___x_3538_ = lean_nat_sub(v___x_3531_, v___x_3537_);
v___x_3542_ = lean_nat_dec_le(v___x_3520_, v___x_3538_);
if (v___x_3542_ == 0)
{
lean_inc(v___x_3538_);
v___y_3540_ = v___x_3538_;
goto v___jp_3539_;
}
else
{
v___y_3540_ = v___x_3520_;
goto v___jp_3539_;
}
v___jp_3539_:
{
uint8_t v___x_3541_; 
v___x_3541_ = lean_nat_dec_le(v___y_3540_, v___x_3538_);
if (v___x_3541_ == 0)
{
lean_dec(v___x_3538_);
lean_inc(v___y_3540_);
v___y_3533_ = v___y_3540_;
v___y_3534_ = v___y_3540_;
goto v___jp_3532_;
}
else
{
v___y_3533_ = v___y_3540_;
v___y_3534_ = v___x_3538_;
goto v___jp_3532_;
}
}
}
else
{
lean_dec_ref(v___f_3514_);
v___y_3522_ = v___x_3519_;
goto v___jp_3521_;
}
v___jp_3521_:
{
lean_object* v___x_3523_; lean_object* v___f_3524_; lean_object* v___x_3525_; lean_object* v___f_3526_; size_t v_sz_3527_; size_t v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3523_ = lean_box(0);
v___f_3524_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3524_, 0, v_toApplicative_3508_);
lean_closure_set(v___f_3524_, 1, v___x_3523_);
v___x_3525_ = lean_box(v___x_3509_);
lean_inc(v_toBind_3511_);
v___f_3526_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__6___boxed), 8, 5);
lean_closure_set(v___f_3526_, 0, v___x_3520_);
lean_closure_set(v___f_3526_, 1, v___x_3525_);
lean_closure_set(v___f_3526_, 2, v_inst_3510_);
lean_closure_set(v___f_3526_, 3, v_toBind_3511_);
lean_closure_set(v___f_3526_, 4, v___f_3524_);
v_sz_3527_ = lean_array_size(v___y_3522_);
v___x_3528_ = ((size_t)0ULL);
v___x_3529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3512_, v___y_3522_, v___f_3526_, v_sz_3527_, v___x_3528_, v___x_3523_);
v___x_3530_ = lean_apply_4(v_toBind_3511_, lean_box(0), lean_box(0), v___x_3529_, v___f_3513_);
return v___x_3530_;
}
v___jp_3532_:
{
lean_object* v___x_3535_; 
v___x_3535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_3514_, v___x_3531_, v___x_3519_, v___y_3533_, v___y_3534_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_3534_);
v___y_3522_ = v___x_3535_;
goto v___jp_3521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7___boxed(lean_object* v___f_3543_, lean_object* v_toApplicative_3544_, lean_object* v___x_3545_, lean_object* v_inst_3546_, lean_object* v_toBind_3547_, lean_object* v_inst_3548_, lean_object* v___f_3549_, lean_object* v___f_3550_, lean_object* v_____s_3551_){
_start:
{
uint8_t v___x_2322__boxed_3552_; lean_object* v_res_3553_; 
v___x_2322__boxed_3552_ = lean_unbox(v___x_3545_);
v_res_3553_ = l_Lean_addTraceAsMessages___redArg___lam__7(v___f_3543_, v_toApplicative_3544_, v___x_2322__boxed_3552_, v_inst_3546_, v_toBind_3547_, v_inst_3548_, v___f_3549_, v___f_3550_, v_____s_3551_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object* v_traceElem_3554_, lean_object* v_toApplicative_3555_, lean_object* v___f_3556_, lean_object* v___f_3557_, lean_object* v_____s_3558_, uint8_t v___x_3559_, lean_object* v_____do__lift_3560_){
_start:
{
lean_object* v___y_3562_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v_i_3570_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v_i_3591_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v_ref_3608_; lean_object* v_msg_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3661_; 
v_ref_3608_ = lean_ctor_get(v_traceElem_3554_, 0);
v_msg_3609_ = lean_ctor_get(v_traceElem_3554_, 1);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_traceElem_3554_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3611_ = v_traceElem_3554_;
v_isShared_3612_ = v_isSharedCheck_3661_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_msg_3609_);
lean_inc(v_ref_3608_);
lean_dec(v_traceElem_3554_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3661_;
goto v_resetjp_3610_;
}
v___jp_3561_:
{
lean_object* v_toPure_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v_toPure_3563_ = lean_ctor_get(v_toApplicative_3555_, 1);
lean_inc(v_toPure_3563_);
lean_dec_ref(v_toApplicative_3555_);
v___x_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3564_, 0, v___y_3562_);
v___x_3565_ = lean_apply_2(v_toPure_3563_, lean_box(0), v___x_3564_);
return v___x_3565_;
}
v___jp_3566_:
{
lean_object* v_size_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v_size_3571_ = lean_ctor_get(v___y_3569_, 0);
v___x_3572_ = lean_unsigned_to_nat(1u);
v___x_3573_ = lean_nat_add(v_size_3571_, v___x_3572_);
v___x_3574_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3569_, v___x_3573_, v_i_3570_, v___y_3568_, v___y_3567_);
lean_dec(v_i_3570_);
v___y_3562_ = v___x_3574_;
goto v___jp_3561_;
}
v___jp_3575_:
{
lean_object* v___x_3580_; 
lean_inc_ref(v___y_3578_);
v___x_3580_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_3556_, v___f_3557_, v___y_3579_, v___y_3578_);
switch(lean_obj_tag(v___x_3580_))
{
case 0:
{
lean_object* v_index_3581_; lean_object* v_size_3582_; lean_object* v___x_3583_; 
lean_dec(v___y_3577_);
v_index_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_index_3581_);
lean_dec_ref_known(v___x_3580_, 3);
v_size_3582_ = lean_ctor_get(v___y_3579_, 0);
lean_inc(v_size_3582_);
v___x_3583_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3579_, v_size_3582_, v_index_3581_, v___y_3578_, v___y_3576_);
lean_dec(v_index_3581_);
v___y_3562_ = v___x_3583_;
goto v___jp_3561_;
}
case 1:
{
lean_object* v_index_3584_; 
lean_dec(v___y_3577_);
v_index_3584_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_index_3584_);
lean_dec_ref_known(v___x_3580_, 1);
v___y_3567_ = v___y_3576_;
v___y_3568_ = v___y_3578_;
v___y_3569_ = v___y_3579_;
v_i_3570_ = v_index_3584_;
goto v___jp_3566_;
}
default: 
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_3579_, v___y_3577_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_index_3586_; 
v_index_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_index_3586_);
lean_dec_ref_known(v___x_3585_, 1);
v___y_3567_ = v___y_3576_;
v___y_3568_ = v___y_3578_;
v___y_3569_ = v___y_3579_;
v_i_3570_ = v_index_3586_;
goto v___jp_3566_;
}
else
{
lean_dec_ref(v___y_3578_);
lean_dec_ref(v___y_3576_);
v___y_3562_ = v___y_3579_;
goto v___jp_3561_;
}
}
}
}
v___jp_3587_:
{
lean_object* v_size_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_size_3592_ = lean_ctor_get(v___y_3590_, 0);
v___x_3593_ = lean_unsigned_to_nat(1u);
v___x_3594_ = lean_nat_add(v_size_3592_, v___x_3593_);
v___x_3595_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_3590_, v___x_3594_, v_i_3591_, v___y_3589_, v___y_3588_);
lean_dec(v_i_3591_);
v___y_3562_ = v___x_3595_;
goto v___jp_3561_;
}
v___jp_3596_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
lean_inc_ref(v___f_3557_);
lean_inc_ref(v___f_3556_);
v___x_3600_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_3556_, v___f_3557_, v_____s_3558_);
lean_inc_ref(v___y_3599_);
v___x_3601_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_3556_, v___f_3557_, v___x_3600_, v___y_3599_);
switch(lean_obj_tag(v___x_3601_))
{
case 0:
{
lean_object* v_index_3602_; lean_object* v_size_3603_; lean_object* v___x_3604_; 
lean_dec(v___y_3598_);
v_index_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_index_3602_);
lean_dec_ref_known(v___x_3601_, 3);
v_size_3603_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_size_3603_);
v___x_3604_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_3600_, v_size_3603_, v_index_3602_, v___y_3599_, v___y_3597_);
lean_dec(v_index_3602_);
v___y_3562_ = v___x_3604_;
goto v___jp_3561_;
}
case 1:
{
lean_object* v_index_3605_; 
lean_dec(v___y_3598_);
v_index_3605_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_index_3605_);
lean_dec_ref_known(v___x_3601_, 1);
v___y_3588_ = v___y_3597_;
v___y_3589_ = v___y_3599_;
v___y_3590_ = v___x_3600_;
v_i_3591_ = v_index_3605_;
goto v___jp_3587_;
}
default: 
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_3600_, v___y_3598_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_index_3607_; 
v_index_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_index_3607_);
lean_dec_ref_known(v___x_3606_, 1);
v___y_3588_ = v___y_3597_;
v___y_3589_ = v___y_3599_;
v___y_3590_ = v___x_3600_;
v_i_3591_ = v_index_3607_;
goto v___jp_3587_;
}
else
{
lean_dec_ref(v___y_3599_);
lean_dec_ref(v___y_3597_);
v___y_3562_ = v___x_3600_;
goto v___jp_3561_;
}
}
}
}
v_resetjp_3610_:
{
lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v_ref_3653_; lean_object* v___y_3655_; lean_object* v___x_3658_; 
v_ref_3653_ = l_Lean_replaceRef(v_ref_3608_, v_____do__lift_3560_);
lean_dec(v_ref_3608_);
v___x_3658_ = l_Lean_Syntax_getPos_x3f(v_ref_3653_, v___x_3559_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_unsigned_to_nat(0u);
v___y_3655_ = v___x_3659_;
goto v___jp_3654_;
}
else
{
lean_object* v_val_3660_; 
v_val_3660_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_val_3660_);
lean_dec_ref_known(v___x_3658_, 1);
v___y_3655_ = v_val_3660_;
goto v___jp_3654_;
}
v___jp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 1, v___y_3615_);
lean_ctor_set(v___x_3611_, 0, v___y_3614_);
v___x_3617_ = v___x_3611_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___y_3614_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v___y_3615_);
v___x_3617_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3618_ = lean_unsigned_to_nat(0u);
v___x_3619_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
lean_inc_ref_n(v___x_3617_, 2);
lean_inc_ref_n(v___f_3557_, 2);
lean_inc_ref_n(v___f_3556_, 2);
v___x_3620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_3556_, v___f_3557_, v_____s_3558_, v___x_3617_, v___x_3619_);
v___x_3621_ = lean_array_push(v___x_3620_, v_msg_3609_);
v___x_3622_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_3556_, v___f_3557_, v_____s_3558_, v___x_3617_);
switch(lean_obj_tag(v___x_3622_))
{
case 0:
{
lean_object* v_index_3623_; lean_object* v_size_3624_; lean_object* v___x_3625_; 
lean_dec_ref(v___f_3557_);
lean_dec_ref(v___f_3556_);
v_index_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_index_3623_);
lean_dec_ref_known(v___x_3622_, 3);
v_size_3624_ = lean_ctor_get(v_____s_3558_, 0);
lean_inc(v_size_3624_);
v___x_3625_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_3558_, v_size_3624_, v_index_3623_, v___x_3617_, v___x_3621_);
lean_dec(v_index_3623_);
v___y_3562_ = v___x_3625_;
goto v___jp_3561_;
}
case 1:
{
lean_object* v_index_3626_; lean_object* v_size_3627_; lean_object* v_keyArray_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v_index_3626_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_index_3626_);
lean_dec_ref_known(v___x_3622_, 1);
v_size_3627_ = lean_ctor_get(v_____s_3558_, 0);
v_keyArray_3628_ = lean_ctor_get(v_____s_3558_, 1);
v___x_3629_ = lean_unsigned_to_nat(1u);
v___x_3630_ = lean_nat_add(v_size_3627_, v___x_3629_);
v___x_3631_ = lean_array_get_size(v_keyArray_3628_);
v___x_3632_ = lean_nat_dec_lt(v___x_3630_, v___x_3631_);
if (v___x_3632_ == 0)
{
lean_dec(v___x_3630_);
lean_dec(v_index_3626_);
v___y_3597_ = v___x_3621_;
v___y_3598_ = v___x_3618_;
v___y_3599_ = v___x_3617_;
goto v___jp_3596_;
}
else
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___x_3633_ = lean_unsigned_to_nat(4u);
v___x_3634_ = lean_nat_mul(v___x_3630_, v___x_3633_);
v___x_3635_ = lean_unsigned_to_nat(3u);
v___x_3636_ = lean_nat_mul(v___x_3631_, v___x_3635_);
v___x_3637_ = lean_nat_dec_le(v___x_3634_, v___x_3636_);
lean_dec(v___x_3636_);
lean_dec(v___x_3634_);
if (v___x_3637_ == 0)
{
lean_dec(v___x_3630_);
lean_dec(v_index_3626_);
v___y_3597_ = v___x_3621_;
v___y_3598_ = v___x_3618_;
v___y_3599_ = v___x_3617_;
goto v___jp_3596_;
}
else
{
lean_object* v___x_3638_; 
lean_dec_ref(v___f_3557_);
lean_dec_ref(v___f_3556_);
v___x_3638_ = l_Std_DHashMap_Raw_setEntry___redArg(v_____s_3558_, v___x_3630_, v_index_3626_, v___x_3617_, v___x_3621_);
lean_dec(v_index_3626_);
v___y_3562_ = v___x_3638_;
goto v___jp_3561_;
}
}
}
default: 
{
lean_object* v_size_3639_; lean_object* v_keyArray_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v_size_3639_ = lean_ctor_get(v_____s_3558_, 0);
v_keyArray_3640_ = lean_ctor_get(v_____s_3558_, 1);
v___x_3641_ = lean_unsigned_to_nat(1u);
v___x_3642_ = lean_nat_add(v_size_3639_, v___x_3641_);
v___x_3643_ = lean_array_get_size(v_keyArray_3640_);
v___x_3644_ = lean_nat_dec_lt(v___x_3642_, v___x_3643_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3645_; 
lean_dec(v___x_3642_);
lean_inc_ref(v___f_3557_);
lean_inc_ref(v___f_3556_);
v___x_3645_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_3556_, v___f_3557_, v_____s_3558_);
v___y_3576_ = v___x_3621_;
v___y_3577_ = v___x_3618_;
v___y_3578_ = v___x_3617_;
v___y_3579_ = v___x_3645_;
goto v___jp_3575_;
}
else
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3646_ = lean_unsigned_to_nat(4u);
v___x_3647_ = lean_nat_mul(v___x_3642_, v___x_3646_);
lean_dec(v___x_3642_);
v___x_3648_ = lean_unsigned_to_nat(3u);
v___x_3649_ = lean_nat_mul(v___x_3643_, v___x_3648_);
v___x_3650_ = lean_nat_dec_le(v___x_3647_, v___x_3649_);
lean_dec(v___x_3649_);
lean_dec(v___x_3647_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; 
lean_inc_ref(v___f_3557_);
lean_inc_ref(v___f_3556_);
v___x_3651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_3556_, v___f_3557_, v_____s_3558_);
v___y_3576_ = v___x_3621_;
v___y_3577_ = v___x_3618_;
v___y_3578_ = v___x_3617_;
v___y_3579_ = v___x_3651_;
goto v___jp_3575_;
}
else
{
v___y_3576_ = v___x_3621_;
v___y_3577_ = v___x_3618_;
v___y_3578_ = v___x_3617_;
v___y_3579_ = v_____s_3558_;
goto v___jp_3575_;
}
}
}
}
}
}
v___jp_3654_:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_Syntax_getTailPos_x3f(v_ref_3653_, v___x_3559_);
lean_dec(v_ref_3653_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_inc(v___y_3655_);
v___y_3614_ = v___y_3655_;
v___y_3615_ = v___y_3655_;
goto v___jp_3613_;
}
else
{
lean_object* v_val_3657_; 
v_val_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_val_3657_);
lean_dec_ref_known(v___x_3656_, 1);
v___y_3614_ = v___y_3655_;
v___y_3615_ = v_val_3657_;
goto v___jp_3613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object* v_traceElem_3662_, lean_object* v_toApplicative_3663_, lean_object* v___f_3664_, lean_object* v___f_3665_, lean_object* v_____s_3666_, lean_object* v___x_3667_, lean_object* v_____do__lift_3668_){
_start:
{
uint8_t v___x_2406__boxed_3669_; lean_object* v_res_3670_; 
v___x_2406__boxed_3669_ = lean_unbox(v___x_3667_);
v_res_3670_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_traceElem_3662_, v_toApplicative_3663_, v___f_3664_, v___f_3665_, v_____s_3666_, v___x_2406__boxed_3669_, v_____do__lift_3668_);
lean_dec(v_____do__lift_3668_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object* v_inst_3671_, lean_object* v_toApplicative_3672_, lean_object* v___f_3673_, lean_object* v___f_3674_, uint8_t v___x_3675_, lean_object* v_toBind_3676_, lean_object* v_traceElem_3677_, lean_object* v_____s_3678_){
_start:
{
lean_object* v_getRef_3679_; lean_object* v___x_3680_; lean_object* v___f_3681_; lean_object* v___x_3682_; 
v_getRef_3679_ = lean_ctor_get(v_inst_3671_, 0);
lean_inc(v_getRef_3679_);
lean_dec_ref(v_inst_3671_);
v___x_3680_ = lean_box(v___x_3675_);
v___f_3681_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__8___boxed), 7, 6);
lean_closure_set(v___f_3681_, 0, v_traceElem_3677_);
lean_closure_set(v___f_3681_, 1, v_toApplicative_3672_);
lean_closure_set(v___f_3681_, 2, v___f_3673_);
lean_closure_set(v___f_3681_, 3, v___f_3674_);
lean_closure_set(v___f_3681_, 4, v_____s_3678_);
lean_closure_set(v___f_3681_, 5, v___x_3680_);
v___x_3682_ = lean_apply_4(v_toBind_3676_, lean_box(0), lean_box(0), v_getRef_3679_, v___f_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object* v_inst_3683_, lean_object* v_toApplicative_3684_, lean_object* v___f_3685_, lean_object* v___f_3686_, lean_object* v___x_3687_, lean_object* v_toBind_3688_, lean_object* v_traceElem_3689_, lean_object* v_____s_3690_){
_start:
{
uint8_t v___x_2593__boxed_3691_; lean_object* v_res_3692_; 
v___x_2593__boxed_3691_ = lean_unbox(v___x_3687_);
v_res_3692_ = l_Lean_addTraceAsMessages___redArg___lam__9(v_inst_3683_, v_toApplicative_3684_, v___f_3685_, v___f_3686_, v___x_2593__boxed_3691_, v_toBind_3688_, v_traceElem_3689_, v_____s_3690_);
return v_res_3692_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__10___closed__0(void){
_start:
{
lean_object* v___x_3693_; lean_object* v___f_3694_; 
v___x_3693_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_3694_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3694_, 0, v___x_3693_);
return v___f_3694_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___f_3695_; lean_object* v___f_3696_; 
v___f_3695_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__10___closed__0, &l_Lean_addTraceAsMessages___redArg___lam__10___closed__0_once, _init_l_Lean_addTraceAsMessages___redArg___lam__10___closed__0);
v___f_3696_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3696_, 0, v___f_3695_);
lean_closure_set(v___f_3696_, 1, v___f_3695_);
return v___f_3696_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__10___closed__4(void){
_start:
{
lean_object* v_cellCount_3700_; lean_object* v___x_3701_; 
v_cellCount_3700_ = lean_unsigned_to_nat(16u);
v___x_3701_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3700_);
return v___x_3701_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__10___closed__5(void){
_start:
{
lean_object* v_cellCount_3702_; lean_object* v___x_3703_; 
v_cellCount_3702_ = lean_unsigned_to_nat(16u);
v___x_3703_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3702_);
return v___x_3703_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__10___closed__6(void){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v_pos2traces_3707_; 
v___x_3704_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__10___closed__5, &l_Lean_addTraceAsMessages___redArg___lam__10___closed__5_once, _init_l_Lean_addTraceAsMessages___redArg___lam__10___closed__5);
v___x_3705_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__10___closed__4, &l_Lean_addTraceAsMessages___redArg___lam__10___closed__4_once, _init_l_Lean_addTraceAsMessages___redArg___lam__10___closed__4);
v___x_3706_ = lean_unsigned_to_nat(0u);
v_pos2traces_3707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_pos2traces_3707_, 0, v___x_3706_);
lean_ctor_set(v_pos2traces_3707_, 1, v___x_3705_);
lean_ctor_set(v_pos2traces_3707_, 2, v___x_3704_);
return v_pos2traces_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object* v_inst_3708_, lean_object* v_toApplicative_3709_, lean_object* v_toBind_3710_, lean_object* v_inst_3711_, lean_object* v___f_3712_, lean_object* v_traces_3713_){
_start:
{
uint8_t v___x_3714_; 
v___x_3714_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_3713_);
if (v___x_3714_ == 0)
{
lean_object* v___f_3715_; lean_object* v___f_3716_; lean_object* v___x_3717_; lean_object* v___f_3718_; lean_object* v_pos2traces_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___f_3715_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__10___closed__1, &l_Lean_addTraceAsMessages___redArg___lam__10___closed__1_once, _init_l_Lean_addTraceAsMessages___redArg___lam__10___closed__1);
v___f_3716_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___lam__10___closed__3));
v___x_3717_ = lean_box(v___x_3714_);
lean_inc(v_toBind_3710_);
v___f_3718_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_3718_, 0, v_inst_3708_);
lean_closure_set(v___f_3718_, 1, v_toApplicative_3709_);
lean_closure_set(v___f_3718_, 2, v___f_3715_);
lean_closure_set(v___f_3718_, 3, v___f_3716_);
lean_closure_set(v___f_3718_, 4, v___x_3717_);
lean_closure_set(v___f_3718_, 5, v_toBind_3710_);
v_pos2traces_3719_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__10___closed__6, &l_Lean_addTraceAsMessages___redArg___lam__10___closed__6_once, _init_l_Lean_addTraceAsMessages___redArg___lam__10___closed__6);
v___x_3720_ = l_Lean_PersistentArray_forIn___redArg(v_inst_3711_, v_traces_3713_, v_pos2traces_3719_, v___f_3718_);
v___x_3721_ = lean_apply_4(v_toBind_3710_, lean_box(0), lean_box(0), v___x_3720_, v___f_3712_);
return v___x_3721_;
}
else
{
lean_object* v_toPure_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec(v___f_3712_);
lean_dec_ref(v_inst_3711_);
lean_dec(v_toBind_3710_);
lean_dec_ref(v_inst_3708_);
v_toPure_3722_ = lean_ctor_get(v_toApplicative_3709_, 1);
lean_inc(v_toPure_3722_);
lean_dec_ref(v_toApplicative_3709_);
v___x_3723_ = lean_box(0);
v___x_3724_ = lean_apply_2(v_toPure_3722_, lean_box(0), v___x_3723_);
return v___x_3724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object* v_inst_3725_, lean_object* v_toApplicative_3726_, lean_object* v_toBind_3727_, lean_object* v_inst_3728_, lean_object* v___f_3729_, lean_object* v_traces_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Lean_addTraceAsMessages___redArg___lam__10(v_inst_3725_, v_toApplicative_3726_, v_toBind_3727_, v_inst_3728_, v___f_3729_, v_traces_3730_);
lean_dec_ref(v_traces_3730_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11(lean_object* v_toApplicative_3732_, lean_object* v___f_3733_, lean_object* v_inst_3734_, lean_object* v_toBind_3735_, lean_object* v_inst_3736_, lean_object* v___f_3737_, lean_object* v___f_3738_, lean_object* v_inst_3739_, lean_object* v_inst_3740_, lean_object* v_____do__lift_3741_){
_start:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3746_ = l_Lean_KVMap_instValueBool;
v___x_3747_ = l_Lean_KVMap_instValueString;
v___x_3748_ = l_Lean_trace_profiler_output;
v___x_3749_ = l_Lean_Option_get_x3f___redArg(v___x_3747_, v_____do__lift_3741_, v___x_3748_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v___x_3750_; lean_object* v___x_3751_; uint8_t v___x_3752_; 
v___x_3750_ = l_Lean_trace_profiler_serve;
v___x_3751_ = l_Lean_Option_get___redArg(v___x_3746_, v_____do__lift_3741_, v___x_3750_);
v___x_3752_ = lean_unbox(v___x_3751_);
lean_dec(v___x_3751_);
if (v___x_3752_ == 0)
{
uint8_t v___x_3753_; lean_object* v___x_3754_; lean_object* v___f_3755_; lean_object* v___f_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3753_ = 1;
v___x_3754_ = lean_box(v___x_3753_);
lean_inc_ref_n(v_inst_3736_, 2);
lean_inc_n(v_toBind_3735_, 2);
lean_inc_ref(v_toApplicative_3732_);
v___f_3755_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__7___boxed), 9, 8);
lean_closure_set(v___f_3755_, 0, v___f_3733_);
lean_closure_set(v___f_3755_, 1, v_toApplicative_3732_);
lean_closure_set(v___f_3755_, 2, v___x_3754_);
lean_closure_set(v___f_3755_, 3, v_inst_3734_);
lean_closure_set(v___f_3755_, 4, v_toBind_3735_);
lean_closure_set(v___f_3755_, 5, v_inst_3736_);
lean_closure_set(v___f_3755_, 6, v___f_3737_);
lean_closure_set(v___f_3755_, 7, v___f_3738_);
v___f_3756_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__10___boxed), 6, 5);
lean_closure_set(v___f_3756_, 0, v_inst_3739_);
lean_closure_set(v___f_3756_, 1, v_toApplicative_3732_);
lean_closure_set(v___f_3756_, 2, v_toBind_3735_);
lean_closure_set(v___f_3756_, 3, v_inst_3736_);
lean_closure_set(v___f_3756_, 4, v___f_3755_);
v___x_3757_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3736_, v_inst_3740_);
v___x_3758_ = lean_apply_4(v_toBind_3735_, lean_box(0), lean_box(0), v___x_3757_, v___f_3756_);
return v___x_3758_;
}
else
{
lean_dec_ref(v_inst_3740_);
lean_dec_ref(v_inst_3739_);
lean_dec_ref(v___f_3738_);
lean_dec(v___f_3737_);
lean_dec_ref(v_inst_3736_);
lean_dec(v_toBind_3735_);
lean_dec_ref(v_inst_3734_);
lean_dec_ref(v___f_3733_);
goto v___jp_3742_;
}
}
else
{
lean_dec_ref_known(v___x_3749_, 1);
lean_dec_ref(v_inst_3740_);
lean_dec_ref(v_inst_3739_);
lean_dec_ref(v___f_3738_);
lean_dec(v___f_3737_);
lean_dec_ref(v_inst_3736_);
lean_dec(v_toBind_3735_);
lean_dec_ref(v_inst_3734_);
lean_dec_ref(v___f_3733_);
goto v___jp_3742_;
}
v___jp_3742_:
{
lean_object* v_toPure_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_toPure_3743_ = lean_ctor_get(v_toApplicative_3732_, 1);
lean_inc(v_toPure_3743_);
lean_dec_ref(v_toApplicative_3732_);
v___x_3744_ = lean_box(0);
v___x_3745_ = lean_apply_2(v_toPure_3743_, lean_box(0), v___x_3744_);
return v___x_3745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___boxed(lean_object* v_toApplicative_3759_, lean_object* v___f_3760_, lean_object* v_inst_3761_, lean_object* v_toBind_3762_, lean_object* v_inst_3763_, lean_object* v___f_3764_, lean_object* v___f_3765_, lean_object* v_inst_3766_, lean_object* v_inst_3767_, lean_object* v_____do__lift_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_addTraceAsMessages___redArg___lam__11(v_toApplicative_3759_, v___f_3760_, v_inst_3761_, v_toBind_3762_, v_inst_3763_, v___f_3764_, v___f_3765_, v_inst_3766_, v_inst_3767_, v_____do__lift_3768_);
lean_dec_ref(v_____do__lift_3768_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object* v_inst_3772_, lean_object* v_inst_3773_, lean_object* v_inst_3774_, lean_object* v_inst_3775_, lean_object* v_inst_3776_){
_start:
{
lean_object* v_toApplicative_3777_; lean_object* v_toBind_3778_; lean_object* v___f_3779_; lean_object* v___f_3780_; lean_object* v___f_3781_; lean_object* v___f_3782_; lean_object* v___x_3783_; 
v_toApplicative_3777_ = lean_ctor_get(v_inst_3773_, 0);
lean_inc_ref_n(v_toApplicative_3777_, 2);
v_toBind_3778_ = lean_ctor_get(v_inst_3773_, 1);
lean_inc_n(v_toBind_3778_, 2);
v___f_3779_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__0));
v___f_3780_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3780_, 0, v_toApplicative_3777_);
v___f_3781_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__1));
v___f_3782_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__11___boxed), 10, 9);
lean_closure_set(v___f_3782_, 0, v_toApplicative_3777_);
lean_closure_set(v___f_3782_, 1, v___f_3781_);
lean_closure_set(v___f_3782_, 2, v_inst_3775_);
lean_closure_set(v___f_3782_, 3, v_toBind_3778_);
lean_closure_set(v___f_3782_, 4, v_inst_3773_);
lean_closure_set(v___f_3782_, 5, v___f_3780_);
lean_closure_set(v___f_3782_, 6, v___f_3779_);
lean_closure_set(v___f_3782_, 7, v_inst_3774_);
lean_closure_set(v___f_3782_, 8, v_inst_3776_);
v___x_3783_ = lean_apply_4(v_toBind_3778_, lean_box(0), lean_box(0), v_inst_3772_, v___f_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object* v_m_3784_, lean_object* v_inst_3785_, lean_object* v_inst_3786_, lean_object* v_inst_3787_, lean_object* v_inst_3788_, lean_object* v_inst_3789_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Lean_addTraceAsMessages___redArg(v_inst_3785_, v_inst_3786_, v_inst_3787_, v_inst_3788_, v_inst_3789_);
return v___x_3790_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3832_ = lean_unsigned_to_nat(2826257906u);
v___x_3833_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3834_ = l_Lean_Name_num___override(v___x_3833_, v___x_3832_);
return v___x_3834_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3836_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3837_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3838_ = l_Lean_Name_str___override(v___x_3837_, v___x_3836_);
return v___x_3838_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3840_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3841_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3842_ = l_Lean_Name_str___override(v___x_3841_, v___x_3840_);
return v___x_3842_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3843_ = lean_unsigned_to_nat(2u);
v___x_3844_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3845_ = l_Lean_Name_num___override(v___x_3844_, v___x_3843_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3847_; uint8_t v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3847_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3848_ = 0;
v___x_3849_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3850_ = l_Lean_registerTraceClass(v___x_3847_, v___x_3848_, v___x_3849_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object* v_a_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
return v_res_3852_;
}
}
lean_object* runtime_initialize_Lean_Elab_Exception(uint8_t builtin);
lean_object* runtime_initialize_Lean_Log(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Trace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_trace_profiler_serve = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_trace_profiler_serve);
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
