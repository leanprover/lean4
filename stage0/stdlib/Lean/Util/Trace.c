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
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_MonadCacheT_instMonadExceptOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_instHashableRaw_hash___boxed(lean_object*);
lean_object* l_instMonadExceptOfEIO___redArg();
lean_object* l_Lean_MessageData_format___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BaseIO_toIO___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueString;
lean_object* l_Lean_Option_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringFormat___lam__0(lean_object*);
lean_object* l_IO_println___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_instDecidableEqRaw___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO___redArg();
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO___redArg___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResultBool___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultBool___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResultBool___redArg___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResultBool___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___redArg();
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResultOption___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultOption___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResultOption___redArg___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResultOption___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___redArg();
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultExpr___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResultExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultExpr___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResultExpr___redArg___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResultExpr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___redArg();
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instExceptToTraceResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResult___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instExceptToTraceResult___redArg___closed__0 = (const lean_object*)&l_Lean_instExceptToTraceResult___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___redArg();
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, double, double, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, double, double, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___closed__0;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___closed__1;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___closed__2;
static lean_once_cell_t l_Lean_addTraceAsMessages___redArg___lam__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHashableRaw_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___closed__0 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___closed__0_value;
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableProd___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_addTraceAsMessages___redArg___closed__0_value),((lean_object*)&l_Lean_addTraceAsMessages___redArg___closed__0_value)} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___closed__1 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___closed__1_value;
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_addTraceAsMessages___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___closed__2 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___closed__2_value;
static const lean_closure_object l_Lean_addTraceAsMessages___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_addTraceAsMessages___redArg___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addTraceAsMessages___redArg___closed__3 = (const lean_object*)&l_Lean_addTraceAsMessages___redArg___closed__3_value;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(lean_object* v_m_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_buckets_228_; lean_object* v___x_229_; uint64_t v___y_231_; 
v_buckets_228_ = lean_ctor_get(v_m_226_, 1);
v___x_229_ = lean_array_get_size(v_buckets_228_);
if (lean_obj_tag(v_a_227_) == 0)
{
uint64_t v___x_245_; 
v___x_245_ = 1723ULL;
v___y_231_ = v___x_245_;
goto v___jp_230_;
}
else
{
uint64_t v_hash_246_; 
v_hash_246_ = lean_ctor_get_uint64(v_a_227_, sizeof(void*)*2);
v___y_231_ = v_hash_246_;
goto v___jp_230_;
}
v___jp_230_:
{
uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v_fold_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_232_ = 32ULL;
v___x_233_ = lean_uint64_shift_right(v___y_231_, v___x_232_);
v_fold_234_ = lean_uint64_xor(v___y_231_, v___x_233_);
v___x_235_ = 16ULL;
v___x_236_ = lean_uint64_shift_right(v_fold_234_, v___x_235_);
v___x_237_ = lean_uint64_xor(v_fold_234_, v___x_236_);
v___x_238_ = lean_uint64_to_usize(v___x_237_);
v___x_239_ = lean_usize_of_nat(v___x_229_);
v___x_240_ = ((size_t)1ULL);
v___x_241_ = lean_usize_sub(v___x_239_, v___x_240_);
v___x_242_ = lean_usize_land(v___x_238_, v___x_241_);
v___x_243_ = lean_array_uget_borrowed(v_buckets_228_, v___x_242_);
v___x_244_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_227_, v___x_243_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___boxed(lean_object* v_m_247_, lean_object* v_a_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_247_, v_a_248_);
lean_dec(v_a_248_);
lean_dec_ref(v_m_247_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object* v_inherited_251_, lean_object* v_opts_252_, lean_object* v_opt_253_){
_start:
{
lean_object* v_map_259_; lean_object* v___x_260_; 
v_map_259_ = lean_ctor_get(v_opts_252_, 0);
v___x_260_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_259_, v_opt_253_);
if (lean_obj_tag(v___x_260_) == 0)
{
goto v___jp_254_;
}
else
{
lean_object* v_val_261_; 
v_val_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v___x_260_, 1);
if (lean_obj_tag(v_val_261_) == 1)
{
uint8_t v_v_262_; 
v_v_262_ = lean_ctor_get_uint8(v_val_261_, 0);
lean_dec_ref_known(v_val_261_, 0);
return v_v_262_;
}
else
{
lean_dec(v_val_261_);
goto v___jp_254_;
}
}
v___jp_254_:
{
if (lean_obj_tag(v_opt_253_) == 1)
{
lean_object* v_pre_255_; uint8_t v___x_256_; 
v_pre_255_ = lean_ctor_get(v_opt_253_, 0);
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_inherited_251_, v_opt_253_);
if (v___x_256_ == 0)
{
return v___x_256_;
}
else
{
v_opt_253_ = v_pre_255_;
goto _start;
}
}
else
{
uint8_t v___x_258_; 
v___x_258_ = 0;
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go___boxed(lean_object* v_inherited_263_, lean_object* v_opts_264_, lean_object* v_opt_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_263_, v_opts_264_, v_opt_265_);
lean_dec(v_opt_265_);
lean_dec_ref(v_opts_264_);
lean_dec_ref(v_inherited_263_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(lean_object* v_00_u03b2_268_, lean_object* v_m_269_, lean_object* v_a_270_){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_269_, v_a_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(lean_object* v_00_u03b2_272_, lean_object* v_m_273_, lean_object* v_a_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(v_00_u03b2_272_, v_m_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_m_273_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(lean_object* v_00_u03b2_277_, lean_object* v_a_278_, lean_object* v_x_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_278_, v_x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_281_, lean_object* v_a_282_, lean_object* v_x_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(v_00_u03b2_281_, v_a_282_, v_x_283_);
lean_dec(v_x_283_);
lean_dec(v_a_282_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT uint8_t l_Lean_checkTraceOption(lean_object* v_inherited_289_, lean_object* v_opts_290_, lean_object* v_cls_291_){
_start:
{
uint8_t v_hasTrace_292_; 
v_hasTrace_292_ = lean_ctor_get_uint8(v_opts_290_, sizeof(void*)*1);
if (v_hasTrace_292_ == 0)
{
lean_dec(v_cls_291_);
return v_hasTrace_292_;
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_293_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_294_ = l_Lean_Name_append(v___x_293_, v_cls_291_);
v___x_295_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_289_, v_opts_290_, v___x_294_);
lean_dec(v___x_294_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkTraceOption___boxed(lean_object* v_inherited_296_, lean_object* v_opts_297_, lean_object* v_cls_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Lean_checkTraceOption(v_inherited_296_, v_opts_297_, v_cls_298_);
lean_dec_ref(v_opts_297_);
lean_dec_ref(v_inherited_296_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0(lean_object* v_toPure_301_, lean_object* v_cls_302_, lean_object* v_____do__lift_303_, lean_object* v_____do__lift_304_){
_start:
{
uint8_t v_hasTrace_305_; 
v_hasTrace_305_ = lean_ctor_get_uint8(v_____do__lift_304_, sizeof(void*)*1);
if (v_hasTrace_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_cls_302_);
v___x_306_ = lean_box(v_hasTrace_305_);
v___x_307_ = lean_apply_2(v_toPure_301_, lean_box(0), v___x_306_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_308_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_309_ = l_Lean_Name_append(v___x_308_, v_cls_302_);
v___x_310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_303_, v_____do__lift_304_, v___x_309_);
lean_dec(v___x_309_);
v___x_311_ = lean_box(v___x_310_);
v___x_312_ = lean_apply_2(v_toPure_301_, lean_box(0), v___x_311_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0___boxed(lean_object* v_toPure_313_, lean_object* v_cls_314_, lean_object* v_____do__lift_315_, lean_object* v_____do__lift_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_isTracingEnabledFor___redArg___lam__0(v_toPure_313_, v_cls_314_, v_____do__lift_315_, v_____do__lift_316_);
lean_dec_ref(v_____do__lift_316_);
lean_dec_ref(v_____do__lift_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__1(lean_object* v_inst_318_, lean_object* v_toPure_319_, lean_object* v_cls_320_, lean_object* v_toBind_321_, lean_object* v_____do__lift_322_){
_start:
{
lean_object* v_getOptionsUnrestricted_323_; lean_object* v___f_324_; lean_object* v___x_325_; 
v_getOptionsUnrestricted_323_ = lean_ctor_get(v_inst_318_, 1);
lean_inc(v_getOptionsUnrestricted_323_);
lean_dec_ref(v_inst_318_);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_324_, 0, v_toPure_319_);
lean_closure_set(v___f_324_, 1, v_cls_320_);
lean_closure_set(v___f_324_, 2, v_____do__lift_322_);
v___x_325_ = lean_apply_4(v_toBind_321_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_323_, v___f_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_cls_329_){
_start:
{
lean_object* v_toApplicative_330_; lean_object* v_toBind_331_; lean_object* v_getInheritedTraceOptions_332_; lean_object* v_toPure_333_; lean_object* v___f_334_; lean_object* v___x_335_; 
v_toApplicative_330_ = lean_ctor_get(v_inst_326_, 0);
lean_inc_ref(v_toApplicative_330_);
v_toBind_331_ = lean_ctor_get(v_inst_326_, 1);
lean_inc_n(v_toBind_331_, 2);
lean_dec_ref(v_inst_326_);
v_getInheritedTraceOptions_332_ = lean_ctor_get(v_inst_327_, 2);
lean_inc(v_getInheritedTraceOptions_332_);
lean_dec_ref(v_inst_327_);
v_toPure_333_ = lean_ctor_get(v_toApplicative_330_, 1);
lean_inc(v_toPure_333_);
lean_dec_ref(v_toApplicative_330_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_334_, 0, v_inst_328_);
lean_closure_set(v___f_334_, 1, v_toPure_333_);
lean_closure_set(v___f_334_, 2, v_cls_329_);
lean_closure_set(v___f_334_, 3, v_toBind_331_);
v___x_335_ = lean_apply_4(v_toBind_331_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_332_, v___f_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor(lean_object* v_m_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_cls_340_){
_start:
{
lean_object* v_toApplicative_341_; lean_object* v_toBind_342_; lean_object* v_getInheritedTraceOptions_343_; lean_object* v_toPure_344_; lean_object* v___f_345_; lean_object* v___x_346_; 
v_toApplicative_341_ = lean_ctor_get(v_inst_337_, 0);
lean_inc_ref(v_toApplicative_341_);
v_toBind_342_ = lean_ctor_get(v_inst_337_, 1);
lean_inc_n(v_toBind_342_, 2);
lean_dec_ref(v_inst_337_);
v_getInheritedTraceOptions_343_ = lean_ctor_get(v_inst_338_, 2);
lean_inc(v_getInheritedTraceOptions_343_);
lean_dec_ref(v_inst_338_);
v_toPure_344_ = lean_ctor_get(v_toApplicative_341_, 1);
lean_inc(v_toPure_344_);
lean_dec_ref(v_toApplicative_341_);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_345_, 0, v_inst_339_);
lean_closure_set(v___f_345_, 1, v_toPure_344_);
lean_closure_set(v___f_345_, 2, v_cls_340_);
lean_closure_set(v___f_345_, 3, v_toBind_342_);
v___x_346_ = lean_apply_4(v_toBind_342_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_343_, v___f_345_);
return v___x_346_;
}
}
LEAN_EXPORT uint8_t lean_is_trace_class_enabled(lean_object* v_opts_347_, lean_object* v_cls_348_){
_start:
{
uint8_t v_hasTrace_350_; 
v_hasTrace_350_ = lean_ctor_get_uint8(v_opts_347_, sizeof(void*)*1);
if (v_hasTrace_350_ == 0)
{
lean_dec(v_cls_348_);
lean_dec_ref(v_opts_347_);
return v_hasTrace_350_;
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_351_ = l_Lean_inheritedTraceOptions;
v___x_352_ = lean_st_ref_get(v___x_351_);
v___x_353_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_354_ = l_Lean_Name_append(v___x_353_, v_cls_348_);
v___x_355_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_352_, v_opts_347_, v___x_354_);
lean_dec(v___x_354_);
lean_dec_ref(v_opts_347_);
lean_dec(v___x_352_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object* v_opts_356_, lean_object* v_cls_357_, lean_object* v_a_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = lean_is_trace_class_enabled(v_opts_356_, v_cls_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object* v_toPure_361_, lean_object* v_s_362_){
_start:
{
lean_object* v_traces_363_; lean_object* v___x_364_; 
v_traces_363_ = lean_ctor_get(v_s_362_, 0);
lean_inc_ref(v_traces_363_);
lean_dec_ref(v_s_362_);
v___x_364_ = lean_apply_2(v_toPure_361_, lean_box(0), v_traces_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object* v_inst_365_, lean_object* v_inst_366_){
_start:
{
lean_object* v_toApplicative_367_; lean_object* v_toBind_368_; lean_object* v_getTraceState_369_; lean_object* v_toPure_370_; lean_object* v___f_371_; lean_object* v___x_372_; 
v_toApplicative_367_ = lean_ctor_get(v_inst_365_, 0);
lean_inc_ref(v_toApplicative_367_);
v_toBind_368_ = lean_ctor_get(v_inst_365_, 1);
lean_inc(v_toBind_368_);
lean_dec_ref(v_inst_365_);
v_getTraceState_369_ = lean_ctor_get(v_inst_366_, 1);
lean_inc(v_getTraceState_369_);
lean_dec_ref(v_inst_366_);
v_toPure_370_ = lean_ctor_get(v_toApplicative_367_, 1);
lean_inc(v_toPure_370_);
lean_dec_ref(v_toApplicative_367_);
v___f_371_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_371_, 0, v_toPure_370_);
v___x_372_ = lean_apply_4(v_toBind_368_, lean_box(0), lean_box(0), v_getTraceState_369_, v___f_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object* v_m_373_, lean_object* v_inst_374_, lean_object* v_inst_375_){
_start:
{
lean_object* v_toApplicative_376_; lean_object* v_toBind_377_; lean_object* v_getTraceState_378_; lean_object* v_toPure_379_; lean_object* v___f_380_; lean_object* v___x_381_; 
v_toApplicative_376_ = lean_ctor_get(v_inst_374_, 0);
lean_inc_ref(v_toApplicative_376_);
v_toBind_377_ = lean_ctor_get(v_inst_374_, 1);
lean_inc(v_toBind_377_);
lean_dec_ref(v_inst_374_);
v_getTraceState_378_ = lean_ctor_get(v_inst_375_, 1);
lean_inc(v_getTraceState_378_);
lean_dec_ref(v_inst_375_);
v_toPure_379_ = lean_ctor_get(v_toApplicative_376_, 1);
lean_inc(v_toPure_379_);
lean_dec_ref(v_toApplicative_376_);
v___f_380_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_380_, 0, v_toPure_379_);
v___x_381_ = lean_apply_4(v_toBind_377_, lean_box(0), lean_box(0), v_getTraceState_378_, v___f_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object* v_f_382_, lean_object* v_s_383_){
_start:
{
uint64_t v_tid_384_; lean_object* v_traces_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_393_; 
v_tid_384_ = lean_ctor_get_uint64(v_s_383_, sizeof(void*)*1);
v_traces_385_ = lean_ctor_get(v_s_383_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v_s_383_);
if (v_isSharedCheck_393_ == 0)
{
v___x_387_ = v_s_383_;
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_traces_385_);
lean_dec(v_s_383_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_apply_1(v_f_382_, v_traces_385_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_389_);
lean_ctor_set_uint64(v_reuseFailAlloc_392_, sizeof(void*)*1, v_tid_384_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object* v_inst_394_, lean_object* v_f_395_){
_start:
{
lean_object* v_modifyTraceState_396_; lean_object* v___f_397_; lean_object* v___x_398_; 
v_modifyTraceState_396_ = lean_ctor_get(v_inst_394_, 0);
lean_inc(v_modifyTraceState_396_);
lean_dec_ref(v_inst_394_);
v___f_397_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_397_, 0, v_f_395_);
v___x_398_ = lean_apply_1(v_modifyTraceState_396_, v___f_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object* v_m_399_, lean_object* v_inst_400_, lean_object* v_f_401_){
_start:
{
lean_object* v_modifyTraceState_402_; lean_object* v___f_403_; lean_object* v___x_404_; 
v_modifyTraceState_402_ = lean_ctor_get(v_inst_400_, 0);
lean_inc(v_modifyTraceState_402_);
lean_dec_ref(v_inst_400_);
v___f_403_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_403_, 0, v_f_401_);
v___x_404_ = lean_apply_1(v_modifyTraceState_402_, v___f_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object* v_s_405_, lean_object* v_x_406_){
_start:
{
lean_inc_ref(v_s_405_);
return v_s_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object* v_s_407_, lean_object* v_x_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_setTraceState___redArg___lam__0(v_s_407_, v_x_408_);
lean_dec_ref(v_x_408_);
lean_dec_ref(v_s_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object* v_inst_410_, lean_object* v_s_411_){
_start:
{
lean_object* v_modifyTraceState_412_; lean_object* v___f_413_; lean_object* v___x_414_; 
v_modifyTraceState_412_ = lean_ctor_get(v_inst_410_, 0);
lean_inc(v_modifyTraceState_412_);
lean_dec_ref(v_inst_410_);
v___f_413_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_413_, 0, v_s_411_);
v___x_414_ = lean_apply_1(v_modifyTraceState_412_, v___f_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object* v_m_415_, lean_object* v_inst_416_, lean_object* v_s_417_){
_start:
{
lean_object* v_modifyTraceState_418_; lean_object* v___f_419_; lean_object* v___x_420_; 
v_modifyTraceState_418_ = lean_ctor_get(v_inst_416_, 0);
lean_inc(v_modifyTraceState_418_);
lean_dec_ref(v_inst_416_);
v___f_419_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_419_, 0, v_s_417_);
v___x_420_ = lean_apply_1(v_modifyTraceState_418_, v___f_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object* v_s_421_){
_start:
{
uint64_t v_tid_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_432_; 
v_tid_422_ = lean_ctor_get_uint64(v_s_421_, sizeof(void*)*1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_s_421_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v_s_421_, 0);
lean_dec(v_unused_433_);
v___x_424_ = v_s_421_;
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
else
{
lean_dec(v_s_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_426_ = lean_unsigned_to_nat(32u);
v___x_427_ = lean_mk_empty_array_with_capacity(v___x_426_);
lean_dec_ref(v___x_427_);
v___x_428_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__1, &l_Lean_instInhabitedTraceState_default___closed__1_once, _init_l_Lean_instInhabitedTraceState_default___closed__1);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_428_);
v___x_430_ = v___x_424_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
lean_ctor_set_uint64(v_reuseFailAlloc_431_, sizeof(void*)*1, v_tid_422_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object* v_toPure_434_, lean_object* v_oldTraces_435_, lean_object* v_____r_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lean_apply_2(v_toPure_434_, lean_box(0), v_oldTraces_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object* v_toPure_438_, lean_object* v_modifyTraceState_439_, lean_object* v___f_440_, lean_object* v_toBind_441_, lean_object* v_oldTraces_442_){
_start:
{
lean_object* v___f_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___f_443_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_443_, 0, v_toPure_438_);
lean_closure_set(v___f_443_, 1, v_oldTraces_442_);
v___x_444_ = lean_apply_1(v_modifyTraceState_439_, v___f_440_);
v___x_445_ = lean_apply_4(v_toBind_441_, lean_box(0), lean_box(0), v___x_444_, v___f_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object* v_inst_447_, lean_object* v_inst_448_){
_start:
{
lean_object* v_toApplicative_449_; lean_object* v_toBind_450_; lean_object* v_modifyTraceState_451_; lean_object* v_getTraceState_452_; lean_object* v_toPure_453_; lean_object* v___f_454_; lean_object* v___f_455_; lean_object* v___f_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_toApplicative_449_ = lean_ctor_get(v_inst_447_, 0);
lean_inc_ref(v_toApplicative_449_);
v_toBind_450_ = lean_ctor_get(v_inst_447_, 1);
lean_inc_n(v_toBind_450_, 3);
lean_dec_ref(v_inst_447_);
v_modifyTraceState_451_ = lean_ctor_get(v_inst_448_, 0);
lean_inc(v_modifyTraceState_451_);
v_getTraceState_452_ = lean_ctor_get(v_inst_448_, 1);
lean_inc(v_getTraceState_452_);
lean_dec_ref(v_inst_448_);
v_toPure_453_ = lean_ctor_get(v_toApplicative_449_, 1);
lean_inc_n(v_toPure_453_, 2);
lean_dec_ref(v_toApplicative_449_);
v___f_454_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0));
v___f_455_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_455_, 0, v_toPure_453_);
lean_closure_set(v___f_455_, 1, v_modifyTraceState_451_);
lean_closure_set(v___f_455_, 2, v___f_454_);
lean_closure_set(v___f_455_, 3, v_toBind_450_);
v___f_456_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_456_, 0, v_toPure_453_);
v___x_457_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v_getTraceState_452_, v___f_456_);
v___x_458_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v___x_457_, v___f_455_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object* v_m_459_, lean_object* v_inst_460_, lean_object* v_inst_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_460_, v_inst_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object* v_ref_463_, lean_object* v_msg_464_, lean_object* v_s_465_){
_start:
{
uint64_t v_tid_466_; lean_object* v_traces_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_476_; 
v_tid_466_ = lean_ctor_get_uint64(v_s_465_, sizeof(void*)*1);
v_traces_467_ = lean_ctor_get(v_s_465_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_s_465_);
if (v_isSharedCheck_476_ == 0)
{
v___x_469_ = v_s_465_;
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_traces_467_);
lean_dec(v_s_465_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v_ref_463_);
lean_ctor_set(v___x_471_, 1, v_msg_464_);
v___x_472_ = l_Lean_PersistentArray_push___redArg(v_traces_467_, v___x_471_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_472_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
lean_ctor_set_uint64(v_reuseFailAlloc_475_, sizeof(void*)*1, v_tid_466_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object* v_inst_477_, lean_object* v_ref_478_, lean_object* v_msg_479_){
_start:
{
lean_object* v_modifyTraceState_480_; lean_object* v___f_481_; lean_object* v___x_482_; 
v_modifyTraceState_480_ = lean_ctor_get(v_inst_477_, 0);
lean_inc(v_modifyTraceState_480_);
lean_dec_ref(v_inst_477_);
v___f_481_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__0), 3, 2);
lean_closure_set(v___f_481_, 0, v_ref_478_);
lean_closure_set(v___f_481_, 1, v_msg_479_);
v___x_482_ = lean_apply_1(v_modifyTraceState_480_, v___f_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_msg_485_, lean_object* v_toBind_486_, lean_object* v_ref_487_){
_start:
{
lean_object* v___f_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___f_488_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__1), 3, 2);
lean_closure_set(v___f_488_, 0, v_inst_483_);
lean_closure_set(v___f_488_, 1, v_ref_487_);
v___x_489_ = lean_apply_1(v_inst_484_, v_msg_485_);
v___x_490_ = lean_apply_4(v_toBind_486_, lean_box(0), lean_box(0), v___x_489_, v___f_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_msg_495_){
_start:
{
lean_object* v_toBind_496_; lean_object* v_getRef_497_; lean_object* v___f_498_; lean_object* v___x_499_; 
v_toBind_496_ = lean_ctor_get(v_inst_491_, 1);
lean_inc_n(v_toBind_496_, 2);
lean_dec_ref(v_inst_491_);
v_getRef_497_ = lean_ctor_get(v_inst_493_, 0);
lean_inc(v_getRef_497_);
lean_dec_ref(v_inst_493_);
v___f_498_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__2), 5, 4);
lean_closure_set(v___f_498_, 0, v_inst_492_);
lean_closure_set(v___f_498_, 1, v_inst_494_);
lean_closure_set(v___f_498_, 2, v_msg_495_);
lean_closure_set(v___f_498_, 3, v_toBind_496_);
v___x_499_ = lean_apply_4(v_toBind_496_, lean_box(0), lean_box(0), v_getRef_497_, v___f_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object* v_m_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_msg_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_addRawTrace___redArg(v_inst_501_, v_inst_502_, v_inst_503_, v_inst_504_, v_msg_505_);
return v___x_506_;
}
}
static double _init_l_Lean_addTrace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_507_; double v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_float_of_nat(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object* v_cls_512_, lean_object* v_msg_513_, lean_object* v_ref_514_, lean_object* v_s_515_){
_start:
{
uint64_t v_tid_516_; lean_object* v_traces_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_533_; 
v_tid_516_ = lean_ctor_get_uint64(v_s_515_, sizeof(void*)*1);
v_traces_517_ = lean_ctor_get(v_s_515_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_s_515_);
if (v_isSharedCheck_533_ == 0)
{
v___x_519_ = v_s_515_;
v_isShared_520_ = v_isSharedCheck_533_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_traces_517_);
lean_dec(v_s_515_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_533_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; double v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_521_ = lean_box(0);
v___x_522_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
v___x_523_ = 0;
v___x_524_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_525_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_525_, 0, v_cls_512_);
lean_ctor_set(v___x_525_, 1, v___x_521_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
lean_ctor_set_float(v___x_525_, sizeof(void*)*3, v___x_522_);
lean_ctor_set_float(v___x_525_, sizeof(void*)*3 + 8, v___x_522_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*3 + 16, v___x_523_);
v___x_526_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
v___x_527_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v_msg_513_);
lean_ctor_set(v___x_527_, 2, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_ref_514_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = l_Lean_PersistentArray_push___redArg(v_traces_517_, v___x_528_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_529_);
v___x_531_ = v___x_519_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
lean_ctor_set_uint64(v_reuseFailAlloc_532_, sizeof(void*)*1, v_tid_516_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object* v_inst_534_, lean_object* v_cls_535_, lean_object* v_ref_536_, lean_object* v_msg_537_){
_start:
{
lean_object* v_modifyTraceState_538_; lean_object* v___f_539_; lean_object* v___x_540_; 
v_modifyTraceState_538_ = lean_ctor_get(v_inst_534_, 0);
lean_inc(v_modifyTraceState_538_);
lean_dec_ref(v_inst_534_);
v___f_539_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_539_, 0, v_cls_535_);
lean_closure_set(v___f_539_, 1, v_msg_537_);
lean_closure_set(v___f_539_, 2, v_ref_536_);
v___x_540_ = lean_apply_1(v_modifyTraceState_538_, v___f_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object* v_inst_541_, lean_object* v_cls_542_, lean_object* v_inst_543_, lean_object* v_msg_544_, lean_object* v_toBind_545_, lean_object* v_ref_546_){
_start:
{
lean_object* v___f_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___f_547_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__1), 4, 3);
lean_closure_set(v___f_547_, 0, v_inst_541_);
lean_closure_set(v___f_547_, 1, v_cls_542_);
lean_closure_set(v___f_547_, 2, v_ref_546_);
v___x_548_ = lean_apply_1(v_inst_543_, v_msg_544_);
v___x_549_ = lean_apply_4(v_toBind_545_, lean_box(0), lean_box(0), v___x_548_, v___f_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_cls_554_, lean_object* v_msg_555_){
_start:
{
lean_object* v_toBind_556_; lean_object* v_getRef_557_; lean_object* v___f_558_; lean_object* v___x_559_; 
v_toBind_556_ = lean_ctor_get(v_inst_550_, 1);
lean_inc_n(v_toBind_556_, 2);
lean_dec_ref(v_inst_550_);
v_getRef_557_ = lean_ctor_get(v_inst_552_, 0);
lean_inc(v_getRef_557_);
lean_dec_ref(v_inst_552_);
v___f_558_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__2), 6, 5);
lean_closure_set(v___f_558_, 0, v_inst_551_);
lean_closure_set(v___f_558_, 1, v_cls_554_);
lean_closure_set(v___f_558_, 2, v_inst_553_);
lean_closure_set(v___f_558_, 3, v_msg_555_);
lean_closure_set(v___f_558_, 4, v_toBind_556_);
v___x_559_ = lean_apply_4(v_toBind_556_, lean_box(0), lean_box(0), v_getRef_557_, v___f_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object* v_m_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_cls_565_, lean_object* v_msg_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_addTrace___redArg(v_inst_561_, v_inst_562_, v_inst_563_, v_inst_564_, v_cls_565_, v_msg_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0(lean_object* v_toPure_568_, lean_object* v_msg_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_cls_574_, uint8_t v_____do__lift_575_){
_start:
{
if (v_____do__lift_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_cls_574_);
lean_dec(v_inst_573_);
lean_dec_ref(v_inst_572_);
lean_dec_ref(v_inst_571_);
lean_dec_ref(v_inst_570_);
lean_dec_ref(v_msg_569_);
v___x_576_ = lean_box(0);
v___x_577_ = lean_apply_2(v_toPure_568_, lean_box(0), v___x_576_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_toPure_568_);
v___x_578_ = lean_box(0);
v___x_579_ = lean_apply_1(v_msg_569_, v___x_578_);
v___x_580_ = l_Lean_addTrace___redArg(v_inst_570_, v_inst_571_, v_inst_572_, v_inst_573_, v_cls_574_, v___x_579_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object* v_toPure_581_, lean_object* v_msg_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_cls_587_, lean_object* v_____do__lift_588_){
_start:
{
uint8_t v_____do__lift_126__boxed_589_; lean_object* v_res_590_; 
v_____do__lift_126__boxed_589_ = lean_unbox(v_____do__lift_588_);
v_res_590_ = l_Lean_trace___redArg___lam__0(v_toPure_581_, v_msg_582_, v_inst_583_, v_inst_584_, v_inst_585_, v_inst_586_, v_cls_587_, v_____do__lift_126__boxed_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_cls_596_, lean_object* v_msg_597_){
_start:
{
lean_object* v_toApplicative_598_; lean_object* v_toBind_599_; lean_object* v_getInheritedTraceOptions_600_; lean_object* v_toPure_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_toApplicative_598_ = lean_ctor_get(v_inst_591_, 0);
v_toBind_599_ = lean_ctor_get(v_inst_591_, 1);
lean_inc_n(v_toBind_599_, 3);
v_getInheritedTraceOptions_600_ = lean_ctor_get(v_inst_592_, 2);
lean_inc(v_getInheritedTraceOptions_600_);
v_toPure_601_ = lean_ctor_get(v_toApplicative_598_, 1);
lean_inc_n(v_toPure_601_, 2);
lean_inc(v_cls_596_);
v___f_602_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_602_, 0, v_toPure_601_);
lean_closure_set(v___f_602_, 1, v_msg_597_);
lean_closure_set(v___f_602_, 2, v_inst_591_);
lean_closure_set(v___f_602_, 3, v_inst_592_);
lean_closure_set(v___f_602_, 4, v_inst_593_);
lean_closure_set(v___f_602_, 5, v_inst_594_);
lean_closure_set(v___f_602_, 6, v_cls_596_);
v___f_603_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_603_, 0, v_inst_595_);
lean_closure_set(v___f_603_, 1, v_toPure_601_);
lean_closure_set(v___f_603_, 2, v_cls_596_);
lean_closure_set(v___f_603_, 3, v_toBind_599_);
v___x_604_ = lean_apply_4(v_toBind_599_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_600_, v___f_603_);
v___x_605_ = lean_apply_4(v_toBind_599_, lean_box(0), lean_box(0), v___x_604_, v___f_602_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace(lean_object* v_m_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_cls_612_, lean_object* v_msg_613_){
_start:
{
lean_object* v_toApplicative_614_; lean_object* v_toBind_615_; lean_object* v_getInheritedTraceOptions_616_; lean_object* v_toPure_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_toApplicative_614_ = lean_ctor_get(v_inst_607_, 0);
v_toBind_615_ = lean_ctor_get(v_inst_607_, 1);
lean_inc_n(v_toBind_615_, 3);
v_getInheritedTraceOptions_616_ = lean_ctor_get(v_inst_608_, 2);
lean_inc(v_getInheritedTraceOptions_616_);
v_toPure_617_ = lean_ctor_get(v_toApplicative_614_, 1);
lean_inc_n(v_toPure_617_, 2);
lean_inc(v_cls_612_);
v___f_618_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_618_, 0, v_toPure_617_);
lean_closure_set(v___f_618_, 1, v_msg_613_);
lean_closure_set(v___f_618_, 2, v_inst_607_);
lean_closure_set(v___f_618_, 3, v_inst_608_);
lean_closure_set(v___f_618_, 4, v_inst_609_);
lean_closure_set(v___f_618_, 5, v_inst_610_);
lean_closure_set(v___f_618_, 6, v_cls_612_);
v___f_619_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_619_, 0, v_inst_611_);
lean_closure_set(v___f_619_, 1, v_toPure_617_);
lean_closure_set(v___f_619_, 2, v_cls_612_);
lean_closure_set(v___f_619_, 3, v_toBind_615_);
v___x_620_ = lean_apply_4(v_toBind_615_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_616_, v___f_619_);
v___x_621_ = lean_apply_4(v_toBind_615_, lean_box(0), lean_box(0), v___x_620_, v___f_618_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_cls_626_, lean_object* v_msg_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_addTrace___redArg(v_inst_622_, v_inst_623_, v_inst_624_, v_inst_625_, v_cls_626_, v_msg_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1(lean_object* v_toPure_629_, lean_object* v_toBind_630_, lean_object* v_mkMsg_631_, lean_object* v___f_632_, uint8_t v_____do__lift_633_){
_start:
{
if (v_____do__lift_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec(v___f_632_);
lean_dec(v_mkMsg_631_);
lean_dec(v_toBind_630_);
v___x_634_ = lean_box(0);
v___x_635_ = lean_apply_2(v_toPure_629_, lean_box(0), v___x_634_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; 
lean_dec(v_toPure_629_);
v___x_636_ = lean_apply_4(v_toBind_630_, lean_box(0), lean_box(0), v_mkMsg_631_, v___f_632_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object* v_toPure_637_, lean_object* v_toBind_638_, lean_object* v_mkMsg_639_, lean_object* v___f_640_, lean_object* v_____do__lift_641_){
_start:
{
uint8_t v_____do__lift_132__boxed_642_; lean_object* v_res_643_; 
v_____do__lift_132__boxed_642_ = lean_unbox(v_____do__lift_641_);
v_res_643_ = l_Lean_traceM___redArg___lam__1(v_toPure_637_, v_toBind_638_, v_mkMsg_639_, v___f_640_, v_____do__lift_132__boxed_642_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_cls_649_, lean_object* v_mkMsg_650_){
_start:
{
lean_object* v_toApplicative_651_; lean_object* v_toBind_652_; lean_object* v_getInheritedTraceOptions_653_; lean_object* v_toPure_654_; lean_object* v___f_655_; lean_object* v___f_656_; lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_toApplicative_651_ = lean_ctor_get(v_inst_644_, 0);
v_toBind_652_ = lean_ctor_get(v_inst_644_, 1);
lean_inc_n(v_toBind_652_, 4);
v_getInheritedTraceOptions_653_ = lean_ctor_get(v_inst_645_, 2);
lean_inc(v_getInheritedTraceOptions_653_);
v_toPure_654_ = lean_ctor_get(v_toApplicative_651_, 1);
lean_inc_n(v_toPure_654_, 2);
lean_inc(v_cls_649_);
v___f_655_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_655_, 0, v_inst_644_);
lean_closure_set(v___f_655_, 1, v_inst_645_);
lean_closure_set(v___f_655_, 2, v_inst_646_);
lean_closure_set(v___f_655_, 3, v_inst_647_);
lean_closure_set(v___f_655_, 4, v_cls_649_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_656_, 0, v_toPure_654_);
lean_closure_set(v___f_656_, 1, v_toBind_652_);
lean_closure_set(v___f_656_, 2, v_mkMsg_650_);
lean_closure_set(v___f_656_, 3, v___f_655_);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_657_, 0, v_inst_648_);
lean_closure_set(v___f_657_, 1, v_toPure_654_);
lean_closure_set(v___f_657_, 2, v_cls_649_);
lean_closure_set(v___f_657_, 3, v_toBind_652_);
v___x_658_ = lean_apply_4(v_toBind_652_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_653_, v___f_657_);
v___x_659_ = lean_apply_4(v_toBind_652_, lean_box(0), lean_box(0), v___x_658_, v___f_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object* v_m_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_cls_666_, lean_object* v_mkMsg_667_){
_start:
{
lean_object* v_toApplicative_668_; lean_object* v_toBind_669_; lean_object* v_getInheritedTraceOptions_670_; lean_object* v_toPure_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___f_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_toApplicative_668_ = lean_ctor_get(v_inst_661_, 0);
v_toBind_669_ = lean_ctor_get(v_inst_661_, 1);
lean_inc_n(v_toBind_669_, 4);
v_getInheritedTraceOptions_670_ = lean_ctor_get(v_inst_662_, 2);
lean_inc(v_getInheritedTraceOptions_670_);
v_toPure_671_ = lean_ctor_get(v_toApplicative_668_, 1);
lean_inc_n(v_toPure_671_, 2);
lean_inc(v_cls_666_);
v___f_672_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_672_, 0, v_inst_661_);
lean_closure_set(v___f_672_, 1, v_inst_662_);
lean_closure_set(v___f_672_, 2, v_inst_663_);
lean_closure_set(v___f_672_, 3, v_inst_664_);
lean_closure_set(v___f_672_, 4, v_cls_666_);
v___f_673_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_673_, 0, v_toPure_671_);
lean_closure_set(v___f_673_, 1, v_toBind_669_);
lean_closure_set(v___f_673_, 2, v_mkMsg_667_);
lean_closure_set(v___f_673_, 3, v___f_672_);
v___f_674_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_674_, 0, v_inst_665_);
lean_closure_set(v___f_674_, 1, v_toPure_671_);
lean_closure_set(v___f_674_, 2, v_cls_666_);
lean_closure_set(v___f_674_, 3, v_toBind_669_);
v___x_675_ = lean_apply_4(v_toBind_669_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_670_, v___f_674_);
v___x_676_ = lean_apply_4(v_toBind_669_, lean_box(0), lean_box(0), v___x_675_, v___f_673_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object* v_x_677_){
_start:
{
lean_object* v_msg_678_; 
v_msg_678_ = lean_ctor_get(v_x_677_, 1);
lean_inc_ref(v_msg_678_);
return v_msg_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object* v_x_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_679_);
lean_dec_ref(v_x_679_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object* v_ref_681_, lean_object* v_msg_682_, lean_object* v_oldTraces_683_, lean_object* v_s_684_){
_start:
{
uint64_t v_tid_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_694_; 
v_tid_685_ = lean_ctor_get_uint64(v_s_684_, sizeof(void*)*1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_s_684_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v_s_684_, 0);
lean_dec(v_unused_695_);
v___x_687_ = v_s_684_;
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
else
{
lean_dec(v_s_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_ref_681_);
lean_ctor_set(v___x_689_, 1, v_msg_682_);
v___x_690_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_683_, v___x_689_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_690_);
v___x_692_ = v___x_687_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
lean_ctor_set_uint64(v_reuseFailAlloc_693_, sizeof(void*)*1, v_tid_685_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object* v_ref_696_, lean_object* v_oldTraces_697_, lean_object* v_modifyTraceState_698_, lean_object* v_msg_699_){
_start:
{
lean_object* v___f_700_; lean_object* v___x_701_; 
v___f_700_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0), 4, 3);
lean_closure_set(v___f_700_, 0, v_ref_696_);
lean_closure_set(v___f_700_, 1, v_msg_699_);
lean_closure_set(v___f_700_, 2, v_oldTraces_697_);
v___x_701_ = lean_apply_1(v_modifyTraceState_698_, v___f_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object* v___f_721_, lean_object* v_data_722_, lean_object* v_msg_723_, lean_object* v_inst_724_, lean_object* v_toBind_725_, lean_object* v___f_726_, lean_object* v_____do__lift_727_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; size_t v_sz_730_; size_t v___x_731_; lean_object* v___x_732_; lean_object* v_msg_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_728_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_727_);
v___x_729_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v_sz_730_ = lean_array_size(v___x_728_);
v___x_731_ = ((size_t)0ULL);
v___x_732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_729_, v___f_721_, v_sz_730_, v___x_731_, v___x_728_);
v_msg_733_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_733_, 0, v_data_722_);
lean_ctor_set(v_msg_733_, 1, v_msg_723_);
lean_ctor_set(v_msg_733_, 2, v___x_732_);
v___x_734_ = lean_apply_1(v_inst_724_, v_msg_733_);
v___x_735_ = lean_apply_4(v_toBind_725_, lean_box(0), lean_box(0), v___x_734_, v___f_726_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object* v___f_736_, lean_object* v_data_737_, lean_object* v_msg_738_, lean_object* v_inst_739_, lean_object* v_toBind_740_, lean_object* v___f_741_, lean_object* v_____do__lift_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(v___f_736_, v_data_737_, v_msg_738_, v_inst_739_, v_toBind_740_, v___f_741_, v_____do__lift_742_);
lean_dec_ref(v_____do__lift_742_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object* v_ref_744_, lean_object* v_withRef_745_, lean_object* v___x_746_, lean_object* v_oldRef_747_){
_start:
{
lean_object* v_ref_748_; lean_object* v___x_749_; 
v_ref_748_ = l_Lean_replaceRef(v_ref_744_, v_oldRef_747_);
v___x_749_ = lean_apply_3(v_withRef_745_, lean_box(0), v_ref_748_, v___x_746_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object* v_ref_750_, lean_object* v_withRef_751_, lean_object* v___x_752_, lean_object* v_oldRef_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(v_ref_750_, v_withRef_751_, v___x_752_, v_oldRef_753_);
lean_dec(v_oldRef_753_);
lean_dec(v_ref_750_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_oldTraces_760_, lean_object* v_data_761_, lean_object* v_ref_762_, lean_object* v_msg_763_){
_start:
{
lean_object* v_toApplicative_764_; lean_object* v_toBind_765_; lean_object* v_modifyTraceState_766_; lean_object* v_getTraceState_767_; lean_object* v_toPure_768_; lean_object* v_getRef_769_; lean_object* v_withRef_770_; lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___f_777_; lean_object* v___x_778_; 
v_toApplicative_764_ = lean_ctor_get(v_inst_756_, 0);
lean_inc_ref(v_toApplicative_764_);
v_toBind_765_ = lean_ctor_get(v_inst_756_, 1);
lean_inc_n(v_toBind_765_, 4);
lean_dec_ref(v_inst_756_);
v_modifyTraceState_766_ = lean_ctor_get(v_inst_757_, 0);
lean_inc(v_modifyTraceState_766_);
v_getTraceState_767_ = lean_ctor_get(v_inst_757_, 1);
lean_inc(v_getTraceState_767_);
lean_dec_ref(v_inst_757_);
v_toPure_768_ = lean_ctor_get(v_toApplicative_764_, 1);
lean_inc(v_toPure_768_);
lean_dec_ref(v_toApplicative_764_);
v_getRef_769_ = lean_ctor_get(v_inst_758_, 0);
lean_inc(v_getRef_769_);
v_withRef_770_ = lean_ctor_get(v_inst_758_, 1);
lean_inc(v_withRef_770_);
lean_dec_ref(v_inst_758_);
v___f_771_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_771_, 0, v_toPure_768_);
v___x_772_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v_getTraceState_767_, v___f_771_);
v___f_773_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0));
lean_inc(v_ref_762_);
v___f_774_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2), 4, 3);
lean_closure_set(v___f_774_, 0, v_ref_762_);
lean_closure_set(v___f_774_, 1, v_oldTraces_760_);
lean_closure_set(v___f_774_, 2, v_modifyTraceState_766_);
v___f_775_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_775_, 0, v___f_773_);
lean_closure_set(v___f_775_, 1, v_data_761_);
lean_closure_set(v___f_775_, 2, v_msg_763_);
lean_closure_set(v___f_775_, 3, v_inst_759_);
lean_closure_set(v___f_775_, 4, v_toBind_765_);
lean_closure_set(v___f_775_, 5, v___f_774_);
v___x_776_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v___x_772_, v___f_775_);
v___f_777_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_777_, 0, v_ref_762_);
lean_closure_set(v___f_777_, 1, v_withRef_770_);
lean_closure_set(v___f_777_, 2, v___x_776_);
v___x_778_ = lean_apply_4(v_toBind_765_, lean_box(0), lean_box(0), v_getRef_769_, v___f_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object* v_m_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_oldTraces_784_, lean_object* v_data_785_, lean_object* v_ref_786_, lean_object* v_msg_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_780_, v_inst_781_, v_inst_782_, v_inst_783_, v_oldTraces_784_, v_data_785_, v_ref_786_, v_msg_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object* v_name_789_, lean_object* v_decl_790_, lean_object* v_ref_791_){
_start:
{
lean_object* v_defValue_793_; lean_object* v_descr_794_; lean_object* v_deprecation_x3f_795_; lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_defValue_793_ = lean_ctor_get(v_decl_790_, 0);
v_descr_794_ = lean_ctor_get(v_decl_790_, 1);
v_deprecation_x3f_795_ = lean_ctor_get(v_decl_790_, 2);
v___x_796_ = lean_alloc_ctor(1, 0, 1);
v___x_797_ = lean_unbox(v_defValue_793_);
lean_ctor_set_uint8(v___x_796_, 0, v___x_797_);
lean_inc(v_deprecation_x3f_795_);
lean_inc_ref(v_descr_794_);
lean_inc_n(v_name_789_, 2);
v___x_798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_798_, 0, v_name_789_);
lean_ctor_set(v___x_798_, 1, v_ref_791_);
lean_ctor_set(v___x_798_, 2, v___x_796_);
lean_ctor_set(v___x_798_, 3, v_descr_794_);
lean_ctor_set(v___x_798_, 4, v_deprecation_x3f_795_);
v___x_799_ = lean_register_option(v_name_789_, v___x_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_807_; 
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v___x_799_, 0);
lean_dec(v_unused_808_);
v___x_801_ = v___x_799_;
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
else
{
lean_dec(v___x_799_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
lean_inc(v_defValue_793_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_name_789_);
lean_ctor_set(v___x_803_, 1, v_defValue_793_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec(v_name_789_);
v_a_809_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_799_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_799_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_817_, lean_object* v_decl_818_, lean_object* v_ref_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_817_, v_decl_818_, v_ref_819_);
lean_dec_ref(v_decl_818_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_838_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_839_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_840_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_837_, v___x_838_, v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object* v_name_843_, lean_object* v_decl_844_, lean_object* v_ref_845_){
_start:
{
lean_object* v_defValue_847_; lean_object* v_descr_848_; lean_object* v_deprecation_x3f_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_defValue_847_ = lean_ctor_get(v_decl_844_, 0);
v_descr_848_ = lean_ctor_get(v_decl_844_, 1);
v_deprecation_x3f_849_ = lean_ctor_get(v_decl_844_, 2);
lean_inc(v_defValue_847_);
v___x_850_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_850_, 0, v_defValue_847_);
lean_inc(v_deprecation_x3f_849_);
lean_inc_ref(v_descr_848_);
lean_inc_n(v_name_843_, 2);
v___x_851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_851_, 0, v_name_843_);
lean_ctor_set(v___x_851_, 1, v_ref_845_);
lean_ctor_set(v___x_851_, 2, v___x_850_);
lean_ctor_set(v___x_851_, 3, v_descr_848_);
lean_ctor_set(v___x_851_, 4, v_deprecation_x3f_849_);
v___x_852_ = lean_register_option(v_name_843_, v___x_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_860_; 
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v___x_852_, 0);
lean_dec(v_unused_861_);
v___x_854_ = v___x_852_;
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
else
{
lean_dec(v___x_852_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
lean_inc(v_defValue_847_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_name_843_);
lean_ctor_set(v___x_856_, 1, v_defValue_847_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_856_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_name_843_);
v_a_862_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_852_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_852_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
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
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_870_, lean_object* v_decl_871_, lean_object* v_ref_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_870_, v_decl_871_, v_ref_872_);
lean_dec_ref(v_decl_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_891_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_892_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_893_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_894_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_891_, v___x_892_, v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_914_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_915_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_916_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_917_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_914_, v___x_915_, v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object* v_name_920_, lean_object* v_decl_921_, lean_object* v_ref_922_){
_start:
{
lean_object* v_defValue_924_; lean_object* v_descr_925_; lean_object* v_deprecation_x3f_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_defValue_924_ = lean_ctor_get(v_decl_921_, 0);
v_descr_925_ = lean_ctor_get(v_decl_921_, 1);
v_deprecation_x3f_926_ = lean_ctor_get(v_decl_921_, 2);
lean_inc(v_defValue_924_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v_defValue_924_);
lean_inc(v_deprecation_x3f_926_);
lean_inc_ref(v_descr_925_);
lean_inc_n(v_name_920_, 2);
v___x_928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_928_, 0, v_name_920_);
lean_ctor_set(v___x_928_, 1, v_ref_922_);
lean_ctor_set(v___x_928_, 2, v___x_927_);
lean_ctor_set(v___x_928_, 3, v_descr_925_);
lean_ctor_set(v___x_928_, 4, v_deprecation_x3f_926_);
v___x_929_ = lean_register_option(v_name_920_, v___x_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_937_; 
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v___x_929_, 0);
lean_dec(v_unused_938_);
v___x_931_ = v___x_929_;
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
else
{
lean_dec(v___x_929_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
lean_inc(v_defValue_924_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_name_920_);
lean_ctor_set(v___x_933_, 1, v_defValue_924_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_933_);
v___x_935_ = v___x_931_;
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
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec(v_name_920_);
v_a_939_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_929_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_929_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
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
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_947_, lean_object* v_decl_948_, lean_object* v_ref_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_947_, v_decl_948_, v_ref_949_);
lean_dec_ref(v_decl_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_969_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_970_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_971_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_968_, v___x_969_, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_991_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_992_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_993_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_994_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_991_, v___x_992_, v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4____boxed(lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
return v_res_996_;
}
}
LEAN_EXPORT uint8_t l_Lean_trace_profiler_isExporting(lean_object* v_opts_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_998_ = l_Lean_KVMap_instValueBool;
v___x_999_ = l_Lean_KVMap_instValueString;
v___x_1000_ = l_Lean_trace_profiler_output;
v___x_1001_ = l_Lean_Option_get_x3f___redArg(v___x_999_, v_opts_997_, v___x_1000_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1002_ = l_Lean_trace_profiler_serve;
v___x_1003_ = l_Lean_Option_get___redArg(v___x_998_, v_opts_997_, v___x_1002_);
v___x_1004_ = lean_unbox(v___x_1003_);
lean_dec(v___x_1003_);
return v___x_1004_;
}
else
{
uint8_t v___x_1005_; 
lean_dec_ref_known(v___x_1001_, 1);
v___x_1005_ = 1;
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_isExporting___boxed(lean_object* v_opts_1006_){
_start:
{
uint8_t v_res_1007_; lean_object* v_r_1008_; 
v_res_1007_ = l_Lean_trace_profiler_isExporting(v_opts_1006_);
lean_dec_ref(v_opts_1006_);
v_r_1008_ = lean_box(v_res_1007_);
return v_r_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1029_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1030_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1031_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_1028_, v___x_1029_, v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
return v_res_1033_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1034_; double v___x_1035_; 
v___x_1034_ = lean_unsigned_to_nat(1000000000u);
v___x_1035_ = lean_float_of_nat(v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object* v_start_1036_, lean_object* v_a_1037_, lean_object* v_toPure_1038_, lean_object* v_stop_1039_){
_start:
{
double v___x_1040_; double v___x_1041_; double v___x_1042_; double v___x_1043_; double v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1040_ = lean_float_of_nat(v_start_1036_);
v___x_1041_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1042_ = lean_float_div(v___x_1040_, v___x_1041_);
v___x_1043_ = lean_float_of_nat(v_stop_1039_);
v___x_1044_ = lean_float_div(v___x_1043_, v___x_1041_);
v___x_1045_ = lean_box_float(v___x_1042_);
v___x_1046_ = lean_box_float(v___x_1044_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_a_1037_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_apply_2(v_toPure_1038_, lean_box(0), v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object* v_start_1050_, lean_object* v_toPure_1051_, lean_object* v_toBind_1052_, lean_object* v___x_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___f_1055_; lean_object* v___x_1056_; 
v___f_1055_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1055_, 0, v_start_1050_);
lean_closure_set(v___f_1055_, 1, v_a_1054_);
lean_closure_set(v___f_1055_, 2, v_toPure_1051_);
v___x_1056_ = lean_apply_4(v_toBind_1052_, lean_box(0), lean_box(0), v___x_1053_, v___f_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object* v_toPure_1057_, lean_object* v_toBind_1058_, lean_object* v___x_1059_, lean_object* v_act_1060_, lean_object* v_start_1061_){
_start:
{
lean_object* v___f_1062_; lean_object* v___x_1063_; 
lean_inc(v_toBind_1058_);
v___f_1062_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1062_, 0, v_start_1061_);
lean_closure_set(v___f_1062_, 1, v_toPure_1057_);
lean_closure_set(v___f_1062_, 2, v_toBind_1058_);
lean_closure_set(v___f_1062_, 3, v___x_1059_);
v___x_1063_ = lean_apply_4(v_toBind_1058_, lean_box(0), lean_box(0), v_act_1060_, v___f_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object* v_start_1064_, lean_object* v_a_1065_, lean_object* v_toPure_1066_, lean_object* v_stop_1067_){
_start:
{
double v___x_1068_; double v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1068_ = lean_float_of_nat(v_start_1064_);
v___x_1069_ = lean_float_of_nat(v_stop_1067_);
v___x_1070_ = lean_box_float(v___x_1068_);
v___x_1071_ = lean_box_float(v___x_1069_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_a_1065_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_apply_2(v_toPure_1066_, lean_box(0), v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object* v_start_1075_, lean_object* v_toPure_1076_, lean_object* v_toBind_1077_, lean_object* v___x_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v___f_1080_; lean_object* v___x_1081_; 
v___f_1080_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1080_, 0, v_start_1075_);
lean_closure_set(v___f_1080_, 1, v_a_1079_);
lean_closure_set(v___f_1080_, 2, v_toPure_1076_);
v___x_1081_ = lean_apply_4(v_toBind_1077_, lean_box(0), lean_box(0), v___x_1078_, v___f_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object* v_toPure_1082_, lean_object* v_toBind_1083_, lean_object* v___x_1084_, lean_object* v_act_1085_, lean_object* v_start_1086_){
_start:
{
lean_object* v___f_1087_; lean_object* v___x_1088_; 
lean_inc(v_toBind_1083_);
v___f_1087_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1087_, 0, v_start_1086_);
lean_closure_set(v___f_1087_, 1, v_toPure_1082_);
lean_closure_set(v___f_1087_, 2, v_toBind_1083_);
lean_closure_set(v___f_1087_, 3, v___x_1084_);
v___x_1088_ = lean_apply_4(v_toBind_1083_, lean_box(0), lean_box(0), v_act_1085_, v___f_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_opts_1093_, lean_object* v_act_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v_toApplicative_1096_; lean_object* v_toBind_1097_; lean_object* v_toPure_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1095_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1096_ = lean_ctor_get(v_inst_1091_, 0);
lean_inc_ref(v_toApplicative_1096_);
v_toBind_1097_ = lean_ctor_get(v_inst_1091_, 1);
lean_inc(v_toBind_1097_);
lean_dec_ref(v_inst_1091_);
v_toPure_1098_ = lean_ctor_get(v_toApplicative_1096_, 1);
lean_inc(v_toPure_1098_);
lean_dec_ref(v_toApplicative_1096_);
v___x_1099_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1100_ = l_Lean_Option_get___redArg(v___x_1095_, v_opts_1093_, v___x_1099_);
v___x_1101_ = lean_unbox(v___x_1100_);
lean_dec(v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; 
v___x_1102_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1103_ = lean_apply_2(v_inst_1092_, lean_box(0), v___x_1102_);
lean_inc(v___x_1103_);
lean_inc(v_toBind_1097_);
v___f_1104_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1104_, 0, v_toPure_1098_);
lean_closure_set(v___f_1104_, 1, v_toBind_1097_);
lean_closure_set(v___f_1104_, 2, v___x_1103_);
lean_closure_set(v___f_1104_, 3, v_act_1094_);
v___x_1105_ = lean_apply_4(v_toBind_1097_, lean_box(0), lean_box(0), v___x_1103_, v___f_1104_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; 
v___x_1106_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1107_ = lean_apply_2(v_inst_1092_, lean_box(0), v___x_1106_);
lean_inc(v___x_1107_);
lean_inc(v_toBind_1097_);
v___f_1108_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1108_, 0, v_toPure_1098_);
lean_closure_set(v___f_1108_, 1, v_toBind_1097_);
lean_closure_set(v___f_1108_, 2, v___x_1107_);
lean_closure_set(v___f_1108_, 3, v_act_1094_);
v___x_1109_ = lean_apply_4(v_toBind_1097_, lean_box(0), lean_box(0), v___x_1107_, v___f_1108_);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object* v_inst_1110_, lean_object* v_inst_1111_, lean_object* v_opts_1112_, lean_object* v_act_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(v_inst_1110_, v_inst_1111_, v_opts_1112_, v_act_1113_);
lean_dec_ref(v_opts_1112_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object* v_00_u03b1_1115_, lean_object* v_m_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_opts_1119_, lean_object* v_act_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v_toApplicative_1122_; lean_object* v_toBind_1123_; lean_object* v_toPure_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1121_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1122_ = lean_ctor_get(v_inst_1117_, 0);
lean_inc_ref(v_toApplicative_1122_);
v_toBind_1123_ = lean_ctor_get(v_inst_1117_, 1);
lean_inc(v_toBind_1123_);
lean_dec_ref(v_inst_1117_);
v_toPure_1124_ = lean_ctor_get(v_toApplicative_1122_, 1);
lean_inc(v_toPure_1124_);
lean_dec_ref(v_toApplicative_1122_);
v___x_1125_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1126_ = l_Lean_Option_get___redArg(v___x_1121_, v_opts_1119_, v___x_1125_);
v___x_1127_ = lean_unbox(v___x_1126_);
lean_dec(v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1129_ = lean_apply_2(v_inst_1118_, lean_box(0), v___x_1128_);
lean_inc(v___x_1129_);
lean_inc(v_toBind_1123_);
v___f_1130_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1130_, 0, v_toPure_1124_);
lean_closure_set(v___f_1130_, 1, v_toBind_1123_);
lean_closure_set(v___f_1130_, 2, v___x_1129_);
lean_closure_set(v___f_1130_, 3, v_act_1120_);
v___x_1131_ = lean_apply_4(v_toBind_1123_, lean_box(0), lean_box(0), v___x_1129_, v___f_1130_);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; 
v___x_1132_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1133_ = lean_apply_2(v_inst_1118_, lean_box(0), v___x_1132_);
lean_inc(v___x_1133_);
lean_inc(v_toBind_1123_);
v___f_1134_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1134_, 0, v_toPure_1124_);
lean_closure_set(v___f_1134_, 1, v_toBind_1123_);
lean_closure_set(v___f_1134_, 2, v___x_1133_);
lean_closure_set(v___f_1134_, 3, v_act_1120_);
v___x_1135_ = lean_apply_4(v_toBind_1123_, lean_box(0), lean_box(0), v___x_1133_, v___f_1134_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_m_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_opts_1140_, lean_object* v_act_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(v_00_u03b1_1136_, v_m_1137_, v_inst_1138_, v_inst_1139_, v_opts_1140_, v_act_1141_);
lean_dec_ref(v_opts_1140_);
return v_res_1142_;
}
}
static double _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0(void){
_start:
{
lean_object* v___x_1143_; double v___x_1144_; 
v___x_1143_ = lean_unsigned_to_nat(1000u);
v___x_1144_ = lean_float_of_nat(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object* v_o_1145_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1146_ = l_Lean_KVMap_instValueBool;
v___x_1147_ = l_Lean_KVMap_instValueNat;
v___x_1148_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1149_ = l_Lean_Option_get___redArg(v___x_1146_, v_o_1145_, v___x_1148_);
v___x_1150_ = lean_unbox(v___x_1149_);
lean_dec(v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; double v___x_1153_; double v___x_1154_; double v___x_1155_; 
v___x_1151_ = l_Lean_trace_profiler_threshold;
v___x_1152_ = l_Lean_Option_get___redArg(v___x_1147_, v_o_1145_, v___x_1151_);
v___x_1153_ = lean_float_of_nat(v___x_1152_);
v___x_1154_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1155_ = lean_float_div(v___x_1153_, v___x_1154_);
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; double v___x_1158_; 
v___x_1156_ = l_Lean_trace_profiler_threshold;
v___x_1157_ = l_Lean_Option_get___redArg(v___x_1147_, v_o_1145_, v___x_1156_);
v___x_1158_ = lean_float_of_nat(v___x_1157_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object* v_o_1159_){
_start:
{
double v_res_1160_; lean_object* v_r_1161_; 
v_res_1160_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1159_);
lean_dec_ref(v_o_1159_);
v_r_1161_ = lean_box_float(v_res_1160_);
return v_r_1161_;
}
}
static lean_object* _init_l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0(void){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_instMonadExceptOfEIO___redArg();
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO___redArg(){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0, &l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO___redArg___boxed(lean_object* v___dummy_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_instMonadAlwaysExceptEIO___redArg();
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object* v_00_u03b5_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0, &l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object* v_inst_1169_, lean_object* v_always_1170_){
_start:
{
lean_object* v___f_1171_; lean_object* v___f_1172_; lean_object* v___x_1173_; 
lean_inc_ref(v_always_1170_);
v___f_1171_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1171_, 0, v_always_1170_);
lean_closure_set(v___f_1171_, 1, v_inst_1169_);
v___f_1172_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_1172_, 0, v_always_1170_);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___f_1171_);
lean_ctor_set(v___x_1173_, 1, v___f_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object* v_m_1174_, lean_object* v_inst_1175_, lean_object* v_00_u03b5_1176_, lean_object* v_00_u03c3_1177_, lean_object* v_always_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_1175_, v_always_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object* v_always_1180_){
_start:
{
lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; 
lean_inc_ref(v_always_1180_);
v___f_1181_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1181_, 0, v_always_1180_);
v___f_1182_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1182_, 0, v_always_1180_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___f_1181_);
lean_ctor_set(v___x_1183_, 1, v___f_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object* v_m_1184_, lean_object* v_00_u03b5_1185_, lean_object* v_00_u03c9_1186_, lean_object* v_00_u03c3_1187_, lean_object* v_always_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object* v_always_1190_){
_start:
{
lean_object* v___f_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; 
lean_inc_ref(v_always_1190_);
v___f_1191_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1191_, 0, v_always_1190_);
v___f_1192_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1192_, 0, v_always_1190_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___f_1191_);
lean_ctor_set(v___x_1193_, 1, v___f_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object* v_m_1194_, lean_object* v_00_u03b5_1195_, lean_object* v_00_u03c1_1196_, lean_object* v_always_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object* v_always_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1200_, v_inst_1201_, v_inst_1202_, v_always_1199_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object* v_00_u03b1_1204_, lean_object* v_m_1205_, lean_object* v_00_u03b5_1206_, lean_object* v_00_u03c9_1207_, lean_object* v_00_u03b2_1208_, lean_object* v_always_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1210_, v_inst_1211_, v_inst_1212_, v_always_1209_);
return v___x_1213_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___redArg___lam__0(lean_object* v_x_1220_){
_start:
{
if (lean_obj_tag(v_x_1220_) == 0)
{
uint8_t v___x_1221_; 
v___x_1221_ = 2;
return v___x_1221_;
}
else
{
lean_object* v_a_1222_; uint8_t v___x_1223_; 
v_a_1222_ = lean_ctor_get(v_x_1220_, 0);
v___x_1223_ = lean_unbox(v_a_1222_);
if (v___x_1223_ == 0)
{
uint8_t v___x_1224_; 
v___x_1224_ = 1;
return v___x_1224_;
}
else
{
uint8_t v___x_1225_; 
v___x_1225_ = 0;
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___redArg___lam__0___boxed(lean_object* v_x_1226_){
_start:
{
uint8_t v_res_1227_; lean_object* v_r_1228_; 
v_res_1227_ = l_Lean_instExceptToTraceResultBool___redArg___lam__0(v_x_1226_);
lean_dec_ref(v_x_1226_);
v_r_1228_ = lean_box(v_res_1227_);
return v_r_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___redArg(){
_start:
{
lean_object* v___f_1231_; 
v___f_1231_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___redArg___closed__0));
return v___f_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___redArg___boxed(lean_object* v___dummy_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_instExceptToTraceResultBool___redArg();
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object* v_00_u03b5_1234_){
_start:
{
lean_object* v___f_1235_; 
v___f_1235_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___redArg___closed__0));
return v___f_1235_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___redArg___lam__0(lean_object* v_x_1236_){
_start:
{
if (lean_obj_tag(v_x_1236_) == 0)
{
uint8_t v___x_1237_; 
v___x_1237_ = 2;
return v___x_1237_;
}
else
{
lean_object* v_a_1238_; 
v_a_1238_ = lean_ctor_get(v_x_1236_, 0);
if (lean_obj_tag(v_a_1238_) == 0)
{
uint8_t v___x_1239_; 
v___x_1239_ = 1;
return v___x_1239_;
}
else
{
uint8_t v___x_1240_; 
v___x_1240_ = 0;
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___redArg___lam__0___boxed(lean_object* v_x_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Lean_instExceptToTraceResultOption___redArg___lam__0(v_x_1241_);
lean_dec_ref(v_x_1241_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___redArg(){
_start:
{
lean_object* v___f_1246_; 
v___f_1246_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___redArg___closed__0));
return v___f_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___redArg___boxed(lean_object* v___dummy_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_instExceptToTraceResultOption___redArg();
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object* v_00_u03b1_1249_, lean_object* v_00_u03b5_1250_){
_start:
{
lean_object* v___f_1251_; 
v___f_1251_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___redArg___closed__0));
return v___f_1251_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultExpr___redArg___lam__0(lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
uint8_t v___x_1253_; 
v___x_1253_ = 2;
return v___x_1253_;
}
else
{
lean_object* v_a_1254_; uint8_t v___x_1255_; 
v_a_1254_ = lean_ctor_get(v_x_1252_, 0);
v___x_1255_ = l_Lean_Expr_hasSyntheticSorry(v_a_1254_);
if (v___x_1255_ == 0)
{
uint8_t v___x_1256_; 
v___x_1256_ = 0;
return v___x_1256_;
}
else
{
uint8_t v___x_1257_; 
v___x_1257_ = 1;
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___redArg___lam__0___boxed(lean_object* v_x_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Lean_instExceptToTraceResultExpr___redArg___lam__0(v_x_1258_);
lean_dec_ref(v_x_1258_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___redArg(){
_start:
{
lean_object* v___f_1263_; 
v___f_1263_ = ((lean_object*)(l_Lean_instExceptToTraceResultExpr___redArg___closed__0));
return v___f_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___redArg___boxed(lean_object* v___dummy_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_instExceptToTraceResultExpr___redArg();
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr(lean_object* v_00_u03b5_1266_){
_start:
{
lean_object* v___f_1267_; 
v___f_1267_ = ((lean_object*)(l_Lean_instExceptToTraceResultExpr___redArg___closed__0));
return v___f_1267_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___redArg___lam__0(lean_object* v_x_1268_){
_start:
{
if (lean_obj_tag(v_x_1268_) == 0)
{
uint8_t v___x_1269_; 
v___x_1269_ = 2;
return v___x_1269_;
}
else
{
uint8_t v___x_1270_; 
v___x_1270_ = 0;
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___redArg___lam__0___boxed(lean_object* v_x_1271_){
_start:
{
uint8_t v_res_1272_; lean_object* v_r_1273_; 
v_res_1272_ = l_Lean_instExceptToTraceResult___redArg___lam__0(v_x_1271_);
lean_dec_ref(v_x_1271_);
v_r_1273_ = lean_box(v_res_1272_);
return v_r_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___redArg(){
_start:
{
lean_object* v___f_1276_; 
v___f_1276_ = ((lean_object*)(l_Lean_instExceptToTraceResult___redArg___closed__0));
return v___f_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___redArg___boxed(lean_object* v___dummy_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_instExceptToTraceResult___redArg();
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object* v_00_u03b1_1279_, lean_object* v_00_u03b5_1280_){
_start:
{
lean_object* v___f_1281_; 
v___f_1281_ = ((lean_object*)(l_Lean_instExceptToTraceResult___redArg___closed__0));
return v___f_1281_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___redArg(lean_object* v_inst_1282_, lean_object* v_e_1283_){
_start:
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = lean_apply_1(v_inst_1282_, v_e_1283_);
v___x_1285_ = lean_unbox(v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___redArg___boxed(lean_object* v_inst_1286_, lean_object* v_e_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Lean_Except_toTraceResult___redArg(v_inst_1286_, v_e_1287_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult(lean_object* v_00_u03b1_1290_, lean_object* v_00_u03b5_1291_, lean_object* v_inst_1292_, lean_object* v_e_1293_){
_start:
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = lean_apply_1(v_inst_1292_, v_e_1293_);
v___x_1295_ = lean_unbox(v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___boxed(lean_object* v_00_u03b1_1296_, lean_object* v_00_u03b5_1297_, lean_object* v_inst_1298_, lean_object* v_e_1299_){
_start:
{
uint8_t v_res_1300_; lean_object* v_r_1301_; 
v_res_1300_ = l_Lean_Except_toTraceResult(v_00_u03b1_1296_, v_00_u03b5_1297_, v_inst_1298_, v_e_1299_);
v_r_1301_ = lean_box(v_res_1300_);
return v_r_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object* v_oldTraces_1302_, lean_object* v_s_1303_){
_start:
{
uint64_t v_tid_1304_; lean_object* v_traces_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1313_; 
v_tid_1304_ = lean_ctor_get_uint64(v_s_1303_, sizeof(void*)*1);
v_traces_1305_ = lean_ctor_get(v_s_1303_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_s_1303_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1307_ = v_s_1303_;
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_traces_1305_);
lean_dec(v_s_1303_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1313_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1309_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1302_, v_traces_1305_);
lean_dec_ref(v_traces_1305_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1309_);
v___x_1311_ = v___x_1307_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
lean_ctor_set_uint64(v_reuseFailAlloc_1312_, sizeof(void*)*1, v_tid_1304_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__0));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object* v_toPure_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1);
v___x_1320_ = lean_apply_2(v_toPure_1317_, lean_box(0), v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___boxed(lean_object* v_toPure_1321_, lean_object* v_x_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(v_toPure_1321_, v_x_1322_);
lean_dec(v_x_1322_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object* v_inst_1324_, lean_object* v___x_1325_, lean_object* v_fst_1326_, lean_object* v_____r_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_MonadExcept_ofExcept___redArg(v_inst_1324_, v___x_1325_, v_fst_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_oldTraces_1333_, lean_object* v_ref_1334_, lean_object* v_toBind_1335_, lean_object* v___f_1336_, lean_object* v_inst_1337_, lean_object* v_fst_1338_, lean_object* v_cls_1339_, uint8_t v_collapsed_1340_, lean_object* v_tag_1341_, lean_object* v___x_1342_, double v_fst_1343_, double v_snd_1344_, lean_object* v_m_1345_){
_start:
{
lean_object* v_data_1347_; lean_object* v_result_1350_; lean_object* v___x_1351_; double v___x_1352_; lean_object* v_data_1353_; uint8_t v___x_1354_; 
v_result_1350_ = lean_apply_1(v_inst_1337_, v_fst_1338_);
v___x_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1351_, 0, v_result_1350_);
v___x_1352_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_1341_);
lean_inc_ref(v___x_1351_);
lean_inc(v_cls_1339_);
v_data_1353_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1353_, 0, v_cls_1339_);
lean_ctor_set(v_data_1353_, 1, v___x_1351_);
lean_ctor_set(v_data_1353_, 2, v_tag_1341_);
lean_ctor_set_float(v_data_1353_, sizeof(void*)*3, v___x_1352_);
lean_ctor_set_float(v_data_1353_, sizeof(void*)*3 + 8, v___x_1352_);
lean_ctor_set_uint8(v_data_1353_, sizeof(void*)*3 + 16, v_collapsed_1340_);
v___x_1354_ = lean_unbox(v___x_1342_);
if (v___x_1354_ == 0)
{
lean_dec_ref_known(v___x_1351_, 1);
lean_dec_ref(v_tag_1341_);
lean_dec(v_cls_1339_);
v_data_1347_ = v_data_1353_;
goto v___jp_1346_;
}
else
{
lean_object* v_data_1355_; 
lean_dec_ref_known(v_data_1353_, 3);
v_data_1355_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1355_, 0, v_cls_1339_);
lean_ctor_set(v_data_1355_, 1, v___x_1351_);
lean_ctor_set(v_data_1355_, 2, v_tag_1341_);
lean_ctor_set_float(v_data_1355_, sizeof(void*)*3, v_fst_1343_);
lean_ctor_set_float(v_data_1355_, sizeof(void*)*3 + 8, v_snd_1344_);
lean_ctor_set_uint8(v_data_1355_, sizeof(void*)*3 + 16, v_collapsed_1340_);
v_data_1347_ = v_data_1355_;
goto v___jp_1346_;
}
v___jp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_1329_, v_inst_1330_, v_inst_1331_, v_inst_1332_, v_oldTraces_1333_, v_data_1347_, v_ref_1334_, v_m_1345_);
v___x_1349_ = lean_apply_4(v_toBind_1335_, lean_box(0), lean_box(0), v___x_1348_, v___f_1336_);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_1356_ = _args[0];
lean_object* v_inst_1357_ = _args[1];
lean_object* v_inst_1358_ = _args[2];
lean_object* v_inst_1359_ = _args[3];
lean_object* v_oldTraces_1360_ = _args[4];
lean_object* v_ref_1361_ = _args[5];
lean_object* v_toBind_1362_ = _args[6];
lean_object* v___f_1363_ = _args[7];
lean_object* v_inst_1364_ = _args[8];
lean_object* v_fst_1365_ = _args[9];
lean_object* v_cls_1366_ = _args[10];
lean_object* v_collapsed_1367_ = _args[11];
lean_object* v_tag_1368_ = _args[12];
lean_object* v___x_1369_ = _args[13];
lean_object* v_fst_1370_ = _args[14];
lean_object* v_snd_1371_ = _args[15];
lean_object* v_m_1372_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1373_; double v_fst_453__boxed_1374_; double v_snd_454__boxed_1375_; lean_object* v_res_1376_; 
v_collapsed_boxed_1373_ = lean_unbox(v_collapsed_1367_);
v_fst_453__boxed_1374_ = lean_unbox_float(v_fst_1370_);
lean_dec_ref(v_fst_1370_);
v_snd_454__boxed_1375_ = lean_unbox_float(v_snd_1371_);
lean_dec_ref(v_snd_1371_);
v_res_1376_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1356_, v_inst_1357_, v_inst_1358_, v_inst_1359_, v_oldTraces_1360_, v_ref_1361_, v_toBind_1362_, v___f_1363_, v_inst_1364_, v_fst_1365_, v_cls_1366_, v_collapsed_boxed_1373_, v_tag_1368_, v___x_1369_, v_fst_453__boxed_1374_, v_snd_454__boxed_1375_, v_m_1372_);
lean_dec(v___x_1369_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object* v_always_1377_, lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_oldTraces_1382_, lean_object* v_toBind_1383_, lean_object* v___f_1384_, lean_object* v_inst_1385_, lean_object* v_fst_1386_, lean_object* v_cls_1387_, uint8_t v_collapsed_1388_, lean_object* v_tag_1389_, lean_object* v___x_1390_, double v_fst_1391_, double v_snd_1392_, lean_object* v_msg_1393_, lean_object* v___f_1394_, lean_object* v_ref_1395_){
_start:
{
lean_object* v_tryCatch_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_tryCatch_1396_ = lean_ctor_get(v_always_1377_, 1);
lean_inc(v_tryCatch_1396_);
lean_dec_ref(v_always_1377_);
v___x_1397_ = lean_box(v_collapsed_1388_);
v___x_1398_ = lean_box_float(v_fst_1391_);
v___x_1399_ = lean_box_float(v_snd_1392_);
lean_inc_ref(v_fst_1386_);
lean_inc(v_toBind_1383_);
v___f_1400_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1400_, 0, v_inst_1378_);
lean_closure_set(v___f_1400_, 1, v_inst_1379_);
lean_closure_set(v___f_1400_, 2, v_inst_1380_);
lean_closure_set(v___f_1400_, 3, v_inst_1381_);
lean_closure_set(v___f_1400_, 4, v_oldTraces_1382_);
lean_closure_set(v___f_1400_, 5, v_ref_1395_);
lean_closure_set(v___f_1400_, 6, v_toBind_1383_);
lean_closure_set(v___f_1400_, 7, v___f_1384_);
lean_closure_set(v___f_1400_, 8, v_inst_1385_);
lean_closure_set(v___f_1400_, 9, v_fst_1386_);
lean_closure_set(v___f_1400_, 10, v_cls_1387_);
lean_closure_set(v___f_1400_, 11, v___x_1397_);
lean_closure_set(v___f_1400_, 12, v_tag_1389_);
lean_closure_set(v___f_1400_, 13, v___x_1390_);
lean_closure_set(v___f_1400_, 14, v___x_1398_);
lean_closure_set(v___f_1400_, 15, v___x_1399_);
v___x_1401_ = lean_apply_1(v_msg_1393_, v_fst_1386_);
v___x_1402_ = lean_apply_3(v_tryCatch_1396_, lean_box(0), v___x_1401_, v___f_1394_);
v___x_1403_ = lean_apply_4(v_toBind_1383_, lean_box(0), lean_box(0), v___x_1402_, v___f_1400_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_1404_ = _args[0];
lean_object* v_inst_1405_ = _args[1];
lean_object* v_inst_1406_ = _args[2];
lean_object* v_inst_1407_ = _args[3];
lean_object* v_inst_1408_ = _args[4];
lean_object* v_oldTraces_1409_ = _args[5];
lean_object* v_toBind_1410_ = _args[6];
lean_object* v___f_1411_ = _args[7];
lean_object* v_inst_1412_ = _args[8];
lean_object* v_fst_1413_ = _args[9];
lean_object* v_cls_1414_ = _args[10];
lean_object* v_collapsed_1415_ = _args[11];
lean_object* v_tag_1416_ = _args[12];
lean_object* v___x_1417_ = _args[13];
lean_object* v_fst_1418_ = _args[14];
lean_object* v_snd_1419_ = _args[15];
lean_object* v_msg_1420_ = _args[16];
lean_object* v___f_1421_ = _args[17];
lean_object* v_ref_1422_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_1423_; double v_fst_496__boxed_1424_; double v_snd_497__boxed_1425_; lean_object* v_res_1426_; 
v_collapsed_boxed_1423_ = lean_unbox(v_collapsed_1415_);
v_fst_496__boxed_1424_ = lean_unbox_float(v_fst_1418_);
lean_dec_ref(v_fst_1418_);
v_snd_497__boxed_1425_ = lean_unbox_float(v_snd_1419_);
lean_dec_ref(v_snd_1419_);
v_res_1426_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(v_always_1404_, v_inst_1405_, v_inst_1406_, v_inst_1407_, v_inst_1408_, v_oldTraces_1409_, v_toBind_1410_, v___f_1411_, v_inst_1412_, v_fst_1413_, v_cls_1414_, v_collapsed_boxed_1423_, v_tag_1416_, v___x_1417_, v_fst_496__boxed_1424_, v_snd_497__boxed_1425_, v_msg_1420_, v___f_1421_, v_ref_1422_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_inst_1430_, lean_object* v_always_1431_, lean_object* v_inst_1432_, lean_object* v_cls_1433_, uint8_t v_collapsed_1434_, lean_object* v_tag_1435_, lean_object* v_opts_1436_, uint8_t v_clsEnabled_1437_, lean_object* v_oldTraces_1438_, lean_object* v_msg_1439_, lean_object* v_resStartStop_1440_){
_start:
{
lean_object* v___x_1441_; lean_object* v_toApplicative_1442_; lean_object* v_toBind_1443_; lean_object* v___x_1444_; lean_object* v_snd_1445_; lean_object* v_toPure_1446_; lean_object* v_fst_1447_; lean_object* v_fst_1448_; lean_object* v_snd_1449_; lean_object* v___f_1450_; lean_object* v___f_1451_; lean_object* v___f_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___f_1456_; uint8_t v___y_1461_; double v___y_1466_; uint8_t v___x_1471_; 
v___x_1441_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1442_ = lean_ctor_get(v_inst_1427_, 0);
v_toBind_1443_ = lean_ctor_get(v_inst_1427_, 1);
lean_inc_n(v_toBind_1443_, 2);
lean_inc_ref(v_always_1431_);
v___x_1444_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1431_);
v_snd_1445_ = lean_ctor_get(v_resStartStop_1440_, 1);
lean_inc(v_snd_1445_);
v_toPure_1446_ = lean_ctor_get(v_toApplicative_1442_, 1);
v_fst_1447_ = lean_ctor_get(v_resStartStop_1440_, 0);
lean_inc_n(v_fst_1447_, 2);
lean_dec_ref(v_resStartStop_1440_);
v_fst_1448_ = lean_ctor_get(v_snd_1445_, 0);
lean_inc_n(v_fst_1448_, 2);
v_snd_1449_ = lean_ctor_get(v_snd_1445_, 1);
lean_inc_n(v_snd_1449_, 2);
lean_dec(v_snd_1445_);
lean_inc_ref(v_oldTraces_1438_);
v___f_1450_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1450_, 0, v_oldTraces_1438_);
lean_inc(v_toPure_1446_);
v___f_1451_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1451_, 0, v_toPure_1446_);
lean_inc_ref(v_inst_1427_);
v___f_1452_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1452_, 0, v_inst_1427_);
lean_closure_set(v___f_1452_, 1, v___x_1444_);
lean_closure_set(v___f_1452_, 2, v_fst_1447_);
v___x_1453_ = l_Lean_trace_profiler;
v___x_1454_ = l_Lean_Option_get___redArg(v___x_1441_, v_opts_1436_, v___x_1453_);
v___x_1455_ = lean_box(v_collapsed_1434_);
lean_inc(v___x_1454_);
lean_inc_ref(v___f_1452_);
lean_inc_ref(v_inst_1429_);
lean_inc_ref(v_inst_1428_);
v___f_1456_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3___boxed), 19, 18);
lean_closure_set(v___f_1456_, 0, v_always_1431_);
lean_closure_set(v___f_1456_, 1, v_inst_1427_);
lean_closure_set(v___f_1456_, 2, v_inst_1428_);
lean_closure_set(v___f_1456_, 3, v_inst_1429_);
lean_closure_set(v___f_1456_, 4, v_inst_1430_);
lean_closure_set(v___f_1456_, 5, v_oldTraces_1438_);
lean_closure_set(v___f_1456_, 6, v_toBind_1443_);
lean_closure_set(v___f_1456_, 7, v___f_1452_);
lean_closure_set(v___f_1456_, 8, v_inst_1432_);
lean_closure_set(v___f_1456_, 9, v_fst_1447_);
lean_closure_set(v___f_1456_, 10, v_cls_1433_);
lean_closure_set(v___f_1456_, 11, v___x_1455_);
lean_closure_set(v___f_1456_, 12, v_tag_1435_);
lean_closure_set(v___f_1456_, 13, v___x_1454_);
lean_closure_set(v___f_1456_, 14, v_fst_1448_);
lean_closure_set(v___f_1456_, 15, v_snd_1449_);
lean_closure_set(v___f_1456_, 16, v_msg_1439_);
lean_closure_set(v___f_1456_, 17, v___f_1451_);
v___x_1471_ = lean_unbox(v___x_1454_);
if (v___x_1471_ == 0)
{
uint8_t v___x_1472_; 
lean_dec(v_snd_1449_);
lean_dec(v_fst_1448_);
v___x_1472_ = lean_unbox(v___x_1454_);
lean_dec(v___x_1454_);
v___y_1461_ = v___x_1472_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
lean_dec(v___x_1454_);
v___x_1473_ = l_Lean_KVMap_instValueNat;
v___x_1474_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1475_ = l_Lean_Option_get___redArg(v___x_1441_, v_opts_1436_, v___x_1474_);
v___x_1476_ = lean_unbox(v___x_1475_);
lean_dec(v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; double v___x_1479_; double v___x_1480_; double v___x_1481_; 
v___x_1477_ = l_Lean_trace_profiler_threshold;
v___x_1478_ = l_Lean_Option_get___redArg(v___x_1473_, v_opts_1436_, v___x_1477_);
v___x_1479_ = lean_float_of_nat(v___x_1478_);
v___x_1480_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1481_ = lean_float_div(v___x_1479_, v___x_1480_);
v___y_1466_ = v___x_1481_;
goto v___jp_1465_;
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; double v___x_1484_; 
v___x_1482_ = l_Lean_trace_profiler_threshold;
v___x_1483_ = l_Lean_Option_get___redArg(v___x_1473_, v_opts_1436_, v___x_1482_);
v___x_1484_ = lean_float_of_nat(v___x_1483_);
v___y_1466_ = v___x_1484_;
goto v___jp_1465_;
}
}
v___jp_1457_:
{
lean_object* v_getRef_1458_; lean_object* v___x_1459_; 
v_getRef_1458_ = lean_ctor_get(v_inst_1429_, 0);
lean_inc(v_getRef_1458_);
lean_dec_ref(v_inst_1429_);
v___x_1459_ = lean_apply_4(v_toBind_1443_, lean_box(0), lean_box(0), v_getRef_1458_, v___f_1456_);
return v___x_1459_;
}
v___jp_1460_:
{
if (v_clsEnabled_1437_ == 0)
{
if (v___y_1461_ == 0)
{
lean_object* v_modifyTraceState_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec_ref(v___f_1456_);
lean_dec_ref(v_inst_1429_);
v_modifyTraceState_1462_ = lean_ctor_get(v_inst_1428_, 0);
lean_inc(v_modifyTraceState_1462_);
lean_dec_ref(v_inst_1428_);
v___x_1463_ = lean_apply_1(v_modifyTraceState_1462_, v___f_1450_);
v___x_1464_ = lean_apply_4(v_toBind_1443_, lean_box(0), lean_box(0), v___x_1463_, v___f_1452_);
return v___x_1464_;
}
else
{
lean_dec_ref(v___f_1452_);
lean_dec_ref(v___f_1450_);
lean_dec_ref(v_inst_1428_);
goto v___jp_1457_;
}
}
else
{
lean_dec_ref(v___f_1452_);
lean_dec_ref(v___f_1450_);
lean_dec_ref(v_inst_1428_);
goto v___jp_1457_;
}
}
v___jp_1465_:
{
double v___x_1467_; double v___x_1468_; double v___x_1469_; uint8_t v___x_1470_; 
v___x_1467_ = lean_unbox_float(v_snd_1449_);
lean_dec(v_snd_1449_);
v___x_1468_ = lean_unbox_float(v_fst_1448_);
lean_dec(v_fst_1448_);
v___x_1469_ = lean_float_sub(v___x_1467_, v___x_1468_);
v___x_1470_ = lean_float_decLt(v___y_1466_, v___x_1469_);
v___y_1461_ = v___x_1470_;
goto v___jp_1460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object* v_inst_1485_, lean_object* v_inst_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_always_1489_, lean_object* v_inst_1490_, lean_object* v_cls_1491_, lean_object* v_collapsed_1492_, lean_object* v_tag_1493_, lean_object* v_opts_1494_, lean_object* v_clsEnabled_1495_, lean_object* v_oldTraces_1496_, lean_object* v_msg_1497_, lean_object* v_resStartStop_1498_){
_start:
{
uint8_t v_collapsed_boxed_1499_; uint8_t v_clsEnabled_boxed_1500_; lean_object* v_res_1501_; 
v_collapsed_boxed_1499_ = lean_unbox(v_collapsed_1492_);
v_clsEnabled_boxed_1500_ = lean_unbox(v_clsEnabled_1495_);
v_res_1501_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1485_, v_inst_1486_, v_inst_1487_, v_inst_1488_, v_always_1489_, v_inst_1490_, v_cls_1491_, v_collapsed_boxed_1499_, v_tag_1493_, v_opts_1494_, v_clsEnabled_boxed_1500_, v_oldTraces_1496_, v_msg_1497_, v_resStartStop_1498_);
lean_dec_ref(v_opts_1494_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object* v_00_u03b1_1502_, lean_object* v_m_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_00_u03b5_1508_, lean_object* v_always_1509_, lean_object* v_inst_1510_, lean_object* v_cls_1511_, uint8_t v_collapsed_1512_, lean_object* v_tag_1513_, lean_object* v_opts_1514_, uint8_t v_clsEnabled_1515_, lean_object* v_oldTraces_1516_, lean_object* v_msg_1517_, lean_object* v_resStartStop_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1504_, v_inst_1505_, v_inst_1506_, v_inst_1507_, v_always_1509_, v_inst_1510_, v_cls_1511_, v_collapsed_1512_, v_tag_1513_, v_opts_1514_, v_clsEnabled_1515_, v_oldTraces_1516_, v_msg_1517_, v_resStartStop_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_1520_ = _args[0];
lean_object* v_m_1521_ = _args[1];
lean_object* v_inst_1522_ = _args[2];
lean_object* v_inst_1523_ = _args[3];
lean_object* v_inst_1524_ = _args[4];
lean_object* v_inst_1525_ = _args[5];
lean_object* v_00_u03b5_1526_ = _args[6];
lean_object* v_always_1527_ = _args[7];
lean_object* v_inst_1528_ = _args[8];
lean_object* v_cls_1529_ = _args[9];
lean_object* v_collapsed_1530_ = _args[10];
lean_object* v_tag_1531_ = _args[11];
lean_object* v_opts_1532_ = _args[12];
lean_object* v_clsEnabled_1533_ = _args[13];
lean_object* v_oldTraces_1534_ = _args[14];
lean_object* v_msg_1535_ = _args[15];
lean_object* v_resStartStop_1536_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1537_; uint8_t v_clsEnabled_boxed_1538_; lean_object* v_res_1539_; 
v_collapsed_boxed_1537_ = lean_unbox(v_collapsed_1530_);
v_clsEnabled_boxed_1538_ = lean_unbox(v_clsEnabled_1533_);
v_res_1539_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(v_00_u03b1_1520_, v_m_1521_, v_inst_1522_, v_inst_1523_, v_inst_1524_, v_inst_1525_, v_00_u03b5_1526_, v_always_1527_, v_inst_1528_, v_cls_1529_, v_collapsed_boxed_1537_, v_tag_1531_, v_opts_1532_, v_clsEnabled_boxed_1538_, v_oldTraces_1534_, v_msg_1535_, v_resStartStop_1536_);
lean_dec_ref(v_opts_1532_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object* v_inst_1540_, lean_object* v_inst_1541_, lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_always_1544_, lean_object* v_inst_1545_, lean_object* v_cls_1546_, uint8_t v_collapsed_1547_, lean_object* v_tag_1548_, lean_object* v_opts_1549_, uint8_t v_clsEnabled_1550_, lean_object* v_oldTraces_1551_, lean_object* v_msg_1552_, lean_object* v_resStartStop_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1540_, v_inst_1541_, v_inst_1542_, v_inst_1543_, v_always_1544_, v_inst_1545_, v_cls_1546_, v_collapsed_1547_, v_tag_1548_, v_opts_1549_, v_clsEnabled_1550_, v_oldTraces_1551_, v_msg_1552_, v_resStartStop_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object* v_inst_1555_, lean_object* v_inst_1556_, lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_always_1559_, lean_object* v_inst_1560_, lean_object* v_cls_1561_, lean_object* v_collapsed_1562_, lean_object* v_tag_1563_, lean_object* v_opts_1564_, lean_object* v_clsEnabled_1565_, lean_object* v_oldTraces_1566_, lean_object* v_msg_1567_, lean_object* v_resStartStop_1568_){
_start:
{
uint8_t v_collapsed_boxed_1569_; uint8_t v_clsEnabled_boxed_1570_; lean_object* v_res_1571_; 
v_collapsed_boxed_1569_ = lean_unbox(v_collapsed_1562_);
v_clsEnabled_boxed_1570_ = lean_unbox(v_clsEnabled_1565_);
v_res_1571_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1555_, v_inst_1556_, v_inst_1557_, v_inst_1558_, v_always_1559_, v_inst_1560_, v_cls_1561_, v_collapsed_boxed_1569_, v_tag_1563_, v_opts_1564_, v_clsEnabled_boxed_1570_, v_oldTraces_1566_, v_msg_1567_, v_resStartStop_1568_);
lean_dec_ref(v_opts_1564_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object* v_toPure_1572_, lean_object* v_ex_1573_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v_ex_1573_);
v___x_1575_ = lean_apply_2(v_toPure_1572_, lean_box(0), v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object* v_toPure_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v_a_1577_);
v___x_1579_ = lean_apply_2(v_toPure_1576_, lean_box(0), v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object* v_start_1580_, lean_object* v_a_1581_, lean_object* v_toPure_1582_, lean_object* v_stop_1583_){
_start:
{
double v___x_1584_; double v___x_1585_; double v___x_1586_; double v___x_1587_; double v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1584_ = lean_float_of_nat(v_start_1580_);
v___x_1585_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1586_ = lean_float_div(v___x_1584_, v___x_1585_);
v___x_1587_ = lean_float_of_nat(v_stop_1583_);
v___x_1588_ = lean_float_div(v___x_1587_, v___x_1585_);
v___x_1589_ = lean_box_float(v___x_1586_);
v___x_1590_ = lean_box_float(v___x_1588_);
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v_a_1581_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_apply_2(v_toPure_1582_, lean_box(0), v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object* v_start_1594_, lean_object* v_toPure_1595_, lean_object* v_toBind_1596_, lean_object* v___x_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v___f_1599_; lean_object* v___x_1600_; 
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1599_, 0, v_start_1594_);
lean_closure_set(v___f_1599_, 1, v_a_1598_);
lean_closure_set(v___f_1599_, 2, v_toPure_1595_);
v___x_1600_ = lean_apply_4(v_toBind_1596_, lean_box(0), lean_box(0), v___x_1597_, v___f_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object* v_toPure_1601_, lean_object* v_toBind_1602_, lean_object* v___x_1603_, lean_object* v___x_1604_, lean_object* v_start_1605_){
_start:
{
lean_object* v___f_1606_; lean_object* v___x_1607_; 
lean_inc(v_toBind_1602_);
v___f_1606_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1606_, 0, v_start_1605_);
lean_closure_set(v___f_1606_, 1, v_toPure_1601_);
lean_closure_set(v___f_1606_, 2, v_toBind_1602_);
lean_closure_set(v___f_1606_, 3, v___x_1603_);
v___x_1607_ = lean_apply_4(v_toBind_1602_, lean_box(0), lean_box(0), v___x_1604_, v___f_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object* v_start_1608_, lean_object* v_a_1609_, lean_object* v_toPure_1610_, lean_object* v_stop_1611_){
_start:
{
double v___x_1612_; double v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1612_ = lean_float_of_nat(v_start_1608_);
v___x_1613_ = lean_float_of_nat(v_stop_1611_);
v___x_1614_ = lean_box_float(v___x_1612_);
v___x_1615_ = lean_box_float(v___x_1613_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_a_1609_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_apply_2(v_toPure_1610_, lean_box(0), v___x_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object* v_start_1619_, lean_object* v_toPure_1620_, lean_object* v_toBind_1621_, lean_object* v___x_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v___f_1624_; lean_object* v___x_1625_; 
v___f_1624_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__6), 4, 3);
lean_closure_set(v___f_1624_, 0, v_start_1619_);
lean_closure_set(v___f_1624_, 1, v_a_1623_);
lean_closure_set(v___f_1624_, 2, v_toPure_1620_);
v___x_1625_ = lean_apply_4(v_toBind_1621_, lean_box(0), lean_box(0), v___x_1622_, v___f_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object* v_toPure_1626_, lean_object* v_toBind_1627_, lean_object* v___x_1628_, lean_object* v___x_1629_, lean_object* v_start_1630_){
_start:
{
lean_object* v___f_1631_; lean_object* v___x_1632_; 
lean_inc(v_toBind_1627_);
v___f_1631_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1631_, 0, v_start_1630_);
lean_closure_set(v___f_1631_, 1, v_toPure_1626_);
lean_closure_set(v___f_1631_, 2, v_toBind_1627_);
lean_closure_set(v___f_1631_, 3, v___x_1628_);
v___x_1632_ = lean_apply_4(v_toBind_1627_, lean_box(0), lean_box(0), v___x_1629_, v___f_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object* v_always_1633_, lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_cls_1639_, uint8_t v_collapsed_1640_, lean_object* v_tag_1641_, lean_object* v_opts_1642_, uint8_t v_clsEnabled_1643_, lean_object* v_msg_1644_, lean_object* v_toPure_1645_, lean_object* v_toBind_1646_, lean_object* v_k_1647_, lean_object* v___x_1648_, lean_object* v_inst_1649_, lean_object* v_oldTraces_1650_){
_start:
{
lean_object* v_tryCatch_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___f_1654_; lean_object* v___f_1655_; lean_object* v___f_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v_tryCatch_1651_ = lean_ctor_get(v_always_1633_, 1);
lean_inc(v_tryCatch_1651_);
v___x_1652_ = lean_box(v_collapsed_1640_);
v___x_1653_ = lean_box(v_clsEnabled_1643_);
lean_inc_ref(v_opts_1642_);
v___f_1654_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1654_, 0, v_inst_1634_);
lean_closure_set(v___f_1654_, 1, v_inst_1635_);
lean_closure_set(v___f_1654_, 2, v_inst_1636_);
lean_closure_set(v___f_1654_, 3, v_inst_1637_);
lean_closure_set(v___f_1654_, 4, v_always_1633_);
lean_closure_set(v___f_1654_, 5, v_inst_1638_);
lean_closure_set(v___f_1654_, 6, v_cls_1639_);
lean_closure_set(v___f_1654_, 7, v___x_1652_);
lean_closure_set(v___f_1654_, 8, v_tag_1641_);
lean_closure_set(v___f_1654_, 9, v_opts_1642_);
lean_closure_set(v___f_1654_, 10, v___x_1653_);
lean_closure_set(v___f_1654_, 11, v_oldTraces_1650_);
lean_closure_set(v___f_1654_, 12, v_msg_1644_);
lean_inc_n(v_toPure_1645_, 2);
v___f_1655_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1655_, 0, v_toPure_1645_);
v___f_1656_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1656_, 0, v_toPure_1645_);
lean_inc(v_toBind_1646_);
v___x_1657_ = lean_apply_4(v_toBind_1646_, lean_box(0), lean_box(0), v_k_1647_, v___f_1656_);
v___x_1658_ = lean_apply_3(v_tryCatch_1651_, lean_box(0), v___x_1657_, v___f_1655_);
v___x_1659_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1660_ = l_Lean_Option_get___redArg(v___x_1648_, v_opts_1642_, v___x_1659_);
lean_dec_ref(v_opts_1642_);
v___x_1661_ = lean_unbox(v___x_1660_);
lean_dec(v___x_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1662_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1663_ = lean_apply_2(v_inst_1649_, lean_box(0), v___x_1662_);
lean_inc(v___x_1663_);
lean_inc_n(v_toBind_1646_, 2);
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1664_, 0, v_toPure_1645_);
lean_closure_set(v___f_1664_, 1, v_toBind_1646_);
lean_closure_set(v___f_1664_, 2, v___x_1663_);
lean_closure_set(v___f_1664_, 3, v___x_1658_);
v___x_1665_ = lean_apply_4(v_toBind_1646_, lean_box(0), lean_box(0), v___x_1663_, v___f_1664_);
v___x_1666_ = lean_apply_4(v_toBind_1646_, lean_box(0), lean_box(0), v___x_1665_, v___f_1654_);
return v___x_1666_;
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___f_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1667_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1668_ = lean_apply_2(v_inst_1649_, lean_box(0), v___x_1667_);
lean_inc(v___x_1668_);
lean_inc_n(v_toBind_1646_, 2);
v___f_1669_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_1669_, 0, v_toPure_1645_);
lean_closure_set(v___f_1669_, 1, v_toBind_1646_);
lean_closure_set(v___f_1669_, 2, v___x_1668_);
lean_closure_set(v___f_1669_, 3, v___x_1658_);
v___x_1670_ = lean_apply_4(v_toBind_1646_, lean_box(0), lean_box(0), v___x_1668_, v___f_1669_);
v___x_1671_ = lean_apply_4(v_toBind_1646_, lean_box(0), lean_box(0), v___x_1670_, v___f_1654_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_always_1672_ = _args[0];
lean_object* v_inst_1673_ = _args[1];
lean_object* v_inst_1674_ = _args[2];
lean_object* v_inst_1675_ = _args[3];
lean_object* v_inst_1676_ = _args[4];
lean_object* v_inst_1677_ = _args[5];
lean_object* v_cls_1678_ = _args[6];
lean_object* v_collapsed_1679_ = _args[7];
lean_object* v_tag_1680_ = _args[8];
lean_object* v_opts_1681_ = _args[9];
lean_object* v_clsEnabled_1682_ = _args[10];
lean_object* v_msg_1683_ = _args[11];
lean_object* v_toPure_1684_ = _args[12];
lean_object* v_toBind_1685_ = _args[13];
lean_object* v_k_1686_ = _args[14];
lean_object* v___x_1687_ = _args[15];
lean_object* v_inst_1688_ = _args[16];
lean_object* v_oldTraces_1689_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_1690_; uint8_t v_clsEnabled_boxed_1691_; lean_object* v_res_1692_; 
v_collapsed_boxed_1690_ = lean_unbox(v_collapsed_1679_);
v_clsEnabled_boxed_1691_ = lean_unbox(v_clsEnabled_1682_);
v_res_1692_ = l_Lean_withTraceNode___redArg___lam__9(v_always_1672_, v_inst_1673_, v_inst_1674_, v_inst_1675_, v_inst_1676_, v_inst_1677_, v_cls_1678_, v_collapsed_boxed_1690_, v_tag_1680_, v_opts_1681_, v_clsEnabled_boxed_1691_, v_msg_1683_, v_toPure_1684_, v_toBind_1685_, v_k_1686_, v___x_1687_, v_inst_1688_, v_oldTraces_1689_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object* v_always_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_cls_1699_, uint8_t v_collapsed_1700_, lean_object* v_tag_1701_, lean_object* v_opts_1702_, lean_object* v_msg_1703_, lean_object* v_toPure_1704_, lean_object* v_toBind_1705_, lean_object* v_k_1706_, lean_object* v___x_1707_, lean_object* v_inst_1708_, uint8_t v_clsEnabled_1709_){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___f_1712_; 
v___x_1710_ = lean_box(v_collapsed_1700_);
v___x_1711_ = lean_box(v_clsEnabled_1709_);
lean_inc_ref(v___x_1707_);
lean_inc(v_k_1706_);
lean_inc(v_toBind_1705_);
lean_inc_ref(v_opts_1702_);
lean_inc_ref(v_inst_1695_);
lean_inc_ref(v_inst_1694_);
v___f_1712_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__9___boxed), 18, 17);
lean_closure_set(v___f_1712_, 0, v_always_1693_);
lean_closure_set(v___f_1712_, 1, v_inst_1694_);
lean_closure_set(v___f_1712_, 2, v_inst_1695_);
lean_closure_set(v___f_1712_, 3, v_inst_1696_);
lean_closure_set(v___f_1712_, 4, v_inst_1697_);
lean_closure_set(v___f_1712_, 5, v_inst_1698_);
lean_closure_set(v___f_1712_, 6, v_cls_1699_);
lean_closure_set(v___f_1712_, 7, v___x_1710_);
lean_closure_set(v___f_1712_, 8, v_tag_1701_);
lean_closure_set(v___f_1712_, 9, v_opts_1702_);
lean_closure_set(v___f_1712_, 10, v___x_1711_);
lean_closure_set(v___f_1712_, 11, v_msg_1703_);
lean_closure_set(v___f_1712_, 12, v_toPure_1704_);
lean_closure_set(v___f_1712_, 13, v_toBind_1705_);
lean_closure_set(v___f_1712_, 14, v_k_1706_);
lean_closure_set(v___f_1712_, 15, v___x_1707_);
lean_closure_set(v___f_1712_, 16, v_inst_1708_);
if (v_clsEnabled_1709_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1716_ = l_Lean_trace_profiler;
v___x_1717_ = l_Lean_Option_get___redArg(v___x_1707_, v_opts_1702_, v___x_1716_);
lean_dec_ref(v_opts_1702_);
v___x_1718_ = lean_unbox(v___x_1717_);
lean_dec(v___x_1717_);
if (v___x_1718_ == 0)
{
lean_dec_ref(v___f_1712_);
lean_dec(v_toBind_1705_);
lean_dec_ref(v_inst_1695_);
lean_dec_ref(v_inst_1694_);
return v_k_1706_;
}
else
{
lean_dec(v_k_1706_);
goto v___jp_1713_;
}
}
else
{
lean_dec_ref(v___x_1707_);
lean_dec(v_k_1706_);
lean_dec_ref(v_opts_1702_);
goto v___jp_1713_;
}
v___jp_1713_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1694_, v_inst_1695_);
v___x_1715_ = lean_apply_4(v_toBind_1705_, lean_box(0), lean_box(0), v___x_1714_, v___f_1712_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_1719_ = _args[0];
lean_object* v_inst_1720_ = _args[1];
lean_object* v_inst_1721_ = _args[2];
lean_object* v_inst_1722_ = _args[3];
lean_object* v_inst_1723_ = _args[4];
lean_object* v_inst_1724_ = _args[5];
lean_object* v_cls_1725_ = _args[6];
lean_object* v_collapsed_1726_ = _args[7];
lean_object* v_tag_1727_ = _args[8];
lean_object* v_opts_1728_ = _args[9];
lean_object* v_msg_1729_ = _args[10];
lean_object* v_toPure_1730_ = _args[11];
lean_object* v_toBind_1731_ = _args[12];
lean_object* v_k_1732_ = _args[13];
lean_object* v___x_1733_ = _args[14];
lean_object* v_inst_1734_ = _args[15];
lean_object* v_clsEnabled_1735_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1736_; uint8_t v_clsEnabled_boxed_1737_; lean_object* v_res_1738_; 
v_collapsed_boxed_1736_ = lean_unbox(v_collapsed_1726_);
v_clsEnabled_boxed_1737_ = lean_unbox(v_clsEnabled_1735_);
v_res_1738_ = l_Lean_withTraceNode___redArg___lam__10(v_always_1719_, v_inst_1720_, v_inst_1721_, v_inst_1722_, v_inst_1723_, v_inst_1724_, v_cls_1725_, v_collapsed_boxed_1736_, v_tag_1727_, v_opts_1728_, v_msg_1729_, v_toPure_1730_, v_toBind_1731_, v_k_1732_, v___x_1733_, v_inst_1734_, v_clsEnabled_boxed_1737_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__12(lean_object* v_toPure_1739_, lean_object* v_cls_1740_, lean_object* v_toBind_1741_, lean_object* v_getOptionsUnrestricted_1742_, lean_object* v_____do__lift_1743_){
_start:
{
lean_object* v___f_1744_; lean_object* v___x_1745_; 
v___f_1744_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1744_, 0, v_toPure_1739_);
lean_closure_set(v___f_1744_, 1, v_cls_1740_);
lean_closure_set(v___f_1744_, 2, v_____do__lift_1743_);
v___x_1745_ = lean_apply_4(v_toBind_1741_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_1742_, v___f_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__11(lean_object* v_k_1746_, lean_object* v_inst_1747_, lean_object* v_toApplicative_1748_, lean_object* v_always_1749_, lean_object* v_inst_1750_, lean_object* v_inst_1751_, lean_object* v_inst_1752_, lean_object* v_inst_1753_, lean_object* v_cls_1754_, uint8_t v_collapsed_1755_, lean_object* v_tag_1756_, lean_object* v_msg_1757_, lean_object* v_toBind_1758_, lean_object* v___x_1759_, lean_object* v_inst_1760_, lean_object* v_getOptionsUnrestricted_1761_, lean_object* v_opts_1762_){
_start:
{
uint8_t v_hasTrace_1763_; 
v_hasTrace_1763_ = lean_ctor_get_uint8(v_opts_1762_, sizeof(void*)*1);
if (v_hasTrace_1763_ == 0)
{
lean_dec_ref(v_opts_1762_);
lean_dec(v_getOptionsUnrestricted_1761_);
lean_dec(v_inst_1760_);
lean_dec_ref(v___x_1759_);
lean_dec(v_toBind_1758_);
lean_dec(v_msg_1757_);
lean_dec_ref(v_tag_1756_);
lean_dec(v_cls_1754_);
lean_dec_ref(v_inst_1753_);
lean_dec(v_inst_1752_);
lean_dec_ref(v_inst_1751_);
lean_dec_ref(v_inst_1750_);
lean_dec_ref(v_always_1749_);
lean_dec_ref(v_toApplicative_1748_);
lean_dec_ref(v_inst_1747_);
return v_k_1746_;
}
else
{
lean_object* v_getInheritedTraceOptions_1764_; lean_object* v_toPure_1765_; lean_object* v___x_1766_; lean_object* v___f_1767_; lean_object* v___f_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_getInheritedTraceOptions_1764_ = lean_ctor_get(v_inst_1747_, 2);
lean_inc(v_getInheritedTraceOptions_1764_);
v_toPure_1765_ = lean_ctor_get(v_toApplicative_1748_, 1);
lean_inc_n(v_toPure_1765_, 2);
lean_dec_ref(v_toApplicative_1748_);
v___x_1766_ = lean_box(v_collapsed_1755_);
lean_inc_n(v_toBind_1758_, 3);
lean_inc(v_cls_1754_);
v___f_1767_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__10___boxed), 17, 16);
lean_closure_set(v___f_1767_, 0, v_always_1749_);
lean_closure_set(v___f_1767_, 1, v_inst_1750_);
lean_closure_set(v___f_1767_, 2, v_inst_1747_);
lean_closure_set(v___f_1767_, 3, v_inst_1751_);
lean_closure_set(v___f_1767_, 4, v_inst_1752_);
lean_closure_set(v___f_1767_, 5, v_inst_1753_);
lean_closure_set(v___f_1767_, 6, v_cls_1754_);
lean_closure_set(v___f_1767_, 7, v___x_1766_);
lean_closure_set(v___f_1767_, 8, v_tag_1756_);
lean_closure_set(v___f_1767_, 9, v_opts_1762_);
lean_closure_set(v___f_1767_, 10, v_msg_1757_);
lean_closure_set(v___f_1767_, 11, v_toPure_1765_);
lean_closure_set(v___f_1767_, 12, v_toBind_1758_);
lean_closure_set(v___f_1767_, 13, v_k_1746_);
lean_closure_set(v___f_1767_, 14, v___x_1759_);
lean_closure_set(v___f_1767_, 15, v_inst_1760_);
v___f_1768_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__12), 5, 4);
lean_closure_set(v___f_1768_, 0, v_toPure_1765_);
lean_closure_set(v___f_1768_, 1, v_cls_1754_);
lean_closure_set(v___f_1768_, 2, v_toBind_1758_);
lean_closure_set(v___f_1768_, 3, v_getOptionsUnrestricted_1761_);
v___x_1769_ = lean_apply_4(v_toBind_1758_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1764_, v___f_1768_);
v___x_1770_ = lean_apply_4(v_toBind_1758_, lean_box(0), lean_box(0), v___x_1769_, v___f_1767_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_k_1771_ = _args[0];
lean_object* v_inst_1772_ = _args[1];
lean_object* v_toApplicative_1773_ = _args[2];
lean_object* v_always_1774_ = _args[3];
lean_object* v_inst_1775_ = _args[4];
lean_object* v_inst_1776_ = _args[5];
lean_object* v_inst_1777_ = _args[6];
lean_object* v_inst_1778_ = _args[7];
lean_object* v_cls_1779_ = _args[8];
lean_object* v_collapsed_1780_ = _args[9];
lean_object* v_tag_1781_ = _args[10];
lean_object* v_msg_1782_ = _args[11];
lean_object* v_toBind_1783_ = _args[12];
lean_object* v___x_1784_ = _args[13];
lean_object* v_inst_1785_ = _args[14];
lean_object* v_getOptionsUnrestricted_1786_ = _args[15];
lean_object* v_opts_1787_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1788_; lean_object* v_res_1789_; 
v_collapsed_boxed_1788_ = lean_unbox(v_collapsed_1780_);
v_res_1789_ = l_Lean_withTraceNode___redArg___lam__11(v_k_1771_, v_inst_1772_, v_toApplicative_1773_, v_always_1774_, v_inst_1775_, v_inst_1776_, v_inst_1777_, v_inst_1778_, v_cls_1779_, v_collapsed_boxed_1788_, v_tag_1781_, v_msg_1782_, v_toBind_1783_, v___x_1784_, v_inst_1785_, v_getOptionsUnrestricted_1786_, v_opts_1787_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object* v_inst_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_always_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_cls_1798_, lean_object* v_msg_1799_, lean_object* v_k_1800_, uint8_t v_collapsed_1801_, lean_object* v_tag_1802_){
_start:
{
lean_object* v___x_1803_; lean_object* v_toApplicative_1804_; lean_object* v_toBind_1805_; lean_object* v_getOptionsUnrestricted_1806_; lean_object* v___x_1807_; lean_object* v___f_1808_; lean_object* v___x_1809_; 
v___x_1803_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1804_ = lean_ctor_get(v_inst_1790_, 0);
lean_inc_ref(v_toApplicative_1804_);
v_toBind_1805_ = lean_ctor_get(v_inst_1790_, 1);
lean_inc_n(v_toBind_1805_, 2);
v_getOptionsUnrestricted_1806_ = lean_ctor_get(v_inst_1794_, 1);
lean_inc_n(v_getOptionsUnrestricted_1806_, 2);
lean_dec_ref(v_inst_1794_);
v___x_1807_ = lean_box(v_collapsed_1801_);
v___f_1808_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_1808_, 0, v_k_1800_);
lean_closure_set(v___f_1808_, 1, v_inst_1791_);
lean_closure_set(v___f_1808_, 2, v_toApplicative_1804_);
lean_closure_set(v___f_1808_, 3, v_always_1795_);
lean_closure_set(v___f_1808_, 4, v_inst_1790_);
lean_closure_set(v___f_1808_, 5, v_inst_1792_);
lean_closure_set(v___f_1808_, 6, v_inst_1793_);
lean_closure_set(v___f_1808_, 7, v_inst_1797_);
lean_closure_set(v___f_1808_, 8, v_cls_1798_);
lean_closure_set(v___f_1808_, 9, v___x_1807_);
lean_closure_set(v___f_1808_, 10, v_tag_1802_);
lean_closure_set(v___f_1808_, 11, v_msg_1799_);
lean_closure_set(v___f_1808_, 12, v_toBind_1805_);
lean_closure_set(v___f_1808_, 13, v___x_1803_);
lean_closure_set(v___f_1808_, 14, v_inst_1796_);
lean_closure_set(v___f_1808_, 15, v_getOptionsUnrestricted_1806_);
v___x_1809_ = lean_apply_4(v_toBind_1805_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_1806_, v___f_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_always_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_cls_1818_, lean_object* v_msg_1819_, lean_object* v_k_1820_, lean_object* v_collapsed_1821_, lean_object* v_tag_1822_){
_start:
{
uint8_t v_collapsed_boxed_1823_; lean_object* v_res_1824_; 
v_collapsed_boxed_1823_ = lean_unbox(v_collapsed_1821_);
v_res_1824_ = l_Lean_withTraceNode___redArg(v_inst_1810_, v_inst_1811_, v_inst_1812_, v_inst_1813_, v_inst_1814_, v_always_1815_, v_inst_1816_, v_inst_1817_, v_cls_1818_, v_msg_1819_, v_k_1820_, v_collapsed_boxed_1823_, v_tag_1822_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object* v_00_u03b1_1825_, lean_object* v_m_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_00_u03b5_1832_, lean_object* v_always_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_cls_1836_, lean_object* v_msg_1837_, lean_object* v_k_1838_, uint8_t v_collapsed_1839_, lean_object* v_tag_1840_){
_start:
{
lean_object* v___x_1841_; lean_object* v_toApplicative_1842_; lean_object* v_toBind_1843_; lean_object* v_getOptionsUnrestricted_1844_; lean_object* v___x_1845_; lean_object* v___f_1846_; lean_object* v___x_1847_; 
v___x_1841_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1842_ = lean_ctor_get(v_inst_1827_, 0);
lean_inc_ref(v_toApplicative_1842_);
v_toBind_1843_ = lean_ctor_get(v_inst_1827_, 1);
lean_inc_n(v_toBind_1843_, 2);
v_getOptionsUnrestricted_1844_ = lean_ctor_get(v_inst_1831_, 1);
lean_inc_n(v_getOptionsUnrestricted_1844_, 2);
lean_dec_ref(v_inst_1831_);
v___x_1845_ = lean_box(v_collapsed_1839_);
v___f_1846_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_1846_, 0, v_k_1838_);
lean_closure_set(v___f_1846_, 1, v_inst_1828_);
lean_closure_set(v___f_1846_, 2, v_toApplicative_1842_);
lean_closure_set(v___f_1846_, 3, v_always_1833_);
lean_closure_set(v___f_1846_, 4, v_inst_1827_);
lean_closure_set(v___f_1846_, 5, v_inst_1829_);
lean_closure_set(v___f_1846_, 6, v_inst_1830_);
lean_closure_set(v___f_1846_, 7, v_inst_1835_);
lean_closure_set(v___f_1846_, 8, v_cls_1836_);
lean_closure_set(v___f_1846_, 9, v___x_1845_);
lean_closure_set(v___f_1846_, 10, v_tag_1840_);
lean_closure_set(v___f_1846_, 11, v_msg_1837_);
lean_closure_set(v___f_1846_, 12, v_toBind_1843_);
lean_closure_set(v___f_1846_, 13, v___x_1841_);
lean_closure_set(v___f_1846_, 14, v_inst_1834_);
lean_closure_set(v___f_1846_, 15, v_getOptionsUnrestricted_1844_);
v___x_1847_ = lean_apply_4(v_toBind_1843_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_1844_, v___f_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_m_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_00_u03b5_1855_, lean_object* v_always_1856_, lean_object* v_inst_1857_, lean_object* v_inst_1858_, lean_object* v_cls_1859_, lean_object* v_msg_1860_, lean_object* v_k_1861_, lean_object* v_collapsed_1862_, lean_object* v_tag_1863_){
_start:
{
uint8_t v_collapsed_boxed_1864_; lean_object* v_res_1865_; 
v_collapsed_boxed_1864_ = lean_unbox(v_collapsed_1862_);
v_res_1865_ = l_Lean_withTraceNode(v_00_u03b1_1848_, v_m_1849_, v_inst_1850_, v_inst_1851_, v_inst_1852_, v_inst_1853_, v_inst_1854_, v_00_u03b5_1855_, v_always_1856_, v_inst_1857_, v_inst_1858_, v_cls_1859_, v_msg_1860_, v_k_1861_, v_collapsed_boxed_1864_, v_tag_1863_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object* v_self_1866_){
_start:
{
lean_object* v_fst_1867_; 
v_fst_1867_ = lean_ctor_get(v_self_1866_, 0);
lean_inc(v_fst_1867_);
return v_fst_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object* v_self_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_1868_);
lean_dec_ref(v_self_1868_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object* v_toPure_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_a_1871_);
v___x_1873_ = lean_apply_2(v_toPure_1870_, lean_box(0), v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object* v_toPure_1874_, lean_object* v_ex_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_ex_1875_);
v___x_1877_ = lean_apply_2(v_toPure_1874_, lean_box(0), v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object* v_toPure_1878_, lean_object* v_x_1879_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_a_1880_ = lean_ctor_get(v_x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v_x_1879_, 1);
v___x_1881_ = l_Lean_Exception_toMessageData(v_a_1880_);
v___x_1882_ = lean_apply_2(v_toPure_1878_, lean_box(0), v___x_1881_);
return v___x_1882_;
}
else
{
lean_object* v_a_1883_; lean_object* v_snd_1884_; lean_object* v___x_1885_; 
v_a_1883_ = lean_ctor_get(v_x_1879_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v_x_1879_, 1);
v_snd_1884_ = lean_ctor_get(v_a_1883_, 1);
lean_inc(v_snd_1884_);
lean_dec(v_a_1883_);
v___x_1885_ = lean_apply_2(v_toPure_1878_, lean_box(0), v_snd_1884_);
return v___x_1885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v___f_1891_, lean_object* v_cls_1892_, uint8_t v_collapsed_1893_, lean_object* v_tag_1894_, lean_object* v_opts_1895_, uint8_t v_clsEnabled_1896_, lean_object* v_oldTraces_1897_, lean_object* v_msg_1898_, lean_object* v_resStartStop_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1886_, v_inst_1887_, v_inst_1888_, v_inst_1889_, v_inst_1890_, v___f_1891_, v_cls_1892_, v_collapsed_1893_, v_tag_1894_, v_opts_1895_, v_clsEnabled_1896_, v_oldTraces_1897_, v_msg_1898_, v_resStartStop_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6___boxed(lean_object* v_inst_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v___f_1906_, lean_object* v_cls_1907_, lean_object* v_collapsed_1908_, lean_object* v_tag_1909_, lean_object* v_opts_1910_, lean_object* v_clsEnabled_1911_, lean_object* v_oldTraces_1912_, lean_object* v_msg_1913_, lean_object* v_resStartStop_1914_){
_start:
{
uint8_t v_collapsed_boxed_1915_; uint8_t v_clsEnabled_boxed_1916_; lean_object* v_res_1917_; 
v_collapsed_boxed_1915_ = lean_unbox(v_collapsed_1908_);
v_clsEnabled_boxed_1916_ = lean_unbox(v_clsEnabled_1911_);
v_res_1917_ = l_Lean_withTraceNode_x27___redArg___lam__6(v_inst_1901_, v_inst_1902_, v_inst_1903_, v_inst_1904_, v_inst_1905_, v___f_1906_, v_cls_1907_, v_collapsed_boxed_1915_, v_tag_1909_, v_opts_1910_, v_clsEnabled_boxed_1916_, v_oldTraces_1912_, v_msg_1913_, v_resStartStop_1914_);
lean_dec_ref(v_opts_1910_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object* v_start_1918_, lean_object* v_a_1919_, lean_object* v_toPure_1920_, lean_object* v_stop_1921_){
_start:
{
double v___x_1922_; double v___x_1923_; double v___x_1924_; double v___x_1925_; double v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1922_ = lean_float_of_nat(v_start_1918_);
v___x_1923_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1924_ = lean_float_div(v___x_1922_, v___x_1923_);
v___x_1925_ = lean_float_of_nat(v_stop_1921_);
v___x_1926_ = lean_float_div(v___x_1925_, v___x_1923_);
v___x_1927_ = lean_box_float(v___x_1924_);
v___x_1928_ = lean_box_float(v___x_1926_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1919_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_apply_2(v_toPure_1920_, lean_box(0), v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object* v_start_1932_, lean_object* v_toPure_1933_, lean_object* v_toBind_1934_, lean_object* v___x_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___f_1937_; lean_object* v___x_1938_; 
v___f_1937_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_1937_, 0, v_start_1932_);
lean_closure_set(v___f_1937_, 1, v_a_1936_);
lean_closure_set(v___f_1937_, 2, v_toPure_1933_);
v___x_1938_ = lean_apply_4(v_toBind_1934_, lean_box(0), lean_box(0), v___x_1935_, v___f_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object* v_toPure_1939_, lean_object* v_toBind_1940_, lean_object* v___x_1941_, lean_object* v___x_1942_, lean_object* v_start_1943_){
_start:
{
lean_object* v___f_1944_; lean_object* v___x_1945_; 
lean_inc(v_toBind_1940_);
v___f_1944_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1944_, 0, v_start_1943_);
lean_closure_set(v___f_1944_, 1, v_toPure_1939_);
lean_closure_set(v___f_1944_, 2, v_toBind_1940_);
lean_closure_set(v___f_1944_, 3, v___x_1941_);
v___x_1945_ = lean_apply_4(v_toBind_1940_, lean_box(0), lean_box(0), v___x_1942_, v___f_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object* v_start_1946_, lean_object* v_a_1947_, lean_object* v_toPure_1948_, lean_object* v_stop_1949_){
_start:
{
double v___x_1950_; double v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1950_ = lean_float_of_nat(v_start_1946_);
v___x_1951_ = lean_float_of_nat(v_stop_1949_);
v___x_1952_ = lean_box_float(v___x_1950_);
v___x_1953_ = lean_box_float(v___x_1951_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1952_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v_a_1947_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_apply_2(v_toPure_1948_, lean_box(0), v___x_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object* v_start_1957_, lean_object* v_toPure_1958_, lean_object* v_toBind_1959_, lean_object* v___x_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v___f_1962_; lean_object* v___x_1963_; 
v___f_1962_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__8), 4, 3);
lean_closure_set(v___f_1962_, 0, v_start_1957_);
lean_closure_set(v___f_1962_, 1, v_a_1961_);
lean_closure_set(v___f_1962_, 2, v_toPure_1958_);
v___x_1963_ = lean_apply_4(v_toBind_1959_, lean_box(0), lean_box(0), v___x_1960_, v___f_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object* v_toPure_1964_, lean_object* v_toBind_1965_, lean_object* v___x_1966_, lean_object* v___x_1967_, lean_object* v_start_1968_){
_start:
{
lean_object* v___f_1969_; lean_object* v___x_1970_; 
lean_inc(v_toBind_1965_);
v___f_1969_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__9), 5, 4);
lean_closure_set(v___f_1969_, 0, v_start_1968_);
lean_closure_set(v___f_1969_, 1, v_toPure_1964_);
lean_closure_set(v___f_1969_, 2, v_toBind_1965_);
lean_closure_set(v___f_1969_, 3, v___x_1966_);
v___x_1970_ = lean_apply_4(v_toBind_1965_, lean_box(0), lean_box(0), v___x_1967_, v___f_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v___f_1976_, lean_object* v_cls_1977_, uint8_t v_collapsed_1978_, lean_object* v_tag_1979_, lean_object* v_opts_1980_, uint8_t v_clsEnabled_1981_, lean_object* v_msg_1982_, lean_object* v_toBind_1983_, lean_object* v_k_1984_, lean_object* v___f_1985_, lean_object* v___f_1986_, lean_object* v___x_1987_, lean_object* v_inst_1988_, lean_object* v_toPure_1989_, lean_object* v_oldTraces_1990_){
_start:
{
lean_object* v_tryCatch_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v_tryCatch_1991_ = lean_ctor_get(v_inst_1971_, 1);
lean_inc(v_tryCatch_1991_);
v___x_1992_ = lean_box(v_collapsed_1978_);
v___x_1993_ = lean_box(v_clsEnabled_1981_);
lean_inc_ref(v_opts_1980_);
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__6___boxed), 14, 13);
lean_closure_set(v___f_1994_, 0, v_inst_1972_);
lean_closure_set(v___f_1994_, 1, v_inst_1973_);
lean_closure_set(v___f_1994_, 2, v_inst_1974_);
lean_closure_set(v___f_1994_, 3, v_inst_1975_);
lean_closure_set(v___f_1994_, 4, v_inst_1971_);
lean_closure_set(v___f_1994_, 5, v___f_1976_);
lean_closure_set(v___f_1994_, 6, v_cls_1977_);
lean_closure_set(v___f_1994_, 7, v___x_1992_);
lean_closure_set(v___f_1994_, 8, v_tag_1979_);
lean_closure_set(v___f_1994_, 9, v_opts_1980_);
lean_closure_set(v___f_1994_, 10, v___x_1993_);
lean_closure_set(v___f_1994_, 11, v_oldTraces_1990_);
lean_closure_set(v___f_1994_, 12, v_msg_1982_);
lean_inc(v_toBind_1983_);
v___x_1995_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v_k_1984_, v___f_1985_);
v___x_1996_ = lean_apply_3(v_tryCatch_1991_, lean_box(0), v___x_1995_, v___f_1986_);
v___x_1997_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1998_ = l_Lean_Option_get___redArg(v___x_1987_, v_opts_1980_, v___x_1997_);
lean_dec_ref(v_opts_1980_);
v___x_1999_ = lean_unbox(v___x_1998_);
lean_dec(v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___f_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2000_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_2001_ = lean_apply_2(v_inst_1988_, lean_box(0), v___x_2000_);
lean_inc(v___x_2001_);
lean_inc_n(v_toBind_1983_, 2);
v___f_2002_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__7), 5, 4);
lean_closure_set(v___f_2002_, 0, v_toPure_1989_);
lean_closure_set(v___f_2002_, 1, v_toBind_1983_);
lean_closure_set(v___f_2002_, 2, v___x_2001_);
lean_closure_set(v___f_2002_, 3, v___x_1996_);
v___x_2003_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v___x_2001_, v___f_2002_);
v___x_2004_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v___x_2003_, v___f_1994_);
return v___x_2004_;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___f_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2005_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_2006_ = lean_apply_2(v_inst_1988_, lean_box(0), v___x_2005_);
lean_inc(v___x_2006_);
lean_inc_n(v_toBind_1983_, 2);
v___f_2007_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__10), 5, 4);
lean_closure_set(v___f_2007_, 0, v_toPure_1989_);
lean_closure_set(v___f_2007_, 1, v_toBind_1983_);
lean_closure_set(v___f_2007_, 2, v___x_2006_);
lean_closure_set(v___f_2007_, 3, v___x_1996_);
v___x_2008_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v___x_2006_, v___f_2007_);
v___x_2009_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v___x_2008_, v___f_1994_);
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_2010_ = _args[0];
lean_object* v_inst_2011_ = _args[1];
lean_object* v_inst_2012_ = _args[2];
lean_object* v_inst_2013_ = _args[3];
lean_object* v_inst_2014_ = _args[4];
lean_object* v___f_2015_ = _args[5];
lean_object* v_cls_2016_ = _args[6];
lean_object* v_collapsed_2017_ = _args[7];
lean_object* v_tag_2018_ = _args[8];
lean_object* v_opts_2019_ = _args[9];
lean_object* v_clsEnabled_2020_ = _args[10];
lean_object* v_msg_2021_ = _args[11];
lean_object* v_toBind_2022_ = _args[12];
lean_object* v_k_2023_ = _args[13];
lean_object* v___f_2024_ = _args[14];
lean_object* v___f_2025_ = _args[15];
lean_object* v___x_2026_ = _args[16];
lean_object* v_inst_2027_ = _args[17];
lean_object* v_toPure_2028_ = _args[18];
lean_object* v_oldTraces_2029_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_2030_; uint8_t v_clsEnabled_boxed_2031_; lean_object* v_res_2032_; 
v_collapsed_boxed_2030_ = lean_unbox(v_collapsed_2017_);
v_clsEnabled_boxed_2031_ = lean_unbox(v_clsEnabled_2020_);
v_res_2032_ = l_Lean_withTraceNode_x27___redArg___lam__11(v_inst_2010_, v_inst_2011_, v_inst_2012_, v_inst_2013_, v_inst_2014_, v___f_2015_, v_cls_2016_, v_collapsed_boxed_2030_, v_tag_2018_, v_opts_2019_, v_clsEnabled_boxed_2031_, v_msg_2021_, v_toBind_2022_, v_k_2023_, v___f_2024_, v___f_2025_, v___x_2026_, v_inst_2027_, v_toPure_2028_, v_oldTraces_2029_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v___f_2038_, lean_object* v_cls_2039_, uint8_t v_collapsed_2040_, lean_object* v_tag_2041_, lean_object* v_opts_2042_, lean_object* v_msg_2043_, lean_object* v_toBind_2044_, lean_object* v_k_2045_, lean_object* v___f_2046_, lean_object* v___f_2047_, lean_object* v___x_2048_, lean_object* v_inst_2049_, lean_object* v_toPure_2050_, uint8_t v_clsEnabled_2051_){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___f_2054_; 
v___x_2052_ = lean_box(v_collapsed_2040_);
v___x_2053_ = lean_box(v_clsEnabled_2051_);
lean_inc_ref(v___x_2048_);
lean_inc(v_k_2045_);
lean_inc(v_toBind_2044_);
lean_inc_ref(v_opts_2042_);
lean_inc_ref(v_inst_2035_);
lean_inc_ref(v_inst_2034_);
v___f_2054_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__11___boxed), 20, 19);
lean_closure_set(v___f_2054_, 0, v_inst_2033_);
lean_closure_set(v___f_2054_, 1, v_inst_2034_);
lean_closure_set(v___f_2054_, 2, v_inst_2035_);
lean_closure_set(v___f_2054_, 3, v_inst_2036_);
lean_closure_set(v___f_2054_, 4, v_inst_2037_);
lean_closure_set(v___f_2054_, 5, v___f_2038_);
lean_closure_set(v___f_2054_, 6, v_cls_2039_);
lean_closure_set(v___f_2054_, 7, v___x_2052_);
lean_closure_set(v___f_2054_, 8, v_tag_2041_);
lean_closure_set(v___f_2054_, 9, v_opts_2042_);
lean_closure_set(v___f_2054_, 10, v___x_2053_);
lean_closure_set(v___f_2054_, 11, v_msg_2043_);
lean_closure_set(v___f_2054_, 12, v_toBind_2044_);
lean_closure_set(v___f_2054_, 13, v_k_2045_);
lean_closure_set(v___f_2054_, 14, v___f_2046_);
lean_closure_set(v___f_2054_, 15, v___f_2047_);
lean_closure_set(v___f_2054_, 16, v___x_2048_);
lean_closure_set(v___f_2054_, 17, v_inst_2049_);
lean_closure_set(v___f_2054_, 18, v_toPure_2050_);
if (v_clsEnabled_2051_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2058_ = l_Lean_trace_profiler;
v___x_2059_ = l_Lean_Option_get___redArg(v___x_2048_, v_opts_2042_, v___x_2058_);
lean_dec_ref(v_opts_2042_);
v___x_2060_ = lean_unbox(v___x_2059_);
lean_dec(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec_ref(v___f_2054_);
lean_dec(v_toBind_2044_);
lean_dec_ref(v_inst_2035_);
lean_dec_ref(v_inst_2034_);
return v_k_2045_;
}
else
{
lean_dec(v_k_2045_);
goto v___jp_2055_;
}
}
else
{
lean_dec_ref(v___x_2048_);
lean_dec(v_k_2045_);
lean_dec_ref(v_opts_2042_);
goto v___jp_2055_;
}
v___jp_2055_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_2034_, v_inst_2035_);
v___x_2057_ = lean_apply_4(v_toBind_2044_, lean_box(0), lean_box(0), v___x_2056_, v___f_2054_);
return v___x_2057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_inst_2061_ = _args[0];
lean_object* v_inst_2062_ = _args[1];
lean_object* v_inst_2063_ = _args[2];
lean_object* v_inst_2064_ = _args[3];
lean_object* v_inst_2065_ = _args[4];
lean_object* v___f_2066_ = _args[5];
lean_object* v_cls_2067_ = _args[6];
lean_object* v_collapsed_2068_ = _args[7];
lean_object* v_tag_2069_ = _args[8];
lean_object* v_opts_2070_ = _args[9];
lean_object* v_msg_2071_ = _args[10];
lean_object* v_toBind_2072_ = _args[11];
lean_object* v_k_2073_ = _args[12];
lean_object* v___f_2074_ = _args[13];
lean_object* v___f_2075_ = _args[14];
lean_object* v___x_2076_ = _args[15];
lean_object* v_inst_2077_ = _args[16];
lean_object* v_toPure_2078_ = _args[17];
lean_object* v_clsEnabled_2079_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_2080_; uint8_t v_clsEnabled_boxed_2081_; lean_object* v_res_2082_; 
v_collapsed_boxed_2080_ = lean_unbox(v_collapsed_2068_);
v_clsEnabled_boxed_2081_ = lean_unbox(v_clsEnabled_2079_);
v_res_2082_ = l_Lean_withTraceNode_x27___redArg___lam__12(v_inst_2061_, v_inst_2062_, v_inst_2063_, v_inst_2064_, v_inst_2065_, v___f_2066_, v_cls_2067_, v_collapsed_boxed_2080_, v_tag_2069_, v_opts_2070_, v_msg_2071_, v_toBind_2072_, v_k_2073_, v___f_2074_, v___f_2075_, v___x_2076_, v_inst_2077_, v_toPure_2078_, v_clsEnabled_boxed_2081_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object* v_k_2083_, lean_object* v_inst_2084_, lean_object* v_inst_2085_, lean_object* v_inst_2086_, lean_object* v_inst_2087_, lean_object* v_inst_2088_, lean_object* v___f_2089_, lean_object* v_cls_2090_, uint8_t v_collapsed_2091_, lean_object* v_tag_2092_, lean_object* v_msg_2093_, lean_object* v_toBind_2094_, lean_object* v___f_2095_, lean_object* v___f_2096_, lean_object* v___x_2097_, lean_object* v_inst_2098_, lean_object* v_toPure_2099_, lean_object* v___f_2100_, lean_object* v_opts_2101_){
_start:
{
uint8_t v_hasTrace_2102_; 
v_hasTrace_2102_ = lean_ctor_get_uint8(v_opts_2101_, sizeof(void*)*1);
if (v_hasTrace_2102_ == 0)
{
lean_dec_ref(v_opts_2101_);
lean_dec(v___f_2100_);
lean_dec(v_toPure_2099_);
lean_dec(v_inst_2098_);
lean_dec_ref(v___x_2097_);
lean_dec(v___f_2096_);
lean_dec(v___f_2095_);
lean_dec(v_toBind_2094_);
lean_dec(v_msg_2093_);
lean_dec_ref(v_tag_2092_);
lean_dec(v_cls_2090_);
lean_dec_ref(v___f_2089_);
lean_dec(v_inst_2088_);
lean_dec_ref(v_inst_2087_);
lean_dec_ref(v_inst_2086_);
lean_dec_ref(v_inst_2085_);
lean_dec_ref(v_inst_2084_);
return v_k_2083_;
}
else
{
lean_object* v_getInheritedTraceOptions_2103_; lean_object* v___x_2104_; lean_object* v___f_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_getInheritedTraceOptions_2103_ = lean_ctor_get(v_inst_2084_, 2);
lean_inc(v_getInheritedTraceOptions_2103_);
v___x_2104_ = lean_box(v_collapsed_2091_);
lean_inc_n(v_toBind_2094_, 2);
v___f_2105_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__12___boxed), 19, 18);
lean_closure_set(v___f_2105_, 0, v_inst_2085_);
lean_closure_set(v___f_2105_, 1, v_inst_2086_);
lean_closure_set(v___f_2105_, 2, v_inst_2084_);
lean_closure_set(v___f_2105_, 3, v_inst_2087_);
lean_closure_set(v___f_2105_, 4, v_inst_2088_);
lean_closure_set(v___f_2105_, 5, v___f_2089_);
lean_closure_set(v___f_2105_, 6, v_cls_2090_);
lean_closure_set(v___f_2105_, 7, v___x_2104_);
lean_closure_set(v___f_2105_, 8, v_tag_2092_);
lean_closure_set(v___f_2105_, 9, v_opts_2101_);
lean_closure_set(v___f_2105_, 10, v_msg_2093_);
lean_closure_set(v___f_2105_, 11, v_toBind_2094_);
lean_closure_set(v___f_2105_, 12, v_k_2083_);
lean_closure_set(v___f_2105_, 13, v___f_2095_);
lean_closure_set(v___f_2105_, 14, v___f_2096_);
lean_closure_set(v___f_2105_, 15, v___x_2097_);
lean_closure_set(v___f_2105_, 16, v_inst_2098_);
lean_closure_set(v___f_2105_, 17, v_toPure_2099_);
v___x_2106_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2103_, v___f_2100_);
v___x_2107_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v___x_2106_, v___f_2105_);
return v___x_2107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_k_2108_ = _args[0];
lean_object* v_inst_2109_ = _args[1];
lean_object* v_inst_2110_ = _args[2];
lean_object* v_inst_2111_ = _args[3];
lean_object* v_inst_2112_ = _args[4];
lean_object* v_inst_2113_ = _args[5];
lean_object* v___f_2114_ = _args[6];
lean_object* v_cls_2115_ = _args[7];
lean_object* v_collapsed_2116_ = _args[8];
lean_object* v_tag_2117_ = _args[9];
lean_object* v_msg_2118_ = _args[10];
lean_object* v_toBind_2119_ = _args[11];
lean_object* v___f_2120_ = _args[12];
lean_object* v___f_2121_ = _args[13];
lean_object* v___x_2122_ = _args[14];
lean_object* v_inst_2123_ = _args[15];
lean_object* v_toPure_2124_ = _args[16];
lean_object* v___f_2125_ = _args[17];
lean_object* v_opts_2126_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_2127_; lean_object* v_res_2128_; 
v_collapsed_boxed_2127_ = lean_unbox(v_collapsed_2116_);
v_res_2128_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_k_2108_, v_inst_2109_, v_inst_2110_, v_inst_2111_, v_inst_2112_, v_inst_2113_, v___f_2114_, v_cls_2115_, v_collapsed_boxed_2127_, v_tag_2117_, v_msg_2118_, v_toBind_2119_, v___f_2120_, v___f_2121_, v___x_2122_, v_inst_2123_, v_toPure_2124_, v___f_2125_, v_opts_2126_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_cls_2137_, lean_object* v_k_2138_, uint8_t v_collapsed_2139_, lean_object* v_tag_2140_){
_start:
{
lean_object* v_toApplicative_2141_; lean_object* v_toFunctor_2142_; lean_object* v_toBind_2143_; lean_object* v_toPure_2144_; lean_object* v_map_2145_; lean_object* v___x_2146_; lean_object* v_getOptionsUnrestricted_2147_; lean_object* v___f_2148_; lean_object* v___f_2149_; lean_object* v___f_2150_; lean_object* v_msg_2151_; lean_object* v___f_2152_; lean_object* v___f_2153_; lean_object* v___x_2154_; lean_object* v___f_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_toApplicative_2141_ = lean_ctor_get(v_inst_2130_, 0);
v_toFunctor_2142_ = lean_ctor_get(v_toApplicative_2141_, 0);
v_toBind_2143_ = lean_ctor_get(v_inst_2130_, 1);
lean_inc_n(v_toBind_2143_, 3);
v_toPure_2144_ = lean_ctor_get(v_toApplicative_2141_, 1);
lean_inc_n(v_toPure_2144_, 5);
v_map_2145_ = lean_ctor_get(v_toFunctor_2142_, 0);
lean_inc(v_map_2145_);
v___x_2146_ = l_Lean_KVMap_instValueBool;
v_getOptionsUnrestricted_2147_ = lean_ctor_get(v_inst_2134_, 1);
lean_inc_n(v_getOptionsUnrestricted_2147_, 2);
lean_dec_ref(v_inst_2134_);
v___f_2148_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v___f_2149_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2149_, 0, v_toPure_2144_);
v___f_2150_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2150_, 0, v_toPure_2144_);
v_msg_2151_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3), 2, 1);
lean_closure_set(v_msg_2151_, 0, v_toPure_2144_);
v___f_2152_ = ((lean_object*)(l_Lean_instExceptToTraceResult___redArg___closed__0));
lean_inc(v_cls_2137_);
v___f_2153_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__12), 5, 4);
lean_closure_set(v___f_2153_, 0, v_toPure_2144_);
lean_closure_set(v___f_2153_, 1, v_cls_2137_);
lean_closure_set(v___f_2153_, 2, v_toBind_2143_);
lean_closure_set(v___f_2153_, 3, v_getOptionsUnrestricted_2147_);
v___x_2154_ = lean_box(v_collapsed_2139_);
v___f_2155_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 19, 18);
lean_closure_set(v___f_2155_, 0, v_k_2138_);
lean_closure_set(v___f_2155_, 1, v_inst_2131_);
lean_closure_set(v___f_2155_, 2, v_inst_2135_);
lean_closure_set(v___f_2155_, 3, v_inst_2130_);
lean_closure_set(v___f_2155_, 4, v_inst_2132_);
lean_closure_set(v___f_2155_, 5, v_inst_2133_);
lean_closure_set(v___f_2155_, 6, v___f_2152_);
lean_closure_set(v___f_2155_, 7, v_cls_2137_);
lean_closure_set(v___f_2155_, 8, v___x_2154_);
lean_closure_set(v___f_2155_, 9, v_tag_2140_);
lean_closure_set(v___f_2155_, 10, v_msg_2151_);
lean_closure_set(v___f_2155_, 11, v_toBind_2143_);
lean_closure_set(v___f_2155_, 12, v___f_2149_);
lean_closure_set(v___f_2155_, 13, v___f_2150_);
lean_closure_set(v___f_2155_, 14, v___x_2146_);
lean_closure_set(v___f_2155_, 15, v_inst_2136_);
lean_closure_set(v___f_2155_, 16, v_toPure_2144_);
lean_closure_set(v___f_2155_, 17, v___f_2153_);
v___x_2156_ = lean_apply_4(v_toBind_2143_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_2147_, v___f_2155_);
v___x_2157_ = lean_apply_4(v_map_2145_, lean_box(0), lean_box(0), v___f_2148_, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object* v_inst_2158_, lean_object* v_inst_2159_, lean_object* v_inst_2160_, lean_object* v_inst_2161_, lean_object* v_inst_2162_, lean_object* v_inst_2163_, lean_object* v_inst_2164_, lean_object* v_cls_2165_, lean_object* v_k_2166_, lean_object* v_collapsed_2167_, lean_object* v_tag_2168_){
_start:
{
uint8_t v_collapsed_boxed_2169_; lean_object* v_res_2170_; 
v_collapsed_boxed_2169_ = lean_unbox(v_collapsed_2167_);
v_res_2170_ = l_Lean_withTraceNode_x27___redArg(v_inst_2158_, v_inst_2159_, v_inst_2160_, v_inst_2161_, v_inst_2162_, v_inst_2163_, v_inst_2164_, v_cls_2165_, v_k_2166_, v_collapsed_boxed_2169_, v_tag_2168_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object* v_00_u03b1_2171_, lean_object* v_m_2172_, lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_inst_2179_, lean_object* v_cls_2180_, lean_object* v_k_2181_, uint8_t v_collapsed_2182_, lean_object* v_tag_2183_){
_start:
{
lean_object* v_toApplicative_2184_; lean_object* v_toFunctor_2185_; lean_object* v_toBind_2186_; lean_object* v_toPure_2187_; lean_object* v_map_2188_; lean_object* v___x_2189_; lean_object* v_getOptionsUnrestricted_2190_; lean_object* v___f_2191_; lean_object* v___f_2192_; lean_object* v___f_2193_; lean_object* v_msg_2194_; lean_object* v___f_2195_; lean_object* v___f_2196_; lean_object* v___x_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v_toApplicative_2184_ = lean_ctor_get(v_inst_2173_, 0);
v_toFunctor_2185_ = lean_ctor_get(v_toApplicative_2184_, 0);
v_toBind_2186_ = lean_ctor_get(v_inst_2173_, 1);
lean_inc_n(v_toBind_2186_, 3);
v_toPure_2187_ = lean_ctor_get(v_toApplicative_2184_, 1);
lean_inc_n(v_toPure_2187_, 5);
v_map_2188_ = lean_ctor_get(v_toFunctor_2185_, 0);
lean_inc(v_map_2188_);
v___x_2189_ = l_Lean_KVMap_instValueBool;
v_getOptionsUnrestricted_2190_ = lean_ctor_get(v_inst_2177_, 1);
lean_inc_n(v_getOptionsUnrestricted_2190_, 2);
lean_dec_ref(v_inst_2177_);
v___f_2191_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v___f_2192_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2192_, 0, v_toPure_2187_);
v___f_2193_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2193_, 0, v_toPure_2187_);
v_msg_2194_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3), 2, 1);
lean_closure_set(v_msg_2194_, 0, v_toPure_2187_);
v___f_2195_ = ((lean_object*)(l_Lean_instExceptToTraceResult___redArg___closed__0));
lean_inc(v_cls_2180_);
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__12), 5, 4);
lean_closure_set(v___f_2196_, 0, v_toPure_2187_);
lean_closure_set(v___f_2196_, 1, v_cls_2180_);
lean_closure_set(v___f_2196_, 2, v_toBind_2186_);
lean_closure_set(v___f_2196_, 3, v_getOptionsUnrestricted_2190_);
v___x_2197_ = lean_box(v_collapsed_2182_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 19, 18);
lean_closure_set(v___f_2198_, 0, v_k_2181_);
lean_closure_set(v___f_2198_, 1, v_inst_2174_);
lean_closure_set(v___f_2198_, 2, v_inst_2178_);
lean_closure_set(v___f_2198_, 3, v_inst_2173_);
lean_closure_set(v___f_2198_, 4, v_inst_2175_);
lean_closure_set(v___f_2198_, 5, v_inst_2176_);
lean_closure_set(v___f_2198_, 6, v___f_2195_);
lean_closure_set(v___f_2198_, 7, v_cls_2180_);
lean_closure_set(v___f_2198_, 8, v___x_2197_);
lean_closure_set(v___f_2198_, 9, v_tag_2183_);
lean_closure_set(v___f_2198_, 10, v_msg_2194_);
lean_closure_set(v___f_2198_, 11, v_toBind_2186_);
lean_closure_set(v___f_2198_, 12, v___f_2192_);
lean_closure_set(v___f_2198_, 13, v___f_2193_);
lean_closure_set(v___f_2198_, 14, v___x_2189_);
lean_closure_set(v___f_2198_, 15, v_inst_2179_);
lean_closure_set(v___f_2198_, 16, v_toPure_2187_);
lean_closure_set(v___f_2198_, 17, v___f_2196_);
v___x_2199_ = lean_apply_4(v_toBind_2186_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_2190_, v___f_2198_);
v___x_2200_ = lean_apply_4(v_map_2188_, lean_box(0), lean_box(0), v___f_2191_, v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object* v_00_u03b1_2201_, lean_object* v_m_2202_, lean_object* v_inst_2203_, lean_object* v_inst_2204_, lean_object* v_inst_2205_, lean_object* v_inst_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v_cls_2210_, lean_object* v_k_2211_, lean_object* v_collapsed_2212_, lean_object* v_tag_2213_){
_start:
{
uint8_t v_collapsed_boxed_2214_; lean_object* v_res_2215_; 
v_collapsed_boxed_2214_ = lean_unbox(v_collapsed_2212_);
v_res_2215_ = l_Lean_withTraceNode_x27(v_00_u03b1_2201_, v_m_2202_, v_inst_2203_, v_inst_2204_, v_inst_2205_, v_inst_2206_, v_inst_2207_, v_inst_2208_, v_inst_2209_, v_cls_2210_, v_k_2211_, v_collapsed_boxed_2214_, v_tag_2213_);
return v_res_2215_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__4(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__3));
v___x_2225_ = l_Lean_mkAtom(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__5(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__4, &l_Lean_registerTraceClass___auto__1___closed__4_once, _init_l_Lean_registerTraceClass___auto__1___closed__4);
v___x_2227_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2228_ = lean_array_push(v___x_2227_, v___x_2226_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__6(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2229_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__5, &l_Lean_registerTraceClass___auto__1___closed__5_once, _init_l_Lean_registerTraceClass___auto__1___closed__5);
v___x_2230_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__2));
v___x_2231_ = lean_box(2);
v___x_2232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2230_);
lean_ctor_set(v___x_2232_, 2, v___x_2229_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__7(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__6, &l_Lean_registerTraceClass___auto__1___closed__6_once, _init_l_Lean_registerTraceClass___auto__1___closed__6);
v___x_2234_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_2235_ = lean_array_push(v___x_2234_, v___x_2233_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2236_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__7, &l_Lean_registerTraceClass___auto__1___closed__7_once, _init_l_Lean_registerTraceClass___auto__1___closed__7);
v___x_2237_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_2238_ = lean_box(2);
v___x_2239_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v___x_2237_);
lean_ctor_set(v___x_2239_, 2, v___x_2236_);
return v___x_2239_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2240_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__8, &l_Lean_registerTraceClass___auto__1___closed__8_once, _init_l_Lean_registerTraceClass___auto__1___closed__8);
v___x_2241_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2242_ = lean_array_push(v___x_2241_, v___x_2240_);
return v___x_2242_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2243_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__9, &l_Lean_registerTraceClass___auto__1___closed__9_once, _init_l_Lean_registerTraceClass___auto__1___closed__9);
v___x_2244_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2245_ = lean_box(2);
v___x_2246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
lean_ctor_set(v___x_2246_, 1, v___x_2244_);
lean_ctor_set(v___x_2246_, 2, v___x_2243_);
return v___x_2246_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__11(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__10, &l_Lean_registerTraceClass___auto__1___closed__10_once, _init_l_Lean_registerTraceClass___auto__1___closed__10);
v___x_2248_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2249_ = lean_array_push(v___x_2248_, v___x_2247_);
return v___x_2249_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2250_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__11, &l_Lean_registerTraceClass___auto__1___closed__11_once, _init_l_Lean_registerTraceClass___auto__1___closed__11);
v___x_2251_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_2252_ = lean_box(2);
v___x_2253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
lean_ctor_set(v___x_2253_, 1, v___x_2251_);
lean_ctor_set(v___x_2253_, 2, v___x_2250_);
return v___x_2253_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__12, &l_Lean_registerTraceClass___auto__1___closed__12_once, _init_l_Lean_registerTraceClass___auto__1___closed__12);
v___x_2255_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2256_ = lean_array_push(v___x_2255_, v___x_2254_);
return v___x_2256_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2257_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__13, &l_Lean_registerTraceClass___auto__1___closed__13_once, _init_l_Lean_registerTraceClass___auto__1___closed__13);
v___x_2258_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_2259_ = lean_box(2);
v___x_2260_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
lean_ctor_set(v___x_2260_, 1, v___x_2258_);
lean_ctor_set(v___x_2260_, 2, v___x_2257_);
return v___x_2260_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1(void){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__14, &l_Lean_registerTraceClass___auto__1___closed__14_once, _init_l_Lean_registerTraceClass___auto__1___closed__14);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2262_, lean_object* v_x_2263_){
_start:
{
if (lean_obj_tag(v_x_2263_) == 0)
{
return v_x_2262_;
}
else
{
lean_object* v_key_2264_; lean_object* v_value_2265_; lean_object* v_tail_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2292_; 
v_key_2264_ = lean_ctor_get(v_x_2263_, 0);
v_value_2265_ = lean_ctor_get(v_x_2263_, 1);
v_tail_2266_ = lean_ctor_get(v_x_2263_, 2);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_x_2263_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2268_ = v_x_2263_;
v_isShared_2269_ = v_isSharedCheck_2292_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_tail_2266_);
lean_inc(v_value_2265_);
lean_inc(v_key_2264_);
lean_dec(v_x_2263_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2292_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; uint64_t v___y_2272_; 
v___x_2270_ = lean_array_get_size(v_x_2262_);
if (lean_obj_tag(v_key_2264_) == 0)
{
uint64_t v___x_2290_; 
v___x_2290_ = 1723ULL;
v___y_2272_ = v___x_2290_;
goto v___jp_2271_;
}
else
{
uint64_t v_hash_2291_; 
v_hash_2291_ = lean_ctor_get_uint64(v_key_2264_, sizeof(void*)*2);
v___y_2272_ = v_hash_2291_;
goto v___jp_2271_;
}
v___jp_2271_:
{
uint64_t v___x_2273_; uint64_t v___x_2274_; uint64_t v_fold_2275_; uint64_t v___x_2276_; uint64_t v___x_2277_; uint64_t v___x_2278_; size_t v___x_2279_; size_t v___x_2280_; size_t v___x_2281_; size_t v___x_2282_; size_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2273_ = 32ULL;
v___x_2274_ = lean_uint64_shift_right(v___y_2272_, v___x_2273_);
v_fold_2275_ = lean_uint64_xor(v___y_2272_, v___x_2274_);
v___x_2276_ = 16ULL;
v___x_2277_ = lean_uint64_shift_right(v_fold_2275_, v___x_2276_);
v___x_2278_ = lean_uint64_xor(v_fold_2275_, v___x_2277_);
v___x_2279_ = lean_uint64_to_usize(v___x_2278_);
v___x_2280_ = lean_usize_of_nat(v___x_2270_);
v___x_2281_ = ((size_t)1ULL);
v___x_2282_ = lean_usize_sub(v___x_2280_, v___x_2281_);
v___x_2283_ = lean_usize_land(v___x_2279_, v___x_2282_);
v___x_2284_ = lean_array_uget_borrowed(v_x_2262_, v___x_2283_);
lean_inc(v___x_2284_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 2, v___x_2284_);
v___x_2286_ = v___x_2268_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_key_2264_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_value_2265_);
lean_ctor_set(v_reuseFailAlloc_2289_, 2, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_array_uset(v_x_2262_, v___x_2283_, v___x_2286_);
v_x_2262_ = v___x_2287_;
v_x_2263_ = v_tail_2266_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object* v_i_2293_, lean_object* v_source_2294_, lean_object* v_target_2295_){
_start:
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = lean_array_get_size(v_source_2294_);
v___x_2297_ = lean_nat_dec_lt(v_i_2293_, v___x_2296_);
if (v___x_2297_ == 0)
{
lean_dec_ref(v_source_2294_);
lean_dec(v_i_2293_);
return v_target_2295_;
}
else
{
lean_object* v_es_2298_; lean_object* v___x_2299_; lean_object* v_source_2300_; lean_object* v_target_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v_es_2298_ = lean_array_fget(v_source_2294_, v_i_2293_);
v___x_2299_ = lean_box(0);
v_source_2300_ = lean_array_fset(v_source_2294_, v_i_2293_, v___x_2299_);
v_target_2301_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_2295_, v_es_2298_);
v___x_2302_ = lean_unsigned_to_nat(1u);
v___x_2303_ = lean_nat_add(v_i_2293_, v___x_2302_);
lean_dec(v_i_2293_);
v_i_2293_ = v___x_2303_;
v_source_2294_ = v_source_2300_;
v_target_2295_ = v_target_2301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object* v_data_2305_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v_nbuckets_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2306_ = lean_array_get_size(v_data_2305_);
v___x_2307_ = lean_unsigned_to_nat(2u);
v_nbuckets_2308_ = lean_nat_mul(v___x_2306_, v___x_2307_);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_box(0);
v___x_2311_ = lean_mk_array(v_nbuckets_2308_, v___x_2310_);
v___x_2312_ = lean_array_propagate_mark(v_data_2305_, v___x_2311_);
v___x_2313_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_2309_, v_data_2305_, v___x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object* v_m_2314_, lean_object* v_a_2315_, lean_object* v_b_2316_){
_start:
{
lean_object* v_size_2317_; lean_object* v_buckets_2318_; lean_object* v___x_2319_; uint64_t v___y_2321_; 
v_size_2317_ = lean_ctor_get(v_m_2314_, 0);
v_buckets_2318_ = lean_ctor_get(v_m_2314_, 1);
v___x_2319_ = lean_array_get_size(v_buckets_2318_);
if (lean_obj_tag(v_a_2315_) == 0)
{
uint64_t v___x_2358_; 
v___x_2358_ = 1723ULL;
v___y_2321_ = v___x_2358_;
goto v___jp_2320_;
}
else
{
uint64_t v_hash_2359_; 
v_hash_2359_ = lean_ctor_get_uint64(v_a_2315_, sizeof(void*)*2);
v___y_2321_ = v_hash_2359_;
goto v___jp_2320_;
}
v___jp_2320_:
{
uint64_t v___x_2322_; uint64_t v___x_2323_; uint64_t v_fold_2324_; uint64_t v___x_2325_; uint64_t v___x_2326_; uint64_t v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; size_t v___x_2330_; size_t v___x_2331_; size_t v___x_2332_; lean_object* v_bkt_2333_; uint8_t v___x_2334_; 
v___x_2322_ = 32ULL;
v___x_2323_ = lean_uint64_shift_right(v___y_2321_, v___x_2322_);
v_fold_2324_ = lean_uint64_xor(v___y_2321_, v___x_2323_);
v___x_2325_ = 16ULL;
v___x_2326_ = lean_uint64_shift_right(v_fold_2324_, v___x_2325_);
v___x_2327_ = lean_uint64_xor(v_fold_2324_, v___x_2326_);
v___x_2328_ = lean_uint64_to_usize(v___x_2327_);
v___x_2329_ = lean_usize_of_nat(v___x_2319_);
v___x_2330_ = ((size_t)1ULL);
v___x_2331_ = lean_usize_sub(v___x_2329_, v___x_2330_);
v___x_2332_ = lean_usize_land(v___x_2328_, v___x_2331_);
v_bkt_2333_ = lean_array_uget_borrowed(v_buckets_2318_, v___x_2332_);
v___x_2334_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_2315_, v_bkt_2333_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2355_; 
lean_inc_ref(v_buckets_2318_);
lean_inc(v_size_2317_);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_m_2314_);
if (v_isSharedCheck_2355_ == 0)
{
lean_object* v_unused_2356_; lean_object* v_unused_2357_; 
v_unused_2356_ = lean_ctor_get(v_m_2314_, 1);
lean_dec(v_unused_2356_);
v_unused_2357_ = lean_ctor_get(v_m_2314_, 0);
lean_dec(v_unused_2357_);
v___x_2336_ = v_m_2314_;
v_isShared_2337_ = v_isSharedCheck_2355_;
goto v_resetjp_2335_;
}
else
{
lean_dec(v_m_2314_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2355_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v_size_x27_2339_; lean_object* v___x_2340_; lean_object* v_buckets_x27_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2338_ = lean_unsigned_to_nat(1u);
v_size_x27_2339_ = lean_nat_add(v_size_2317_, v___x_2338_);
lean_dec(v_size_2317_);
lean_inc(v_bkt_2333_);
v___x_2340_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2340_, 0, v_a_2315_);
lean_ctor_set(v___x_2340_, 1, v_b_2316_);
lean_ctor_set(v___x_2340_, 2, v_bkt_2333_);
v_buckets_x27_2341_ = lean_array_uset(v_buckets_2318_, v___x_2332_, v___x_2340_);
v___x_2342_ = lean_unsigned_to_nat(4u);
v___x_2343_ = lean_nat_mul(v_size_x27_2339_, v___x_2342_);
v___x_2344_ = lean_unsigned_to_nat(3u);
v___x_2345_ = lean_nat_div(v___x_2343_, v___x_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_array_get_size(v_buckets_x27_2341_);
v___x_2347_ = lean_nat_dec_le(v___x_2345_, v___x_2346_);
lean_dec(v___x_2345_);
if (v___x_2347_ == 0)
{
lean_object* v_val_2348_; lean_object* v___x_2350_; 
v_val_2348_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_2341_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v_val_2348_);
lean_ctor_set(v___x_2336_, 0, v_size_x27_2339_);
v___x_2350_ = v___x_2336_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_size_x27_2339_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_val_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
else
{
lean_object* v___x_2353_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 1, v_buckets_x27_2341_);
lean_ctor_set(v___x_2336_, 0, v_size_x27_2339_);
v___x_2353_ = v___x_2336_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_size_x27_2339_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_buckets_x27_2341_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
else
{
lean_dec(v_b_2316_);
lean_dec(v_a_2315_);
return v_m_2314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object* v_traceClassName_2363_, uint8_t v_inherited_2364_, lean_object* v_ref_2365_){
_start:
{
lean_object* v___x_2367_; lean_object* v_optionName_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2367_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v_optionName_2368_ = l_Lean_Name_append(v___x_2367_, v_traceClassName_2363_);
v___x_2369_ = ((lean_object*)(l_Lean_registerTraceClass___closed__0));
v___x_2370_ = ((lean_object*)(l_Lean_registerTraceClass___closed__1));
v___x_2371_ = lean_box(0);
lean_inc_n(v_optionName_2368_, 2);
v___x_2372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2372_, 0, v_optionName_2368_);
lean_ctor_set(v___x_2372_, 1, v_ref_2365_);
lean_ctor_set(v___x_2372_, 2, v___x_2369_);
lean_ctor_set(v___x_2372_, 3, v___x_2370_);
lean_ctor_set(v___x_2372_, 4, v___x_2371_);
v___x_2373_ = lean_register_option(v_optionName_2368_, v___x_2372_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2389_; 
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; 
v_unused_2390_ = lean_ctor_get(v___x_2373_, 0);
lean_dec(v_unused_2390_);
v___x_2375_ = v___x_2373_;
v_isShared_2376_ = v_isSharedCheck_2389_;
goto v_resetjp_2374_;
}
else
{
lean_dec(v___x_2373_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2389_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
if (v_inherited_2364_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
lean_dec(v_optionName_2368_);
v___x_2377_ = lean_box(0);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2377_);
v___x_2379_ = v___x_2375_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2381_ = l_Lean_inheritedTraceOptions;
v___x_2382_ = lean_st_ref_take(v___x_2381_);
v___x_2383_ = lean_box(0);
v___x_2384_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2382_, v_optionName_2368_, v___x_2383_);
v___x_2385_ = lean_st_ref_put(v___x_2381_, v___x_2384_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2385_);
v___x_2387_ = v___x_2375_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_dec(v_optionName_2368_);
return v___x_2373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object* v_traceClassName_2391_, lean_object* v_inherited_2392_, lean_object* v_ref_2393_, lean_object* v_a_2394_){
_start:
{
uint8_t v_inherited_boxed_2395_; lean_object* v_res_2396_; 
v_inherited_boxed_2395_ = lean_unbox(v_inherited_2392_);
v_res_2396_ = l_Lean_registerTraceClass(v_traceClassName_2391_, v_inherited_boxed_2395_, v_ref_2393_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(lean_object* v_00_u03b2_2397_, lean_object* v_m_2398_, lean_object* v_a_2399_, lean_object* v_b_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v_m_2398_, v_a_2399_, v_b_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object* v_00_u03b2_2402_, lean_object* v_data_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_data_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2405_, lean_object* v_i_2406_, lean_object* v_source_2407_, lean_object* v_target_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_i_2406_, v_source_2407_, v_target_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2410_, lean_object* v_x_2411_, lean_object* v_x_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2411_, v_x_2412_);
return v___x_2413_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_2424_ = l_String_toRawSubstring_x27(v___x_2423_);
return v___x_2424_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13));
v___x_2431_ = l_String_toRawSubstring_x27(v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18));
v___x_2437_ = l_String_toRawSubstring_x27(v___x_2436_);
return v___x_2437_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31(void){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Array_mkArray0___redArg();
return v___x_2465_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40));
v___x_2492_ = l_String_toRawSubstring_x27(v___x_2491_);
return v___x_2492_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57));
v___x_2528_ = l_String_toRawSubstring_x27(v___x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object* v_id_2550_, lean_object* v_s_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v_msg_2651_; lean_object* v_quotContext_2652_; lean_object* v_currMacroScope_2653_; lean_object* v_ref_2654_; lean_object* v___y_2655_; lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
lean_inc(v_s_2551_);
v___x_2701_ = l_Lean_Syntax_getKind(v_s_2551_);
v___x_2702_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49));
v___x_2703_ = lean_name_eq(v___x_2701_, v___x_2702_);
lean_dec(v___x_2701_);
if (v___x_2703_ == 0)
{
lean_object* v_quotContext_2704_; lean_object* v_currMacroScope_2705_; lean_object* v_ref_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_quotContext_2704_ = lean_ctor_get(v_a_2552_, 1);
v_currMacroScope_2705_ = lean_ctor_get(v_a_2552_, 2);
v_ref_2706_ = lean_ctor_get(v_a_2552_, 5);
v___x_2707_ = l_Lean_SourceInfo_fromRef(v_ref_2706_, v___x_2703_);
v___x_2708_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51));
v___x_2709_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52));
v___x_2710_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
lean_inc_n(v___x_2707_, 8);
v___x_2711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2707_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2713_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2714_ = lean_box(0);
lean_inc_n(v_currMacroScope_2705_, 3);
lean_inc_n(v_quotContext_2704_, 3);
v___x_2715_ = l_Lean_addMacroScope(v_quotContext_2704_, v___x_2714_, v_currMacroScope_2705_);
v___x_2716_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55));
v___x_2717_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2707_);
lean_ctor_set(v___x_2717_, 1, v___x_2713_);
lean_ctor_set(v___x_2717_, 2, v___x_2715_);
lean_ctor_set(v___x_2717_, 3, v___x_2716_);
v___x_2718_ = l_Lean_Syntax_node1(v___x_2707_, v___x_2712_, v___x_2717_);
v___x_2719_ = l_Lean_Syntax_node2(v___x_2707_, v___x_2709_, v___x_2711_, v___x_2718_);
v___x_2720_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56));
v___x_2721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2707_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2723_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58);
v___x_2724_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59));
v___x_2725_ = l_Lean_addMacroScope(v_quotContext_2704_, v___x_2724_, v_currMacroScope_2705_);
v___x_2726_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64));
v___x_2727_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2707_);
lean_ctor_set(v___x_2727_, 1, v___x_2723_);
lean_ctor_set(v___x_2727_, 2, v___x_2725_);
lean_ctor_set(v___x_2727_, 3, v___x_2726_);
v___x_2728_ = l_Lean_Syntax_node1(v___x_2707_, v___x_2722_, v___x_2727_);
v___x_2729_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2707_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___x_2731_ = l_Lean_Syntax_node5(v___x_2707_, v___x_2708_, v___x_2719_, v_s_2551_, v___x_2721_, v___x_2728_, v___x_2730_);
v_msg_2651_ = v___x_2731_;
v_quotContext_2652_ = v_quotContext_2704_;
v_currMacroScope_2653_ = v_currMacroScope_2705_;
v_ref_2654_ = v_ref_2706_;
v___y_2655_ = v_a_2553_;
goto v___jp_2650_;
}
else
{
lean_object* v_quotContext_2732_; lean_object* v_currMacroScope_2733_; lean_object* v_ref_2734_; uint8_t v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_quotContext_2732_ = lean_ctor_get(v_a_2552_, 1);
v_currMacroScope_2733_ = lean_ctor_get(v_a_2552_, 2);
v_ref_2734_ = lean_ctor_get(v_a_2552_, 5);
v___x_2735_ = 0;
v___x_2736_ = l_Lean_SourceInfo_fromRef(v_ref_2734_, v___x_2735_);
v___x_2737_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66));
v___x_2738_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67));
lean_inc(v___x_2736_);
v___x_2739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2736_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = l_Lean_Syntax_node2(v___x_2736_, v___x_2737_, v___x_2739_, v_s_2551_);
lean_inc(v_currMacroScope_2733_);
lean_inc(v_quotContext_2732_);
v_msg_2651_ = v___x_2740_;
v_quotContext_2652_ = v_quotContext_2732_;
v_currMacroScope_2653_ = v_currMacroScope_2733_;
v_ref_2654_ = v_ref_2734_;
v___y_2655_ = v_a_2553_;
goto v___jp_2650_;
}
v___jp_2554_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_inc_n(v___y_2558_, 8);
lean_inc(v___y_2560_);
lean_inc_n(v___y_2576_, 30);
v___x_2579_ = l_Lean_Syntax_node5(v___y_2576_, v___y_2560_, v___y_2557_, v___y_2558_, v___y_2558_, v___y_2577_, v___y_2578_);
lean_inc(v___y_2565_);
v___x_2580_ = l_Lean_Syntax_node1(v___y_2576_, v___y_2565_, v___x_2579_);
lean_inc(v___y_2562_);
v___x_2581_ = l_Lean_Syntax_node4(v___y_2576_, v___y_2562_, v___y_2571_, v___y_2558_, v___y_2564_, v___x_2580_);
lean_inc_n(v___y_2574_, 3);
v___x_2582_ = l_Lean_Syntax_node2(v___y_2576_, v___y_2574_, v___x_2581_, v___y_2558_);
v___x_2583_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0));
lean_inc_ref_n(v___y_2561_, 7);
lean_inc_ref_n(v___y_2575_, 7);
lean_inc_ref_n(v___y_2567_, 10);
v___x_2584_ = l_Lean_Name_mkStr4(v___y_2567_, v___y_2575_, v___y_2561_, v___x_2583_);
v___x_2585_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1));
v___x_2586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___y_2576_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2));
v___x_2588_ = l_Lean_Name_mkStr4(v___y_2567_, v___y_2575_, v___y_2561_, v___x_2587_);
v___x_2589_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3));
v___x_2590_ = l_Lean_Name_mkStr4(v___y_2567_, v___y_2575_, v___y_2561_, v___x_2589_);
v___x_2591_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4));
v___x_2592_ = l_Lean_Name_mkStr4(v___y_2567_, v___y_2575_, v___y_2561_, v___x_2591_);
v___x_2593_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
v___x_2594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___y_2576_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2596_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2597_ = lean_box(0);
lean_inc_n(v___y_2563_, 2);
lean_inc_n(v___y_2573_, 2);
v___x_2598_ = l_Lean_addMacroScope(v___y_2573_, v___x_2597_, v___y_2563_);
v___x_2599_ = l_Lean_Name_mkStr1(v___y_2567_);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_inc_n(v___y_2572_, 2);
v___x_2601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___y_2572_);
v___x_2602_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2602_, 0, v___y_2576_);
lean_ctor_set(v___x_2602_, 1, v___x_2596_);
lean_ctor_set(v___x_2602_, 2, v___x_2598_);
lean_ctor_set(v___x_2602_, 3, v___x_2601_);
v___x_2603_ = l_Lean_Syntax_node1(v___y_2576_, v___x_2595_, v___x_2602_);
v___x_2604_ = l_Lean_Syntax_node2(v___y_2576_, v___x_2592_, v___x_2594_, v___x_2603_);
v___x_2605_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9));
v___x_2606_ = l_Lean_Name_mkStr4(v___y_2567_, v___y_2575_, v___y_2561_, v___x_2605_);
v___x_2607_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10));
v___x_2608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___y_2576_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11));
v___x_2610_ = l_Lean_Name_mkStr4(v___y_2567_, v___y_2575_, v___y_2561_, v___x_2609_);
v___x_2611_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12));
v___x_2612_ = l_Lean_Name_mkStr4(v___y_2567_, v___y_2575_, v___y_2561_, v___x_2611_);
v___x_2613_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14);
v___x_2614_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2615_ = l_Lean_Name_mkStr2(v___y_2567_, v___x_2614_);
lean_inc(v___x_2615_);
v___x_2616_ = l_Lean_addMacroScope(v___y_2573_, v___x_2615_, v___y_2563_);
v___x_2617_ = lean_box(0);
v___x_2618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2615_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
lean_ctor_set(v___x_2619_, 1, v___y_2572_);
v___x_2620_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2620_, 0, v___y_2576_);
lean_ctor_set(v___x_2620_, 1, v___x_2613_);
lean_ctor_set(v___x_2620_, 2, v___x_2616_);
lean_ctor_set(v___x_2620_, 3, v___x_2619_);
lean_inc(v___y_2570_);
lean_inc_n(v___y_2566_, 4);
v___x_2621_ = l_Lean_Syntax_node1(v___y_2576_, v___y_2566_, v___y_2570_);
lean_inc(v___x_2612_);
v___x_2622_ = l_Lean_Syntax_node2(v___y_2576_, v___x_2612_, v___x_2620_, v___x_2621_);
lean_inc(v___x_2610_);
v___x_2623_ = l_Lean_Syntax_node1(v___y_2576_, v___x_2610_, v___x_2622_);
v___x_2624_ = l_Lean_Syntax_node2(v___y_2576_, v___x_2606_, v___x_2608_, v___x_2623_);
v___x_2625_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___y_2576_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = l_Lean_Syntax_node3(v___y_2576_, v___x_2590_, v___x_2604_, v___x_2624_, v___x_2626_);
v___x_2628_ = l_Lean_Syntax_node2(v___y_2576_, v___x_2588_, v___y_2558_, v___x_2627_);
v___x_2629_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17));
v___x_2630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___y_2576_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19);
v___x_2632_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20));
v___x_2633_ = l_Lean_Name_mkStr2(v___y_2567_, v___x_2632_);
lean_inc(v___x_2633_);
v___x_2634_ = l_Lean_addMacroScope(v___y_2573_, v___x_2633_, v___y_2563_);
v___x_2635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2617_);
v___x_2636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v___y_2572_);
v___x_2637_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2637_, 0, v___y_2576_);
lean_ctor_set(v___x_2637_, 1, v___x_2631_);
lean_ctor_set(v___x_2637_, 2, v___x_2634_);
lean_ctor_set(v___x_2637_, 3, v___x_2636_);
v___x_2638_ = l_Lean_Syntax_node2(v___y_2576_, v___y_2566_, v___y_2570_, v___y_2568_);
v___x_2639_ = l_Lean_Syntax_node2(v___y_2576_, v___x_2612_, v___x_2637_, v___x_2638_);
v___x_2640_ = l_Lean_Syntax_node1(v___y_2576_, v___x_2610_, v___x_2639_);
v___x_2641_ = l_Lean_Syntax_node2(v___y_2576_, v___y_2574_, v___x_2640_, v___y_2558_);
v___x_2642_ = l_Lean_Syntax_node1(v___y_2576_, v___y_2566_, v___x_2641_);
lean_inc_n(v___y_2556_, 2);
v___x_2643_ = l_Lean_Syntax_node1(v___y_2576_, v___y_2556_, v___x_2642_);
v___x_2644_ = l_Lean_Syntax_node6(v___y_2576_, v___x_2584_, v___x_2586_, v___x_2628_, v___x_2630_, v___x_2643_, v___y_2558_, v___y_2558_);
v___x_2645_ = l_Lean_Syntax_node2(v___y_2576_, v___y_2574_, v___x_2644_, v___y_2558_);
v___x_2646_ = l_Lean_Syntax_node2(v___y_2576_, v___y_2566_, v___x_2582_, v___x_2645_);
v___x_2647_ = l_Lean_Syntax_node1(v___y_2576_, v___y_2556_, v___x_2646_);
lean_inc(v___y_2559_);
v___x_2648_ = l_Lean_Syntax_node2(v___y_2576_, v___y_2559_, v___y_2555_, v___x_2647_);
v___x_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
lean_ctor_set(v___x_2649_, 1, v___y_2569_);
return v___x_2649_;
}
v___jp_2650_:
{
uint8_t v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2656_ = 0;
v___x_2657_ = l_Lean_SourceInfo_fromRef(v_ref_2654_, v___x_2656_);
v___x_2658_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0));
v___x_2659_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1));
v___x_2660_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__0));
v___x_2661_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22));
v___x_2662_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23));
lean_inc_n(v___x_2657_, 7);
v___x_2663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2657_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25));
v___x_2665_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2666_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27));
v___x_2667_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2668_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
v___x_2669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2657_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31);
v___x_2671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2657_);
lean_ctor_set(v___x_2671_, 1, v___x_2665_);
lean_ctor_set(v___x_2671_, 2, v___x_2670_);
v___x_2672_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33));
lean_inc_ref(v___x_2671_);
v___x_2673_ = l_Lean_Syntax_node1(v___x_2657_, v___x_2672_, v___x_2671_);
v___x_2674_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35));
v___x_2675_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37));
v___x_2676_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39));
v___x_2677_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41);
v___x_2678_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42));
lean_inc(v_currMacroScope_2653_);
lean_inc(v_quotContext_2652_);
v___x_2679_ = l_Lean_addMacroScope(v_quotContext_2652_, v___x_2678_, v_currMacroScope_2653_);
v___x_2680_ = lean_box(0);
v___x_2681_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2657_);
lean_ctor_set(v___x_2681_, 1, v___x_2677_);
lean_ctor_set(v___x_2681_, 2, v___x_2679_);
lean_ctor_set(v___x_2681_, 3, v___x_2680_);
lean_inc_ref(v___x_2681_);
v___x_2682_ = l_Lean_Syntax_node1(v___x_2657_, v___x_2676_, v___x_2681_);
v___x_2683_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43));
v___x_2684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2657_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = l_Lean_Syntax_getId(v_id_2550_);
v___x_2686_ = l_Lean_Name_eraseMacroScopes(v___x_2685_);
lean_dec(v___x_2685_);
lean_inc(v___x_2686_);
v___x_2687_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2680_, v___x_2686_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_quoteNameMk(v___x_2686_);
v___y_2555_ = v___x_2663_;
v___y_2556_ = v___x_2664_;
v___y_2557_ = v___x_2682_;
v___y_2558_ = v___x_2671_;
v___y_2559_ = v___x_2661_;
v___y_2560_ = v___x_2675_;
v___y_2561_ = v___x_2660_;
v___y_2562_ = v___x_2667_;
v___y_2563_ = v_currMacroScope_2653_;
v___y_2564_ = v___x_2673_;
v___y_2565_ = v___x_2674_;
v___y_2566_ = v___x_2665_;
v___y_2567_ = v___x_2658_;
v___y_2568_ = v_msg_2651_;
v___y_2569_ = v___y_2655_;
v___y_2570_ = v___x_2681_;
v___y_2571_ = v___x_2669_;
v___y_2572_ = v___x_2680_;
v___y_2573_ = v_quotContext_2652_;
v___y_2574_ = v___x_2666_;
v___y_2575_ = v___x_2659_;
v___y_2576_ = v___x_2657_;
v___y_2577_ = v___x_2684_;
v___y_2578_ = v___x_2688_;
goto v___jp_2554_;
}
else
{
lean_object* v_val_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
lean_dec(v___x_2686_);
v_val_2689_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_val_2689_);
lean_dec_ref_known(v___x_2687_, 1);
v___x_2690_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45));
v___x_2691_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46));
v___x_2692_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47));
v___x_2693_ = lean_string_intercalate(v___x_2692_, v_val_2689_);
v___x_2694_ = lean_string_append(v___x_2691_, v___x_2693_);
lean_dec_ref(v___x_2693_);
v___x_2695_ = lean_box(2);
v___x_2696_ = l_Lean_Syntax_mkNameLit(v___x_2694_, v___x_2695_);
v___x_2697_ = lean_unsigned_to_nat(1u);
v___x_2698_ = lean_mk_empty_array_with_capacity(v___x_2697_);
v___x_2699_ = lean_array_push(v___x_2698_, v___x_2696_);
v___x_2700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2695_);
lean_ctor_set(v___x_2700_, 1, v___x_2690_);
lean_ctor_set(v___x_2700_, 2, v___x_2699_);
v___y_2555_ = v___x_2663_;
v___y_2556_ = v___x_2664_;
v___y_2557_ = v___x_2682_;
v___y_2558_ = v___x_2671_;
v___y_2559_ = v___x_2661_;
v___y_2560_ = v___x_2675_;
v___y_2561_ = v___x_2660_;
v___y_2562_ = v___x_2667_;
v___y_2563_ = v_currMacroScope_2653_;
v___y_2564_ = v___x_2673_;
v___y_2565_ = v___x_2674_;
v___y_2566_ = v___x_2665_;
v___y_2567_ = v___x_2658_;
v___y_2568_ = v_msg_2651_;
v___y_2569_ = v___y_2655_;
v___y_2570_ = v___x_2681_;
v___y_2571_ = v___x_2669_;
v___y_2572_ = v___x_2680_;
v___y_2573_ = v_quotContext_2652_;
v___y_2574_ = v___x_2666_;
v___y_2575_ = v___x_2659_;
v___y_2576_ = v___x_2657_;
v___y_2577_ = v___x_2684_;
v___y_2578_ = v___x_2700_;
goto v___jp_2554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object* v_id_2741_, lean_object* v_s_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v_id_2741_, v_s_2742_, v_a_2743_, v_a_2744_);
lean_dec_ref(v_a_2743_);
lean_dec(v_id_2741_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object* v_x_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v___x_2803_; uint8_t v___x_2804_; 
v___x_2803_ = ((lean_object*)(l_Lean_doElemTrace_x5b___x5d_____00__closed__1));
lean_inc(v_x_2800_);
v___x_2804_ = l_Lean_Syntax_isOfKind(v_x_2800_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
lean_dec(v_x_2800_);
v___x_2805_ = lean_box(1);
v___x_2806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
lean_ctor_set(v___x_2806_, 1, v_a_2802_);
return v___x_2806_;
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v_a_2812_; lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v___x_2807_ = lean_unsigned_to_nat(1u);
v___x_2808_ = l_Lean_Syntax_getArg(v_x_2800_, v___x_2807_);
v___x_2809_ = lean_unsigned_to_nat(3u);
v___x_2810_ = l_Lean_Syntax_getArg(v_x_2800_, v___x_2809_);
lean_dec(v_x_2800_);
v___x_2811_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v___x_2808_, v___x_2810_, v_a_2801_, v_a_2802_);
lean_dec(v___x_2808_);
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_a_2813_ = lean_ctor_get(v___x_2811_, 1);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2811_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2812_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object* v_x_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(v_x_2821_, v_a_2822_, v_a_2823_);
lean_dec_ref(v_a_2822_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object* v_inst_2825_, lean_object* v_inst_2826_, lean_object* v_inst_2827_, lean_object* v_inst_2828_, lean_object* v_always_2829_, lean_object* v_inst_2830_, lean_object* v_cls_2831_, uint8_t v_collapsed_2832_, lean_object* v_tag_2833_, lean_object* v_opts_2834_, uint8_t v_clsEnabled_2835_, lean_object* v_oldTraces_2836_, lean_object* v_ref_2837_, lean_object* v_msg_2838_, lean_object* v_resStartStop_2839_){
_start:
{
lean_object* v___x_2840_; lean_object* v_toBind_2841_; lean_object* v___x_2842_; lean_object* v_snd_2843_; lean_object* v_fst_2844_; lean_object* v_fst_2845_; lean_object* v_snd_2846_; lean_object* v___f_2847_; lean_object* v___f_2848_; lean_object* v_data_2850_; lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___y_2865_; double v___y_2870_; uint8_t v___x_2875_; 
v___x_2840_ = l_Lean_KVMap_instValueBool;
v_toBind_2841_ = lean_ctor_get(v_inst_2825_, 1);
lean_inc(v_toBind_2841_);
v___x_2842_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_2829_);
v_snd_2843_ = lean_ctor_get(v_resStartStop_2839_, 1);
lean_inc(v_snd_2843_);
v_fst_2844_ = lean_ctor_get(v_resStartStop_2839_, 0);
lean_inc_n(v_fst_2844_, 2);
lean_dec_ref(v_resStartStop_2839_);
v_fst_2845_ = lean_ctor_get(v_snd_2843_, 0);
lean_inc(v_fst_2845_);
v_snd_2846_ = lean_ctor_get(v_snd_2843_, 1);
lean_inc(v_snd_2846_);
lean_dec(v_snd_2843_);
lean_inc_ref(v_oldTraces_2836_);
v___f_2847_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2847_, 0, v_oldTraces_2836_);
lean_inc_ref(v_inst_2825_);
v___f_2848_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2848_, 0, v_inst_2825_);
lean_closure_set(v___f_2848_, 1, v___x_2842_);
lean_closure_set(v___f_2848_, 2, v_fst_2844_);
v___x_2853_ = l_Lean_trace_profiler;
v___x_2854_ = l_Lean_Option_get___redArg(v___x_2840_, v_opts_2834_, v___x_2853_);
v___x_2875_ = lean_unbox(v___x_2854_);
if (v___x_2875_ == 0)
{
uint8_t v___x_2876_; 
v___x_2876_ = lean_unbox(v___x_2854_);
v___y_2865_ = v___x_2876_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2877_ = l_Lean_KVMap_instValueNat;
v___x_2878_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2879_ = l_Lean_Option_get___redArg(v___x_2840_, v_opts_2834_, v___x_2878_);
v___x_2880_ = lean_unbox(v___x_2879_);
lean_dec(v___x_2879_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2882_; double v___x_2883_; double v___x_2884_; double v___x_2885_; 
v___x_2881_ = l_Lean_trace_profiler_threshold;
v___x_2882_ = l_Lean_Option_get___redArg(v___x_2877_, v_opts_2834_, v___x_2881_);
v___x_2883_ = lean_float_of_nat(v___x_2882_);
v___x_2884_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_2885_ = lean_float_div(v___x_2883_, v___x_2884_);
v___y_2870_ = v___x_2885_;
goto v___jp_2869_;
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2887_; double v___x_2888_; 
v___x_2886_ = l_Lean_trace_profiler_threshold;
v___x_2887_ = l_Lean_Option_get___redArg(v___x_2877_, v_opts_2834_, v___x_2886_);
v___x_2888_ = lean_float_of_nat(v___x_2887_);
v___y_2870_ = v___x_2888_;
goto v___jp_2869_;
}
}
v___jp_2849_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_2825_, v_inst_2826_, v_inst_2827_, v_inst_2828_, v_oldTraces_2836_, v_data_2850_, v_ref_2837_, v_msg_2838_);
v___x_2852_ = lean_apply_4(v_toBind_2841_, lean_box(0), lean_box(0), v___x_2851_, v___f_2848_);
return v___x_2852_;
}
v___jp_2855_:
{
lean_object* v_result_2856_; lean_object* v___x_2857_; double v___x_2858_; lean_object* v_data_2859_; uint8_t v___x_2860_; 
v_result_2856_ = lean_apply_1(v_inst_2830_, v_fst_2844_);
v___x_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2857_, 0, v_result_2856_);
v___x_2858_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_2833_);
lean_inc_ref(v___x_2857_);
lean_inc(v_cls_2831_);
v_data_2859_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2859_, 0, v_cls_2831_);
lean_ctor_set(v_data_2859_, 1, v___x_2857_);
lean_ctor_set(v_data_2859_, 2, v_tag_2833_);
lean_ctor_set_float(v_data_2859_, sizeof(void*)*3, v___x_2858_);
lean_ctor_set_float(v_data_2859_, sizeof(void*)*3 + 8, v___x_2858_);
lean_ctor_set_uint8(v_data_2859_, sizeof(void*)*3 + 16, v_collapsed_2832_);
v___x_2860_ = lean_unbox(v___x_2854_);
lean_dec(v___x_2854_);
if (v___x_2860_ == 0)
{
lean_dec_ref_known(v___x_2857_, 1);
lean_dec(v_snd_2846_);
lean_dec(v_fst_2845_);
lean_dec_ref(v_tag_2833_);
lean_dec(v_cls_2831_);
v_data_2850_ = v_data_2859_;
goto v___jp_2849_;
}
else
{
lean_object* v_data_2861_; double v___x_2862_; double v___x_2863_; 
lean_dec_ref_known(v_data_2859_, 3);
v_data_2861_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2861_, 0, v_cls_2831_);
lean_ctor_set(v_data_2861_, 1, v___x_2857_);
lean_ctor_set(v_data_2861_, 2, v_tag_2833_);
v___x_2862_ = lean_unbox_float(v_fst_2845_);
lean_dec(v_fst_2845_);
lean_ctor_set_float(v_data_2861_, sizeof(void*)*3, v___x_2862_);
v___x_2863_ = lean_unbox_float(v_snd_2846_);
lean_dec(v_snd_2846_);
lean_ctor_set_float(v_data_2861_, sizeof(void*)*3 + 8, v___x_2863_);
lean_ctor_set_uint8(v_data_2861_, sizeof(void*)*3 + 16, v_collapsed_2832_);
v_data_2850_ = v_data_2861_;
goto v___jp_2849_;
}
}
v___jp_2864_:
{
if (v_clsEnabled_2835_ == 0)
{
if (v___y_2865_ == 0)
{
lean_object* v_modifyTraceState_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_dec(v___x_2854_);
lean_dec(v_snd_2846_);
lean_dec(v_fst_2845_);
lean_dec(v_fst_2844_);
lean_dec_ref(v_msg_2838_);
lean_dec(v_ref_2837_);
lean_dec_ref(v_oldTraces_2836_);
lean_dec_ref(v_tag_2833_);
lean_dec(v_cls_2831_);
lean_dec_ref(v_inst_2830_);
lean_dec(v_inst_2828_);
lean_dec_ref(v_inst_2827_);
lean_dec_ref(v_inst_2825_);
v_modifyTraceState_2866_ = lean_ctor_get(v_inst_2826_, 0);
lean_inc(v_modifyTraceState_2866_);
lean_dec_ref(v_inst_2826_);
v___x_2867_ = lean_apply_1(v_modifyTraceState_2866_, v___f_2847_);
v___x_2868_ = lean_apply_4(v_toBind_2841_, lean_box(0), lean_box(0), v___x_2867_, v___f_2848_);
return v___x_2868_;
}
else
{
lean_dec_ref(v___f_2847_);
goto v___jp_2855_;
}
}
else
{
lean_dec_ref(v___f_2847_);
goto v___jp_2855_;
}
}
v___jp_2869_:
{
double v___x_2871_; double v___x_2872_; double v___x_2873_; uint8_t v___x_2874_; 
v___x_2871_ = lean_unbox_float(v_snd_2846_);
v___x_2872_ = lean_unbox_float(v_fst_2845_);
v___x_2873_ = lean_float_sub(v___x_2871_, v___x_2872_);
v___x_2874_ = lean_float_decLt(v___y_2870_, v___x_2873_);
v___y_2865_ = v___x_2874_;
goto v___jp_2864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object* v_inst_2889_, lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_always_2893_, lean_object* v_inst_2894_, lean_object* v_cls_2895_, lean_object* v_collapsed_2896_, lean_object* v_tag_2897_, lean_object* v_opts_2898_, lean_object* v_clsEnabled_2899_, lean_object* v_oldTraces_2900_, lean_object* v_ref_2901_, lean_object* v_msg_2902_, lean_object* v_resStartStop_2903_){
_start:
{
uint8_t v_collapsed_boxed_2904_; uint8_t v_clsEnabled_boxed_2905_; lean_object* v_res_2906_; 
v_collapsed_boxed_2904_ = lean_unbox(v_collapsed_2896_);
v_clsEnabled_boxed_2905_ = lean_unbox(v_clsEnabled_2899_);
v_res_2906_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2889_, v_inst_2890_, v_inst_2891_, v_inst_2892_, v_always_2893_, v_inst_2894_, v_cls_2895_, v_collapsed_boxed_2904_, v_tag_2897_, v_opts_2898_, v_clsEnabled_boxed_2905_, v_oldTraces_2900_, v_ref_2901_, v_msg_2902_, v_resStartStop_2903_);
lean_dec_ref(v_opts_2898_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object* v_00_u03b1_2907_, lean_object* v_m_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_00_u03b5_2911_, lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_always_2914_, lean_object* v_inst_2915_, lean_object* v_cls_2916_, uint8_t v_collapsed_2917_, lean_object* v_tag_2918_, lean_object* v_opts_2919_, uint8_t v_clsEnabled_2920_, lean_object* v_oldTraces_2921_, lean_object* v_ref_2922_, lean_object* v_msg_2923_, lean_object* v_resStartStop_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2909_, v_inst_2910_, v_inst_2912_, v_inst_2913_, v_always_2914_, v_inst_2915_, v_cls_2916_, v_collapsed_2917_, v_tag_2918_, v_opts_2919_, v_clsEnabled_2920_, v_oldTraces_2921_, v_ref_2922_, v_msg_2923_, v_resStartStop_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_2926_ = _args[0];
lean_object* v_m_2927_ = _args[1];
lean_object* v_inst_2928_ = _args[2];
lean_object* v_inst_2929_ = _args[3];
lean_object* v_00_u03b5_2930_ = _args[4];
lean_object* v_inst_2931_ = _args[5];
lean_object* v_inst_2932_ = _args[6];
lean_object* v_always_2933_ = _args[7];
lean_object* v_inst_2934_ = _args[8];
lean_object* v_cls_2935_ = _args[9];
lean_object* v_collapsed_2936_ = _args[10];
lean_object* v_tag_2937_ = _args[11];
lean_object* v_opts_2938_ = _args[12];
lean_object* v_clsEnabled_2939_ = _args[13];
lean_object* v_oldTraces_2940_ = _args[14];
lean_object* v_ref_2941_ = _args[15];
lean_object* v_msg_2942_ = _args[16];
lean_object* v_resStartStop_2943_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2944_; uint8_t v_clsEnabled_boxed_2945_; lean_object* v_res_2946_; 
v_collapsed_boxed_2944_ = lean_unbox(v_collapsed_2936_);
v_clsEnabled_boxed_2945_ = lean_unbox(v_clsEnabled_2939_);
v_res_2946_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(v_00_u03b1_2926_, v_m_2927_, v_inst_2928_, v_inst_2929_, v_00_u03b5_2930_, v_inst_2931_, v_inst_2932_, v_always_2933_, v_inst_2934_, v_cls_2935_, v_collapsed_boxed_2944_, v_tag_2937_, v_opts_2938_, v_clsEnabled_boxed_2945_, v_oldTraces_2940_, v_ref_2941_, v_msg_2942_, v_resStartStop_2943_);
lean_dec_ref(v_opts_2938_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object* v_inst_2947_, lean_object* v_____do__lift_2948_){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = lean_apply_1(v_inst_2947_, v_____do__lift_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object* v_inst_2950_, lean_object* v_inst_2951_, lean_object* v_inst_2952_, lean_object* v_inst_2953_, lean_object* v_always_2954_, lean_object* v_inst_2955_, lean_object* v_cls_2956_, uint8_t v_collapsed_2957_, lean_object* v_tag_2958_, lean_object* v_opts_2959_, uint8_t v_clsEnabled_2960_, lean_object* v_oldTraces_2961_, lean_object* v_ref_2962_, lean_object* v_msg_2963_, lean_object* v_resStartStop_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2950_, v_inst_2951_, v_inst_2952_, v_inst_2953_, v_always_2954_, v_inst_2955_, v_cls_2956_, v_collapsed_2957_, v_tag_2958_, v_opts_2959_, v_clsEnabled_2960_, v_oldTraces_2961_, v_ref_2962_, v_msg_2963_, v_resStartStop_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object* v_inst_2966_, lean_object* v_inst_2967_, lean_object* v_inst_2968_, lean_object* v_inst_2969_, lean_object* v_always_2970_, lean_object* v_inst_2971_, lean_object* v_cls_2972_, lean_object* v_collapsed_2973_, lean_object* v_tag_2974_, lean_object* v_opts_2975_, lean_object* v_clsEnabled_2976_, lean_object* v_oldTraces_2977_, lean_object* v_ref_2978_, lean_object* v_msg_2979_, lean_object* v_resStartStop_2980_){
_start:
{
uint8_t v_collapsed_boxed_2981_; uint8_t v_clsEnabled_boxed_2982_; lean_object* v_res_2983_; 
v_collapsed_boxed_2981_ = lean_unbox(v_collapsed_2973_);
v_clsEnabled_boxed_2982_ = lean_unbox(v_clsEnabled_2976_);
v_res_2983_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_2966_, v_inst_2967_, v_inst_2968_, v_inst_2969_, v_always_2970_, v_inst_2971_, v_cls_2972_, v_collapsed_boxed_2981_, v_tag_2974_, v_opts_2975_, v_clsEnabled_boxed_2982_, v_oldTraces_2977_, v_ref_2978_, v_msg_2979_, v_resStartStop_2980_);
lean_dec_ref(v_opts_2975_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object* v_always_2984_, lean_object* v_inst_2985_, lean_object* v_inst_2986_, lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_cls_2990_, uint8_t v_collapsed_2991_, lean_object* v_tag_2992_, lean_object* v_opts_2993_, uint8_t v_clsEnabled_2994_, lean_object* v_oldTraces_2995_, lean_object* v_ref_2996_, lean_object* v_toPure_2997_, lean_object* v_toBind_2998_, lean_object* v_k_2999_, lean_object* v___x_3000_, lean_object* v_inst_3001_, lean_object* v_msg_3002_){
_start:
{
lean_object* v_tryCatch_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___f_3006_; lean_object* v___f_3007_; lean_object* v___f_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v_tryCatch_3003_ = lean_ctor_get(v_always_2984_, 1);
lean_inc(v_tryCatch_3003_);
v___x_3004_ = lean_box(v_collapsed_2991_);
v___x_3005_ = lean_box(v_clsEnabled_2994_);
lean_inc_ref(v_opts_2993_);
v___f_3006_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__1___boxed), 15, 14);
lean_closure_set(v___f_3006_, 0, v_inst_2985_);
lean_closure_set(v___f_3006_, 1, v_inst_2986_);
lean_closure_set(v___f_3006_, 2, v_inst_2987_);
lean_closure_set(v___f_3006_, 3, v_inst_2988_);
lean_closure_set(v___f_3006_, 4, v_always_2984_);
lean_closure_set(v___f_3006_, 5, v_inst_2989_);
lean_closure_set(v___f_3006_, 6, v_cls_2990_);
lean_closure_set(v___f_3006_, 7, v___x_3004_);
lean_closure_set(v___f_3006_, 8, v_tag_2992_);
lean_closure_set(v___f_3006_, 9, v_opts_2993_);
lean_closure_set(v___f_3006_, 10, v___x_3005_);
lean_closure_set(v___f_3006_, 11, v_oldTraces_2995_);
lean_closure_set(v___f_3006_, 12, v_ref_2996_);
lean_closure_set(v___f_3006_, 13, v_msg_3002_);
lean_inc_n(v_toPure_2997_, 2);
v___f_3007_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3007_, 0, v_toPure_2997_);
v___f_3008_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3008_, 0, v_toPure_2997_);
lean_inc(v_toBind_2998_);
v___x_3009_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v_k_2999_, v___f_3008_);
v___x_3010_ = lean_apply_3(v_tryCatch_3003_, lean_box(0), v___x_3009_, v___f_3007_);
v___x_3011_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3012_ = l_Lean_Option_get___redArg(v___x_3000_, v_opts_2993_, v___x_3011_);
lean_dec_ref(v_opts_2993_);
v___x_3013_ = lean_unbox(v___x_3012_);
lean_dec(v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___f_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3014_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_3015_ = lean_apply_2(v_inst_3001_, lean_box(0), v___x_3014_);
lean_inc(v___x_3015_);
lean_inc_n(v_toBind_2998_, 2);
v___f_3016_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3016_, 0, v_toPure_2997_);
lean_closure_set(v___f_3016_, 1, v_toBind_2998_);
lean_closure_set(v___f_3016_, 2, v___x_3015_);
lean_closure_set(v___f_3016_, 3, v___x_3010_);
v___x_3017_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v___x_3015_, v___f_3016_);
v___x_3018_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v___x_3017_, v___f_3006_);
return v___x_3018_;
}
else
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___f_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3019_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_3020_ = lean_apply_2(v_inst_3001_, lean_box(0), v___x_3019_);
lean_inc(v___x_3020_);
lean_inc_n(v_toBind_2998_, 2);
v___f_3021_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_3021_, 0, v_toPure_2997_);
lean_closure_set(v___f_3021_, 1, v_toBind_2998_);
lean_closure_set(v___f_3021_, 2, v___x_3020_);
lean_closure_set(v___f_3021_, 3, v___x_3010_);
v___x_3022_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v___x_3020_, v___f_3021_);
v___x_3023_ = lean_apply_4(v_toBind_2998_, lean_box(0), lean_box(0), v___x_3022_, v___f_3006_);
return v___x_3023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_3024_ = _args[0];
lean_object* v_inst_3025_ = _args[1];
lean_object* v_inst_3026_ = _args[2];
lean_object* v_inst_3027_ = _args[3];
lean_object* v_inst_3028_ = _args[4];
lean_object* v_inst_3029_ = _args[5];
lean_object* v_cls_3030_ = _args[6];
lean_object* v_collapsed_3031_ = _args[7];
lean_object* v_tag_3032_ = _args[8];
lean_object* v_opts_3033_ = _args[9];
lean_object* v_clsEnabled_3034_ = _args[10];
lean_object* v_oldTraces_3035_ = _args[11];
lean_object* v_ref_3036_ = _args[12];
lean_object* v_toPure_3037_ = _args[13];
lean_object* v_toBind_3038_ = _args[14];
lean_object* v_k_3039_ = _args[15];
lean_object* v___x_3040_ = _args[16];
lean_object* v_inst_3041_ = _args[17];
lean_object* v_msg_3042_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_3043_; uint8_t v_clsEnabled_boxed_3044_; lean_object* v_res_3045_; 
v_collapsed_boxed_3043_ = lean_unbox(v_collapsed_3031_);
v_clsEnabled_boxed_3044_ = lean_unbox(v_clsEnabled_3034_);
v_res_3045_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_always_3024_, v_inst_3025_, v_inst_3026_, v_inst_3027_, v_inst_3028_, v_inst_3029_, v_cls_3030_, v_collapsed_boxed_3043_, v_tag_3032_, v_opts_3033_, v_clsEnabled_boxed_3044_, v_oldTraces_3035_, v_ref_3036_, v_toPure_3037_, v_toBind_3038_, v_k_3039_, v___x_3040_, v_inst_3041_, v_msg_3042_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object* v_always_3046_, lean_object* v_inst_3047_, lean_object* v_inst_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_cls_3052_, uint8_t v_collapsed_3053_, lean_object* v_tag_3054_, lean_object* v_opts_3055_, uint8_t v_clsEnabled_3056_, lean_object* v_oldTraces_3057_, lean_object* v_toPure_3058_, lean_object* v_toBind_3059_, lean_object* v_k_3060_, lean_object* v___x_3061_, lean_object* v_inst_3062_, lean_object* v_msg_3063_, lean_object* v___f_3064_, lean_object* v_withRef_3065_, lean_object* v_getRef_3066_, lean_object* v_ref_3067_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___f_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___f_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3068_ = lean_box(v_collapsed_3053_);
v___x_3069_ = lean_box(v_clsEnabled_3056_);
lean_inc_n(v_toBind_3059_, 3);
lean_inc(v_ref_3067_);
v___f_3070_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__10___boxed), 19, 18);
lean_closure_set(v___f_3070_, 0, v_always_3046_);
lean_closure_set(v___f_3070_, 1, v_inst_3047_);
lean_closure_set(v___f_3070_, 2, v_inst_3048_);
lean_closure_set(v___f_3070_, 3, v_inst_3049_);
lean_closure_set(v___f_3070_, 4, v_inst_3050_);
lean_closure_set(v___f_3070_, 5, v_inst_3051_);
lean_closure_set(v___f_3070_, 6, v_cls_3052_);
lean_closure_set(v___f_3070_, 7, v___x_3068_);
lean_closure_set(v___f_3070_, 8, v_tag_3054_);
lean_closure_set(v___f_3070_, 9, v_opts_3055_);
lean_closure_set(v___f_3070_, 10, v___x_3069_);
lean_closure_set(v___f_3070_, 11, v_oldTraces_3057_);
lean_closure_set(v___f_3070_, 12, v_ref_3067_);
lean_closure_set(v___f_3070_, 13, v_toPure_3058_);
lean_closure_set(v___f_3070_, 14, v_toBind_3059_);
lean_closure_set(v___f_3070_, 15, v_k_3060_);
lean_closure_set(v___f_3070_, 16, v___x_3061_);
lean_closure_set(v___f_3070_, 17, v_inst_3062_);
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_apply_1(v_msg_3063_, v___x_3071_);
v___x_3073_ = lean_apply_4(v_toBind_3059_, lean_box(0), lean_box(0), v___x_3072_, v___f_3064_);
v___f_3074_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3074_, 0, v_ref_3067_);
lean_closure_set(v___f_3074_, 1, v_withRef_3065_);
lean_closure_set(v___f_3074_, 2, v___x_3073_);
v___x_3075_ = lean_apply_4(v_toBind_3059_, lean_box(0), lean_box(0), v_getRef_3066_, v___f_3074_);
v___x_3076_ = lean_apply_4(v_toBind_3059_, lean_box(0), lean_box(0), v___x_3075_, v___f_3070_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_3077_ = _args[0];
lean_object* v_inst_3078_ = _args[1];
lean_object* v_inst_3079_ = _args[2];
lean_object* v_inst_3080_ = _args[3];
lean_object* v_inst_3081_ = _args[4];
lean_object* v_inst_3082_ = _args[5];
lean_object* v_cls_3083_ = _args[6];
lean_object* v_collapsed_3084_ = _args[7];
lean_object* v_tag_3085_ = _args[8];
lean_object* v_opts_3086_ = _args[9];
lean_object* v_clsEnabled_3087_ = _args[10];
lean_object* v_oldTraces_3088_ = _args[11];
lean_object* v_toPure_3089_ = _args[12];
lean_object* v_toBind_3090_ = _args[13];
lean_object* v_k_3091_ = _args[14];
lean_object* v___x_3092_ = _args[15];
lean_object* v_inst_3093_ = _args[16];
lean_object* v_msg_3094_ = _args[17];
lean_object* v___f_3095_ = _args[18];
lean_object* v_withRef_3096_ = _args[19];
lean_object* v_getRef_3097_ = _args[20];
lean_object* v_ref_3098_ = _args[21];
_start:
{
uint8_t v_collapsed_boxed_3099_; uint8_t v_clsEnabled_boxed_3100_; lean_object* v_res_3101_; 
v_collapsed_boxed_3099_ = lean_unbox(v_collapsed_3084_);
v_clsEnabled_boxed_3100_ = lean_unbox(v_clsEnabled_3087_);
v_res_3101_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_always_3077_, v_inst_3078_, v_inst_3079_, v_inst_3080_, v_inst_3081_, v_inst_3082_, v_cls_3083_, v_collapsed_boxed_3099_, v_tag_3085_, v_opts_3086_, v_clsEnabled_boxed_3100_, v_oldTraces_3088_, v_toPure_3089_, v_toBind_3090_, v_k_3091_, v___x_3092_, v_inst_3093_, v_msg_3094_, v___f_3095_, v_withRef_3096_, v_getRef_3097_, v_ref_3098_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object* v_inst_3102_, lean_object* v_always_3103_, lean_object* v_inst_3104_, lean_object* v_inst_3105_, lean_object* v_inst_3106_, lean_object* v_inst_3107_, lean_object* v_cls_3108_, uint8_t v_collapsed_3109_, lean_object* v_tag_3110_, lean_object* v_opts_3111_, uint8_t v_clsEnabled_3112_, lean_object* v_toPure_3113_, lean_object* v_toBind_3114_, lean_object* v_k_3115_, lean_object* v___x_3116_, lean_object* v_inst_3117_, lean_object* v_msg_3118_, lean_object* v___f_3119_, lean_object* v_oldTraces_3120_){
_start:
{
lean_object* v_getRef_3121_; lean_object* v_withRef_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___f_3125_; lean_object* v___x_3126_; 
v_getRef_3121_ = lean_ctor_get(v_inst_3102_, 0);
lean_inc_n(v_getRef_3121_, 2);
v_withRef_3122_ = lean_ctor_get(v_inst_3102_, 1);
lean_inc(v_withRef_3122_);
v___x_3123_ = lean_box(v_collapsed_3109_);
v___x_3124_ = lean_box(v_clsEnabled_3112_);
lean_inc(v_toBind_3114_);
v___f_3125_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__3___boxed), 22, 21);
lean_closure_set(v___f_3125_, 0, v_always_3103_);
lean_closure_set(v___f_3125_, 1, v_inst_3104_);
lean_closure_set(v___f_3125_, 2, v_inst_3105_);
lean_closure_set(v___f_3125_, 3, v_inst_3102_);
lean_closure_set(v___f_3125_, 4, v_inst_3106_);
lean_closure_set(v___f_3125_, 5, v_inst_3107_);
lean_closure_set(v___f_3125_, 6, v_cls_3108_);
lean_closure_set(v___f_3125_, 7, v___x_3123_);
lean_closure_set(v___f_3125_, 8, v_tag_3110_);
lean_closure_set(v___f_3125_, 9, v_opts_3111_);
lean_closure_set(v___f_3125_, 10, v___x_3124_);
lean_closure_set(v___f_3125_, 11, v_oldTraces_3120_);
lean_closure_set(v___f_3125_, 12, v_toPure_3113_);
lean_closure_set(v___f_3125_, 13, v_toBind_3114_);
lean_closure_set(v___f_3125_, 14, v_k_3115_);
lean_closure_set(v___f_3125_, 15, v___x_3116_);
lean_closure_set(v___f_3125_, 16, v_inst_3117_);
lean_closure_set(v___f_3125_, 17, v_msg_3118_);
lean_closure_set(v___f_3125_, 18, v___f_3119_);
lean_closure_set(v___f_3125_, 19, v_withRef_3122_);
lean_closure_set(v___f_3125_, 20, v_getRef_3121_);
v___x_3126_ = lean_apply_4(v_toBind_3114_, lean_box(0), lean_box(0), v_getRef_3121_, v___f_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_3127_ = _args[0];
lean_object* v_always_3128_ = _args[1];
lean_object* v_inst_3129_ = _args[2];
lean_object* v_inst_3130_ = _args[3];
lean_object* v_inst_3131_ = _args[4];
lean_object* v_inst_3132_ = _args[5];
lean_object* v_cls_3133_ = _args[6];
lean_object* v_collapsed_3134_ = _args[7];
lean_object* v_tag_3135_ = _args[8];
lean_object* v_opts_3136_ = _args[9];
lean_object* v_clsEnabled_3137_ = _args[10];
lean_object* v_toPure_3138_ = _args[11];
lean_object* v_toBind_3139_ = _args[12];
lean_object* v_k_3140_ = _args[13];
lean_object* v___x_3141_ = _args[14];
lean_object* v_inst_3142_ = _args[15];
lean_object* v_msg_3143_ = _args[16];
lean_object* v___f_3144_ = _args[17];
lean_object* v_oldTraces_3145_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_3146_; uint8_t v_clsEnabled_boxed_3147_; lean_object* v_res_3148_; 
v_collapsed_boxed_3146_ = lean_unbox(v_collapsed_3134_);
v_clsEnabled_boxed_3147_ = lean_unbox(v_clsEnabled_3137_);
v_res_3148_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3127_, v_always_3128_, v_inst_3129_, v_inst_3130_, v_inst_3131_, v_inst_3132_, v_cls_3133_, v_collapsed_boxed_3146_, v_tag_3135_, v_opts_3136_, v_clsEnabled_boxed_3147_, v_toPure_3138_, v_toBind_3139_, v_k_3140_, v___x_3141_, v_inst_3142_, v_msg_3143_, v___f_3144_, v_oldTraces_3145_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object* v_inst_3149_, lean_object* v_always_3150_, lean_object* v_inst_3151_, lean_object* v_inst_3152_, lean_object* v_inst_3153_, lean_object* v_inst_3154_, lean_object* v_cls_3155_, uint8_t v_collapsed_3156_, lean_object* v_tag_3157_, lean_object* v_opts_3158_, lean_object* v_toPure_3159_, lean_object* v_toBind_3160_, lean_object* v_k_3161_, lean_object* v___x_3162_, lean_object* v_inst_3163_, lean_object* v_msg_3164_, lean_object* v___f_3165_, uint8_t v_clsEnabled_3166_){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___f_3169_; 
v___x_3167_ = lean_box(v_collapsed_3156_);
v___x_3168_ = lean_box(v_clsEnabled_3166_);
lean_inc_ref(v___x_3162_);
lean_inc(v_k_3161_);
lean_inc(v_toBind_3160_);
lean_inc_ref(v_opts_3158_);
lean_inc_ref(v_inst_3152_);
lean_inc_ref(v_inst_3151_);
v___f_3169_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__2___boxed), 19, 18);
lean_closure_set(v___f_3169_, 0, v_inst_3149_);
lean_closure_set(v___f_3169_, 1, v_always_3150_);
lean_closure_set(v___f_3169_, 2, v_inst_3151_);
lean_closure_set(v___f_3169_, 3, v_inst_3152_);
lean_closure_set(v___f_3169_, 4, v_inst_3153_);
lean_closure_set(v___f_3169_, 5, v_inst_3154_);
lean_closure_set(v___f_3169_, 6, v_cls_3155_);
lean_closure_set(v___f_3169_, 7, v___x_3167_);
lean_closure_set(v___f_3169_, 8, v_tag_3157_);
lean_closure_set(v___f_3169_, 9, v_opts_3158_);
lean_closure_set(v___f_3169_, 10, v___x_3168_);
lean_closure_set(v___f_3169_, 11, v_toPure_3159_);
lean_closure_set(v___f_3169_, 12, v_toBind_3160_);
lean_closure_set(v___f_3169_, 13, v_k_3161_);
lean_closure_set(v___f_3169_, 14, v___x_3162_);
lean_closure_set(v___f_3169_, 15, v_inst_3163_);
lean_closure_set(v___f_3169_, 16, v_msg_3164_);
lean_closure_set(v___f_3169_, 17, v___f_3165_);
if (v_clsEnabled_3166_ == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v___x_3173_ = l_Lean_trace_profiler;
v___x_3174_ = l_Lean_Option_get___redArg(v___x_3162_, v_opts_3158_, v___x_3173_);
lean_dec_ref(v_opts_3158_);
v___x_3175_ = lean_unbox(v___x_3174_);
lean_dec(v___x_3174_);
if (v___x_3175_ == 0)
{
lean_dec_ref(v___f_3169_);
lean_dec(v_toBind_3160_);
lean_dec_ref(v_inst_3152_);
lean_dec_ref(v_inst_3151_);
return v_k_3161_;
}
else
{
lean_dec(v_k_3161_);
goto v___jp_3170_;
}
}
else
{
lean_dec_ref(v___x_3162_);
lean_dec(v_k_3161_);
lean_dec_ref(v_opts_3158_);
goto v___jp_3170_;
}
v___jp_3170_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3151_, v_inst_3152_);
v___x_3172_ = lean_apply_4(v_toBind_3160_, lean_box(0), lean_box(0), v___x_3171_, v___f_3169_);
return v___x_3172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_3176_ = _args[0];
lean_object* v_always_3177_ = _args[1];
lean_object* v_inst_3178_ = _args[2];
lean_object* v_inst_3179_ = _args[3];
lean_object* v_inst_3180_ = _args[4];
lean_object* v_inst_3181_ = _args[5];
lean_object* v_cls_3182_ = _args[6];
lean_object* v_collapsed_3183_ = _args[7];
lean_object* v_tag_3184_ = _args[8];
lean_object* v_opts_3185_ = _args[9];
lean_object* v_toPure_3186_ = _args[10];
lean_object* v_toBind_3187_ = _args[11];
lean_object* v_k_3188_ = _args[12];
lean_object* v___x_3189_ = _args[13];
lean_object* v_inst_3190_ = _args[14];
lean_object* v_msg_3191_ = _args[15];
lean_object* v___f_3192_ = _args[16];
lean_object* v_clsEnabled_3193_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3194_; uint8_t v_clsEnabled_boxed_3195_; lean_object* v_res_3196_; 
v_collapsed_boxed_3194_ = lean_unbox(v_collapsed_3183_);
v_clsEnabled_boxed_3195_ = lean_unbox(v_clsEnabled_3193_);
v_res_3196_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3176_, v_always_3177_, v_inst_3178_, v_inst_3179_, v_inst_3180_, v_inst_3181_, v_cls_3182_, v_collapsed_boxed_3194_, v_tag_3184_, v_opts_3185_, v_toPure_3186_, v_toBind_3187_, v_k_3188_, v___x_3189_, v_inst_3190_, v_msg_3191_, v___f_3192_, v_clsEnabled_boxed_3195_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object* v_k_3197_, lean_object* v_inst_3198_, lean_object* v_toApplicative_3199_, lean_object* v_inst_3200_, lean_object* v_always_3201_, lean_object* v_inst_3202_, lean_object* v_inst_3203_, lean_object* v_inst_3204_, lean_object* v_cls_3205_, uint8_t v_collapsed_3206_, lean_object* v_tag_3207_, lean_object* v_toBind_3208_, lean_object* v___x_3209_, lean_object* v_inst_3210_, lean_object* v_msg_3211_, lean_object* v___f_3212_, lean_object* v_getOptionsUnrestricted_3213_, lean_object* v_opts_3214_){
_start:
{
uint8_t v_hasTrace_3215_; 
v_hasTrace_3215_ = lean_ctor_get_uint8(v_opts_3214_, sizeof(void*)*1);
if (v_hasTrace_3215_ == 0)
{
lean_dec_ref(v_opts_3214_);
lean_dec(v_getOptionsUnrestricted_3213_);
lean_dec(v___f_3212_);
lean_dec(v_msg_3211_);
lean_dec(v_inst_3210_);
lean_dec_ref(v___x_3209_);
lean_dec(v_toBind_3208_);
lean_dec_ref(v_tag_3207_);
lean_dec(v_cls_3205_);
lean_dec_ref(v_inst_3204_);
lean_dec(v_inst_3203_);
lean_dec_ref(v_inst_3202_);
lean_dec_ref(v_always_3201_);
lean_dec_ref(v_inst_3200_);
lean_dec_ref(v_toApplicative_3199_);
lean_dec_ref(v_inst_3198_);
return v_k_3197_;
}
else
{
lean_object* v_getInheritedTraceOptions_3216_; lean_object* v_toPure_3217_; lean_object* v___x_3218_; lean_object* v___f_3219_; lean_object* v___f_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_getInheritedTraceOptions_3216_ = lean_ctor_get(v_inst_3198_, 2);
lean_inc(v_getInheritedTraceOptions_3216_);
v_toPure_3217_ = lean_ctor_get(v_toApplicative_3199_, 1);
lean_inc_n(v_toPure_3217_, 2);
lean_dec_ref(v_toApplicative_3199_);
v___x_3218_ = lean_box(v_collapsed_3206_);
lean_inc_n(v_toBind_3208_, 3);
lean_inc(v_cls_3205_);
v___f_3219_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__4___boxed), 18, 17);
lean_closure_set(v___f_3219_, 0, v_inst_3200_);
lean_closure_set(v___f_3219_, 1, v_always_3201_);
lean_closure_set(v___f_3219_, 2, v_inst_3202_);
lean_closure_set(v___f_3219_, 3, v_inst_3198_);
lean_closure_set(v___f_3219_, 4, v_inst_3203_);
lean_closure_set(v___f_3219_, 5, v_inst_3204_);
lean_closure_set(v___f_3219_, 6, v_cls_3205_);
lean_closure_set(v___f_3219_, 7, v___x_3218_);
lean_closure_set(v___f_3219_, 8, v_tag_3207_);
lean_closure_set(v___f_3219_, 9, v_opts_3214_);
lean_closure_set(v___f_3219_, 10, v_toPure_3217_);
lean_closure_set(v___f_3219_, 11, v_toBind_3208_);
lean_closure_set(v___f_3219_, 12, v_k_3197_);
lean_closure_set(v___f_3219_, 13, v___x_3209_);
lean_closure_set(v___f_3219_, 14, v_inst_3210_);
lean_closure_set(v___f_3219_, 15, v_msg_3211_);
lean_closure_set(v___f_3219_, 16, v___f_3212_);
v___f_3220_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__12), 5, 4);
lean_closure_set(v___f_3220_, 0, v_toPure_3217_);
lean_closure_set(v___f_3220_, 1, v_cls_3205_);
lean_closure_set(v___f_3220_, 2, v_toBind_3208_);
lean_closure_set(v___f_3220_, 3, v_getOptionsUnrestricted_3213_);
v___x_3221_ = lean_apply_4(v_toBind_3208_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3216_, v___f_3220_);
v___x_3222_ = lean_apply_4(v_toBind_3208_, lean_box(0), lean_box(0), v___x_3221_, v___f_3219_);
return v___x_3222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_k_3223_ = _args[0];
lean_object* v_inst_3224_ = _args[1];
lean_object* v_toApplicative_3225_ = _args[2];
lean_object* v_inst_3226_ = _args[3];
lean_object* v_always_3227_ = _args[4];
lean_object* v_inst_3228_ = _args[5];
lean_object* v_inst_3229_ = _args[6];
lean_object* v_inst_3230_ = _args[7];
lean_object* v_cls_3231_ = _args[8];
lean_object* v_collapsed_3232_ = _args[9];
lean_object* v_tag_3233_ = _args[10];
lean_object* v_toBind_3234_ = _args[11];
lean_object* v___x_3235_ = _args[12];
lean_object* v_inst_3236_ = _args[13];
lean_object* v_msg_3237_ = _args[14];
lean_object* v___f_3238_ = _args[15];
lean_object* v_getOptionsUnrestricted_3239_ = _args[16];
lean_object* v_opts_3240_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3241_; lean_object* v_res_3242_; 
v_collapsed_boxed_3241_ = lean_unbox(v_collapsed_3232_);
v_res_3242_ = l_Lean_withTraceNodeBefore___redArg___lam__7(v_k_3223_, v_inst_3224_, v_toApplicative_3225_, v_inst_3226_, v_always_3227_, v_inst_3228_, v_inst_3229_, v_inst_3230_, v_cls_3231_, v_collapsed_boxed_3241_, v_tag_3233_, v_toBind_3234_, v___x_3235_, v_inst_3236_, v_msg_3237_, v___f_3238_, v_getOptionsUnrestricted_3239_, v_opts_3240_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_always_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_cls_3251_, lean_object* v_msg_3252_, lean_object* v_k_3253_, uint8_t v_collapsed_3254_, lean_object* v_tag_3255_){
_start:
{
lean_object* v___x_3256_; lean_object* v_toApplicative_3257_; lean_object* v_toBind_3258_; lean_object* v_getOptionsUnrestricted_3259_; lean_object* v___f_3260_; lean_object* v___x_3261_; lean_object* v___f_3262_; lean_object* v___x_3263_; 
v___x_3256_ = l_Lean_KVMap_instValueBool;
v_toApplicative_3257_ = lean_ctor_get(v_inst_3243_, 0);
lean_inc_ref(v_toApplicative_3257_);
v_toBind_3258_ = lean_ctor_get(v_inst_3243_, 1);
lean_inc_n(v_toBind_3258_, 2);
v_getOptionsUnrestricted_3259_ = lean_ctor_get(v_inst_3247_, 1);
lean_inc_n(v_getOptionsUnrestricted_3259_, 2);
lean_dec_ref(v_inst_3247_);
lean_inc(v_inst_3246_);
v___f_3260_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3260_, 0, v_inst_3246_);
v___x_3261_ = lean_box(v_collapsed_3254_);
v___f_3262_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 18, 17);
lean_closure_set(v___f_3262_, 0, v_k_3253_);
lean_closure_set(v___f_3262_, 1, v_inst_3244_);
lean_closure_set(v___f_3262_, 2, v_toApplicative_3257_);
lean_closure_set(v___f_3262_, 3, v_inst_3245_);
lean_closure_set(v___f_3262_, 4, v_always_3248_);
lean_closure_set(v___f_3262_, 5, v_inst_3243_);
lean_closure_set(v___f_3262_, 6, v_inst_3246_);
lean_closure_set(v___f_3262_, 7, v_inst_3250_);
lean_closure_set(v___f_3262_, 8, v_cls_3251_);
lean_closure_set(v___f_3262_, 9, v___x_3261_);
lean_closure_set(v___f_3262_, 10, v_tag_3255_);
lean_closure_set(v___f_3262_, 11, v_toBind_3258_);
lean_closure_set(v___f_3262_, 12, v___x_3256_);
lean_closure_set(v___f_3262_, 13, v_inst_3249_);
lean_closure_set(v___f_3262_, 14, v_msg_3252_);
lean_closure_set(v___f_3262_, 15, v___f_3260_);
lean_closure_set(v___f_3262_, 16, v_getOptionsUnrestricted_3259_);
v___x_3263_ = lean_apply_4(v_toBind_3258_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3259_, v___f_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object* v_inst_3264_, lean_object* v_inst_3265_, lean_object* v_inst_3266_, lean_object* v_inst_3267_, lean_object* v_inst_3268_, lean_object* v_always_3269_, lean_object* v_inst_3270_, lean_object* v_inst_3271_, lean_object* v_cls_3272_, lean_object* v_msg_3273_, lean_object* v_k_3274_, lean_object* v_collapsed_3275_, lean_object* v_tag_3276_){
_start:
{
uint8_t v_collapsed_boxed_3277_; lean_object* v_res_3278_; 
v_collapsed_boxed_3277_ = lean_unbox(v_collapsed_3275_);
v_res_3278_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3264_, v_inst_3265_, v_inst_3266_, v_inst_3267_, v_inst_3268_, v_always_3269_, v_inst_3270_, v_inst_3271_, v_cls_3272_, v_msg_3273_, v_k_3274_, v_collapsed_boxed_3277_, v_tag_3276_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object* v_00_u03b1_3279_, lean_object* v_m_3280_, lean_object* v_inst_3281_, lean_object* v_inst_3282_, lean_object* v_00_u03b5_3283_, lean_object* v_inst_3284_, lean_object* v_inst_3285_, lean_object* v_inst_3286_, lean_object* v_always_3287_, lean_object* v_inst_3288_, lean_object* v_inst_3289_, lean_object* v_cls_3290_, lean_object* v_msg_3291_, lean_object* v_k_3292_, uint8_t v_collapsed_3293_, lean_object* v_tag_3294_){
_start:
{
lean_object* v___x_3295_; lean_object* v_toApplicative_3296_; lean_object* v_toBind_3297_; lean_object* v_getOptionsUnrestricted_3298_; lean_object* v___f_3299_; lean_object* v___x_3300_; lean_object* v___f_3301_; lean_object* v___x_3302_; 
v___x_3295_ = l_Lean_KVMap_instValueBool;
v_toApplicative_3296_ = lean_ctor_get(v_inst_3281_, 0);
lean_inc_ref(v_toApplicative_3296_);
v_toBind_3297_ = lean_ctor_get(v_inst_3281_, 1);
lean_inc_n(v_toBind_3297_, 2);
v_getOptionsUnrestricted_3298_ = lean_ctor_get(v_inst_3286_, 1);
lean_inc_n(v_getOptionsUnrestricted_3298_, 2);
lean_dec_ref(v_inst_3286_);
lean_inc(v_inst_3285_);
v___f_3299_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3299_, 0, v_inst_3285_);
v___x_3300_ = lean_box(v_collapsed_3293_);
v___f_3301_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 18, 17);
lean_closure_set(v___f_3301_, 0, v_k_3292_);
lean_closure_set(v___f_3301_, 1, v_inst_3282_);
lean_closure_set(v___f_3301_, 2, v_toApplicative_3296_);
lean_closure_set(v___f_3301_, 3, v_inst_3284_);
lean_closure_set(v___f_3301_, 4, v_always_3287_);
lean_closure_set(v___f_3301_, 5, v_inst_3281_);
lean_closure_set(v___f_3301_, 6, v_inst_3285_);
lean_closure_set(v___f_3301_, 7, v_inst_3289_);
lean_closure_set(v___f_3301_, 8, v_cls_3290_);
lean_closure_set(v___f_3301_, 9, v___x_3300_);
lean_closure_set(v___f_3301_, 10, v_tag_3294_);
lean_closure_set(v___f_3301_, 11, v_toBind_3297_);
lean_closure_set(v___f_3301_, 12, v___x_3295_);
lean_closure_set(v___f_3301_, 13, v_inst_3288_);
lean_closure_set(v___f_3301_, 14, v_msg_3291_);
lean_closure_set(v___f_3301_, 15, v___f_3299_);
lean_closure_set(v___f_3301_, 16, v_getOptionsUnrestricted_3298_);
v___x_3302_ = lean_apply_4(v_toBind_3297_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3298_, v___f_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object* v_00_u03b1_3303_, lean_object* v_m_3304_, lean_object* v_inst_3305_, lean_object* v_inst_3306_, lean_object* v_00_u03b5_3307_, lean_object* v_inst_3308_, lean_object* v_inst_3309_, lean_object* v_inst_3310_, lean_object* v_always_3311_, lean_object* v_inst_3312_, lean_object* v_inst_3313_, lean_object* v_cls_3314_, lean_object* v_msg_3315_, lean_object* v_k_3316_, lean_object* v_collapsed_3317_, lean_object* v_tag_3318_){
_start:
{
uint8_t v_collapsed_boxed_3319_; lean_object* v_res_3320_; 
v_collapsed_boxed_3319_ = lean_unbox(v_collapsed_3317_);
v_res_3320_ = l_Lean_withTraceNodeBefore(v_00_u03b1_3303_, v_m_3304_, v_inst_3305_, v_inst_3306_, v_00_u03b5_3307_, v_inst_3308_, v_inst_3309_, v_inst_3310_, v_always_3311_, v_inst_3312_, v_inst_3313_, v_cls_3314_, v_msg_3315_, v_k_3316_, v_collapsed_boxed_3319_, v_tag_3318_);
return v_res_3320_;
}
}
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__0(lean_object* v_x_3321_, lean_object* v_x_3322_){
_start:
{
lean_object* v_fst_3323_; lean_object* v_fst_3324_; lean_object* v_fst_3325_; lean_object* v_fst_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; 
v_fst_3323_ = lean_ctor_get(v_x_3321_, 0);
v_fst_3324_ = lean_ctor_get(v_x_3322_, 0);
v_fst_3325_ = lean_ctor_get(v_fst_3323_, 0);
v_fst_3326_ = lean_ctor_get(v_fst_3324_, 0);
v___x_3327_ = lean_unsigned_to_nat(1u);
v___x_3328_ = lean_nat_add(v_fst_3325_, v___x_3327_);
v___x_3329_ = lean_nat_dec_le(v___x_3328_, v_fst_3326_);
lean_dec(v___x_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0___boxed(lean_object* v_x_3330_, lean_object* v_x_3331_){
_start:
{
uint8_t v_res_3332_; lean_object* v_r_3333_; 
v_res_3332_ = l_Lean_addTraceAsMessages___redArg___lam__0(v_x_3330_, v_x_3331_);
lean_dec_ref(v_x_3331_);
lean_dec_ref(v_x_3330_);
v_r_3333_ = lean_box(v_res_3332_);
return v_r_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1(lean_object* v_x1_3334_, lean_object* v_x2_3335_, lean_object* v_x3_3336_){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3337_, 0, v_x2_3335_);
lean_ctor_set(v___x_3337_, 1, v_x3_3336_);
v___x_3338_ = lean_array_push(v_x1_3334_, v___x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object* v_____do__lift_3339_, lean_object* v___x_3340_, lean_object* v_fst_3341_, lean_object* v_snd_3342_, lean_object* v_logMessage_3343_, lean_object* v_toBind_3344_, lean_object* v___f_3345_, lean_object* v_____do__lift_3346_){
_start:
{
uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3347_ = 0;
v___x_3348_ = l_Lean_Elab_mkMessageCore(v_____do__lift_3339_, v_____do__lift_3346_, v___x_3340_, v___x_3347_, v_fst_3341_, v_snd_3342_);
v___x_3349_ = lean_apply_1(v_logMessage_3343_, v___x_3348_);
v___x_3350_ = lean_apply_4(v_toBind_3344_, lean_box(0), lean_box(0), v___x_3349_, v___f_3345_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object* v_____do__lift_3351_, lean_object* v___x_3352_, lean_object* v_fst_3353_, lean_object* v_snd_3354_, lean_object* v_logMessage_3355_, lean_object* v_toBind_3356_, lean_object* v___f_3357_, lean_object* v_____do__lift_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lean_addTraceAsMessages___redArg___lam__4(v_____do__lift_3351_, v___x_3352_, v_fst_3353_, v_snd_3354_, v_logMessage_3355_, v_toBind_3356_, v___f_3357_, v_____do__lift_3358_);
lean_dec(v_snd_3354_);
lean_dec(v_fst_3353_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object* v___x_3360_, lean_object* v_fst_3361_, lean_object* v_snd_3362_, lean_object* v_logMessage_3363_, lean_object* v_toBind_3364_, lean_object* v___f_3365_, lean_object* v_toMonadFileMap_3366_, lean_object* v_____do__lift_3367_){
_start:
{
lean_object* v___f_3368_; lean_object* v___x_3369_; 
lean_inc(v_toBind_3364_);
v___f_3368_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_3368_, 0, v_____do__lift_3367_);
lean_closure_set(v___f_3368_, 1, v___x_3360_);
lean_closure_set(v___f_3368_, 2, v_fst_3361_);
lean_closure_set(v___f_3368_, 3, v_snd_3362_);
lean_closure_set(v___f_3368_, 4, v_logMessage_3363_);
lean_closure_set(v___f_3368_, 5, v_toBind_3364_);
lean_closure_set(v___f_3368_, 6, v___f_3365_);
v___x_3369_ = lean_apply_4(v_toBind_3364_, lean_box(0), lean_box(0), v_toMonadFileMap_3366_, v___f_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object* v___x_3370_, uint8_t v___x_3371_, lean_object* v_logMessage_3372_, lean_object* v_toBind_3373_, lean_object* v___f_3374_, lean_object* v_toMonadFileMap_3375_, lean_object* v_getFileName_3376_, lean_object* v_a_3377_, lean_object* v_x_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_fst_3380_; lean_object* v_snd_3381_; lean_object* v_fst_3382_; lean_object* v_snd_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3400_; 
v_fst_3380_ = lean_ctor_get(v_a_3377_, 0);
lean_inc(v_fst_3380_);
v_snd_3381_ = lean_ctor_get(v_a_3377_, 1);
lean_inc(v_snd_3381_);
lean_dec_ref(v_a_3377_);
v_fst_3382_ = lean_ctor_get(v_fst_3380_, 0);
v_snd_3383_ = lean_ctor_get(v_fst_3380_, 1);
v_isSharedCheck_3400_ = !lean_is_exclusive(v_fst_3380_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3385_ = v_fst_3380_;
v_isShared_3386_ = v_isSharedCheck_3400_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_snd_3383_);
lean_inc(v_fst_3382_);
lean_dec(v_fst_3380_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3400_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; double v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3387_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_3388_ = lean_box(0);
v___x_3389_ = lean_box(0);
v___x_3390_ = lean_float_of_nat(v___x_3370_);
v___x_3391_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_3392_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3392_, 0, v___x_3388_);
lean_ctor_set(v___x_3392_, 1, v___x_3389_);
lean_ctor_set(v___x_3392_, 2, v___x_3391_);
lean_ctor_set_float(v___x_3392_, sizeof(void*)*3, v___x_3390_);
lean_ctor_set_float(v___x_3392_, sizeof(void*)*3 + 8, v___x_3390_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 16, v___x_3371_);
v___x_3393_ = l_Lean_MessageData_nil;
v___x_3394_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3392_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
lean_ctor_set(v___x_3394_, 2, v_snd_3381_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set_tag(v___x_3385_, 8);
lean_ctor_set(v___x_3385_, 1, v___x_3394_);
lean_ctor_set(v___x_3385_, 0, v___x_3387_);
v___x_3396_ = v___x_3385_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___f_3397_; lean_object* v___x_3398_; 
lean_inc(v_toBind_3373_);
v___f_3397_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__2), 8, 7);
lean_closure_set(v___f_3397_, 0, v___x_3396_);
lean_closure_set(v___f_3397_, 1, v_fst_3382_);
lean_closure_set(v___f_3397_, 2, v_snd_3383_);
lean_closure_set(v___f_3397_, 3, v_logMessage_3372_);
lean_closure_set(v___f_3397_, 4, v_toBind_3373_);
lean_closure_set(v___f_3397_, 5, v___f_3374_);
lean_closure_set(v___f_3397_, 6, v_toMonadFileMap_3375_);
v___x_3398_ = lean_apply_4(v_toBind_3373_, lean_box(0), lean_box(0), v_getFileName_3376_, v___f_3397_);
return v___x_3398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3___boxed(lean_object* v___x_3401_, lean_object* v___x_3402_, lean_object* v_logMessage_3403_, lean_object* v_toBind_3404_, lean_object* v___f_3405_, lean_object* v_toMonadFileMap_3406_, lean_object* v_getFileName_3407_, lean_object* v_a_3408_, lean_object* v_x_3409_, lean_object* v___y_3410_){
_start:
{
uint8_t v___x_904__boxed_3411_; lean_object* v_res_3412_; 
v___x_904__boxed_3411_ = lean_unbox(v___x_3402_);
v_res_3412_ = l_Lean_addTraceAsMessages___redArg___lam__3(v___x_3401_, v___x_904__boxed_3411_, v_logMessage_3403_, v_toBind_3404_, v___f_3405_, v_toMonadFileMap_3406_, v_getFileName_3407_, v_a_3408_, v_x_3409_, v___y_3410_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object* v___x_3413_, lean_object* v___f_3414_, lean_object* v_acc_3415_, lean_object* v_l_3416_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_3413_, v___f_3414_, v_acc_3415_, v_l_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object* v_toPure_3418_, uint8_t v___x_3419_, lean_object* v_logMessage_3420_, lean_object* v_toBind_3421_, lean_object* v_toMonadFileMap_3422_, lean_object* v_getFileName_3423_, lean_object* v_inst_3424_, lean_object* v___f_3425_, lean_object* v___f_3426_, lean_object* v___f_3427_, lean_object* v_____s_3428_){
_start:
{
lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3455_; lean_object* v_size_3462_; lean_object* v_buckets_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
v_size_3462_ = lean_ctor_get(v_____s_3428_, 0);
lean_inc(v_size_3462_);
v_buckets_3463_ = lean_ctor_get(v_____s_3428_, 1);
lean_inc_ref(v_buckets_3463_);
lean_dec_ref(v_____s_3428_);
v___x_3464_ = lean_mk_empty_array_with_capacity(v_size_3462_);
lean_dec(v_size_3462_);
v___x_3465_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v___x_3466_ = lean_unsigned_to_nat(0u);
v___x_3467_ = lean_array_get_size(v_buckets_3463_);
v___x_3468_ = lean_nat_dec_lt(v___x_3466_, v___x_3467_);
if (v___x_3468_ == 0)
{
lean_dec_ref(v_buckets_3463_);
lean_dec_ref(v___f_3427_);
v___y_3455_ = v___x_3464_;
goto v___jp_3454_;
}
else
{
lean_object* v___f_3469_; size_t v___x_3470_; size_t v___x_3471_; lean_object* v___x_3472_; 
v___f_3469_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__5), 4, 2);
lean_closure_set(v___f_3469_, 0, v___x_3465_);
lean_closure_set(v___f_3469_, 1, v___f_3427_);
v___x_3470_ = ((size_t)0ULL);
v___x_3471_ = lean_usize_of_nat(v___x_3467_);
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3465_, v___f_3469_, v_buckets_3463_, v___x_3470_, v___x_3471_, v___x_3464_);
v___y_3455_ = v___x_3472_;
goto v___jp_3454_;
}
v___jp_3429_:
{
lean_object* v___x_3432_; lean_object* v___f_3433_; lean_object* v___x_3434_; lean_object* v___f_3435_; size_t v_sz_3436_; size_t v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3432_ = lean_box(0);
v___f_3433_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3433_, 0, v___x_3432_);
lean_closure_set(v___f_3433_, 1, v_toPure_3418_);
v___x_3434_ = lean_box(v___x_3419_);
lean_inc(v_toBind_3421_);
v___f_3435_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__3___boxed), 10, 7);
lean_closure_set(v___f_3435_, 0, v___y_3430_);
lean_closure_set(v___f_3435_, 1, v___x_3434_);
lean_closure_set(v___f_3435_, 2, v_logMessage_3420_);
lean_closure_set(v___f_3435_, 3, v_toBind_3421_);
lean_closure_set(v___f_3435_, 4, v___f_3433_);
lean_closure_set(v___f_3435_, 5, v_toMonadFileMap_3422_);
lean_closure_set(v___f_3435_, 6, v_getFileName_3423_);
v_sz_3436_ = lean_array_size(v___y_3431_);
v___x_3437_ = ((size_t)0ULL);
v___x_3438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3424_, v___y_3431_, v___f_3435_, v_sz_3436_, v___x_3437_, v___x_3432_);
v___x_3439_ = lean_apply_4(v_toBind_3421_, lean_box(0), lean_box(0), v___x_3438_, v___f_3425_);
return v___x_3439_;
}
v___jp_3440_:
{
lean_object* v___x_3446_; 
v___x_3446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_3426_, v___y_3443_, v___y_3444_, v___y_3442_, v___y_3445_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_3445_);
lean_dec(v___y_3443_);
v___y_3430_ = v___y_3441_;
v___y_3431_ = v___x_3446_;
goto v___jp_3429_;
}
v___jp_3447_:
{
uint8_t v___x_3453_; 
v___x_3453_ = lean_nat_dec_le(v___y_3452_, v___y_3449_);
if (v___x_3453_ == 0)
{
lean_dec(v___y_3449_);
lean_inc(v___y_3452_);
v___y_3441_ = v___y_3448_;
v___y_3442_ = v___y_3452_;
v___y_3443_ = v___y_3450_;
v___y_3444_ = v___y_3451_;
v___y_3445_ = v___y_3452_;
goto v___jp_3440_;
}
else
{
v___y_3441_ = v___y_3448_;
v___y_3442_ = v___y_3452_;
v___y_3443_ = v___y_3450_;
v___y_3444_ = v___y_3451_;
v___y_3445_ = v___y_3449_;
goto v___jp_3440_;
}
}
v___jp_3454_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3456_ = lean_unsigned_to_nat(0u);
v___x_3457_ = lean_array_get_size(v___y_3455_);
v___x_3458_ = lean_nat_dec_eq(v___x_3457_, v___x_3456_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
v___x_3459_ = lean_unsigned_to_nat(1u);
v___x_3460_ = lean_nat_sub(v___x_3457_, v___x_3459_);
v___x_3461_ = lean_nat_dec_le(v___x_3456_, v___x_3460_);
if (v___x_3461_ == 0)
{
lean_inc(v___x_3460_);
v___y_3448_ = v___x_3456_;
v___y_3449_ = v___x_3460_;
v___y_3450_ = v___x_3457_;
v___y_3451_ = v___y_3455_;
v___y_3452_ = v___x_3460_;
goto v___jp_3447_;
}
else
{
v___y_3448_ = v___x_3456_;
v___y_3449_ = v___x_3460_;
v___y_3450_ = v___x_3457_;
v___y_3451_ = v___y_3455_;
v___y_3452_ = v___x_3456_;
goto v___jp_3447_;
}
}
else
{
lean_dec_ref(v___f_3426_);
v___y_3430_ = v___x_3456_;
v___y_3431_ = v___y_3455_;
goto v___jp_3429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object* v_toPure_3473_, lean_object* v___x_3474_, lean_object* v_logMessage_3475_, lean_object* v_toBind_3476_, lean_object* v_toMonadFileMap_3477_, lean_object* v_getFileName_3478_, lean_object* v_inst_3479_, lean_object* v___f_3480_, lean_object* v___f_3481_, lean_object* v___f_3482_, lean_object* v_____s_3483_){
_start:
{
uint8_t v___x_989__boxed_3484_; lean_object* v_res_3485_; 
v___x_989__boxed_3484_ = lean_unbox(v___x_3474_);
v_res_3485_ = l_Lean_addTraceAsMessages___redArg___lam__6(v_toPure_3473_, v___x_989__boxed_3484_, v_logMessage_3475_, v_toBind_3476_, v_toMonadFileMap_3477_, v_getFileName_3478_, v_inst_3479_, v___f_3480_, v___f_3481_, v___f_3482_, v_____s_3483_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object* v_traceElem_3486_, lean_object* v___f_3487_, lean_object* v___f_3488_, lean_object* v_____s_3489_, lean_object* v_toPure_3490_, uint8_t v___x_3491_, lean_object* v_____do__lift_3492_){
_start:
{
lean_object* v_ref_3493_; lean_object* v_msg_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3518_; 
v_ref_3493_ = lean_ctor_get(v_traceElem_3486_, 0);
v_msg_3494_ = lean_ctor_get(v_traceElem_3486_, 1);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_traceElem_3486_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3496_ = v_traceElem_3486_;
v_isShared_3497_ = v_isSharedCheck_3518_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_msg_3494_);
lean_inc(v_ref_3493_);
lean_dec(v_traceElem_3486_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3518_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v_ref_3510_; lean_object* v___y_3512_; lean_object* v___x_3515_; 
v_ref_3510_ = l_Lean_replaceRef(v_ref_3493_, v_____do__lift_3492_);
lean_dec(v_ref_3493_);
v___x_3515_ = l_Lean_Syntax_getPos_x3f(v_ref_3510_, v___x_3491_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v___x_3516_; 
v___x_3516_ = lean_unsigned_to_nat(0u);
v___y_3512_ = v___x_3516_;
goto v___jp_3511_;
}
else
{
lean_object* v_val_3517_; 
v_val_3517_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_val_3517_);
lean_dec_ref_known(v___x_3515_, 1);
v___y_3512_ = v_val_3517_;
goto v___jp_3511_;
}
v___jp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 1, v___y_3500_);
lean_ctor_set(v___x_3496_, 0, v___y_3499_);
v___x_3502_ = v___x_3496_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___y_3499_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v___y_3500_);
v___x_3502_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v_pos2traces_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3503_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
lean_inc_ref(v___x_3502_);
lean_inc_ref(v___f_3488_);
lean_inc_ref(v___f_3487_);
v___x_3504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_3487_, v___f_3488_, v_____s_3489_, v___x_3502_, v___x_3503_);
v___x_3505_ = lean_array_push(v___x_3504_, v_msg_3494_);
v_pos2traces_3506_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3487_, v___f_3488_, v_____s_3489_, v___x_3502_, v___x_3505_);
v___x_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3507_, 0, v_pos2traces_3506_);
v___x_3508_ = lean_apply_2(v_toPure_3490_, lean_box(0), v___x_3507_);
return v___x_3508_;
}
}
v___jp_3511_:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_Syntax_getTailPos_x3f(v_ref_3510_, v___x_3491_);
lean_dec(v_ref_3510_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_inc(v___y_3512_);
v___y_3499_ = v___y_3512_;
v___y_3500_ = v___y_3512_;
goto v___jp_3498_;
}
else
{
lean_object* v_val_3514_; 
v_val_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_val_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___y_3499_ = v___y_3512_;
v___y_3500_ = v_val_3514_;
goto v___jp_3498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7___boxed(lean_object* v_traceElem_3519_, lean_object* v___f_3520_, lean_object* v___f_3521_, lean_object* v_____s_3522_, lean_object* v_toPure_3523_, lean_object* v___x_3524_, lean_object* v_____do__lift_3525_){
_start:
{
uint8_t v___x_1103__boxed_3526_; lean_object* v_res_3527_; 
v___x_1103__boxed_3526_ = lean_unbox(v___x_3524_);
v_res_3527_ = l_Lean_addTraceAsMessages___redArg___lam__7(v_traceElem_3519_, v___f_3520_, v___f_3521_, v_____s_3522_, v_toPure_3523_, v___x_1103__boxed_3526_, v_____do__lift_3525_);
lean_dec(v_____do__lift_3525_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object* v_inst_3528_, lean_object* v___f_3529_, lean_object* v___f_3530_, lean_object* v_toPure_3531_, uint8_t v___x_3532_, lean_object* v_toBind_3533_, lean_object* v_traceElem_3534_, lean_object* v_____s_3535_){
_start:
{
lean_object* v_getRef_3536_; lean_object* v___x_3537_; lean_object* v___f_3538_; lean_object* v___x_3539_; 
v_getRef_3536_ = lean_ctor_get(v_inst_3528_, 0);
lean_inc(v_getRef_3536_);
lean_dec_ref(v_inst_3528_);
v___x_3537_ = lean_box(v___x_3532_);
v___f_3538_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__7___boxed), 7, 6);
lean_closure_set(v___f_3538_, 0, v_traceElem_3534_);
lean_closure_set(v___f_3538_, 1, v___f_3529_);
lean_closure_set(v___f_3538_, 2, v___f_3530_);
lean_closure_set(v___f_3538_, 3, v_____s_3535_);
lean_closure_set(v___f_3538_, 4, v_toPure_3531_);
lean_closure_set(v___f_3538_, 5, v___x_3537_);
v___x_3539_ = lean_apply_4(v_toBind_3533_, lean_box(0), lean_box(0), v_getRef_3536_, v___f_3538_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object* v_inst_3540_, lean_object* v___f_3541_, lean_object* v___f_3542_, lean_object* v_toPure_3543_, lean_object* v___x_3544_, lean_object* v_toBind_3545_, lean_object* v_traceElem_3546_, lean_object* v_____s_3547_){
_start:
{
uint8_t v___x_1163__boxed_3548_; lean_object* v_res_3549_; 
v___x_1163__boxed_3548_ = lean_unbox(v___x_3544_);
v_res_3549_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_inst_3540_, v___f_3541_, v___f_3542_, v_toPure_3543_, v___x_1163__boxed_3548_, v_toBind_3545_, v_traceElem_3546_, v_____s_3547_);
return v_res_3549_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__0(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___f_3551_; 
v___x_3550_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_3551_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3551_, 0, v___x_3550_);
return v___f_3551_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__1(void){
_start:
{
lean_object* v___f_3552_; lean_object* v___f_3553_; 
v___f_3552_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__0, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__0_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__0);
v___f_3553_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3553_, 0, v___f_3552_);
lean_closure_set(v___f_3553_, 1, v___f_3552_);
return v___f_3553_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__2(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = lean_box(0);
v___x_3555_ = lean_unsigned_to_nat(16u);
v___x_3556_ = lean_mk_array(v___x_3555_, v___x_3554_);
return v___x_3556_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__3(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v_pos2traces_3559_; 
v___x_3557_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__2, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__2_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__2);
v___x_3558_ = lean_unsigned_to_nat(0u);
v_pos2traces_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_3559_, 0, v___x_3558_);
lean_ctor_set(v_pos2traces_3559_, 1, v___x_3557_);
return v_pos2traces_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object* v_inst_3560_, lean_object* v___f_3561_, lean_object* v_toPure_3562_, lean_object* v_toBind_3563_, lean_object* v_inst_3564_, lean_object* v___f_3565_, lean_object* v_traces_3566_){
_start:
{
uint8_t v___x_3567_; 
v___x_3567_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___f_3568_; lean_object* v___x_3569_; lean_object* v___f_3570_; lean_object* v_pos2traces_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___f_3568_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__1, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__1_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__1);
v___x_3569_ = lean_box(v___x_3567_);
lean_inc(v_toBind_3563_);
v___f_3570_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__8___boxed), 8, 6);
lean_closure_set(v___f_3570_, 0, v_inst_3560_);
lean_closure_set(v___f_3570_, 1, v___f_3568_);
lean_closure_set(v___f_3570_, 2, v___f_3561_);
lean_closure_set(v___f_3570_, 3, v_toPure_3562_);
lean_closure_set(v___f_3570_, 4, v___x_3569_);
lean_closure_set(v___f_3570_, 5, v_toBind_3563_);
v_pos2traces_3571_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__3, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__3_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__3);
v___x_3572_ = l_Lean_PersistentArray_forIn___redArg(v_inst_3564_, v_traces_3566_, v_pos2traces_3571_, v___f_3570_);
v___x_3573_ = lean_apply_4(v_toBind_3563_, lean_box(0), lean_box(0), v___x_3572_, v___f_3565_);
return v___x_3573_;
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_dec(v___f_3565_);
lean_dec_ref(v_inst_3564_);
lean_dec(v_toBind_3563_);
lean_dec_ref(v___f_3561_);
lean_dec_ref(v_inst_3560_);
v___x_3574_ = lean_box(0);
v___x_3575_ = lean_apply_2(v_toPure_3562_, lean_box(0), v___x_3574_);
return v___x_3575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object* v_inst_3576_, lean_object* v___f_3577_, lean_object* v_toPure_3578_, lean_object* v_toBind_3579_, lean_object* v_inst_3580_, lean_object* v___f_3581_, lean_object* v_traces_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Lean_addTraceAsMessages___redArg___lam__9(v_inst_3576_, v___f_3577_, v_toPure_3578_, v_toBind_3579_, v_inst_3580_, v___f_3581_, v_traces_3582_);
lean_dec_ref(v_traces_3582_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object* v_toPure_3584_, lean_object* v_logMessage_3585_, lean_object* v_toBind_3586_, lean_object* v_toMonadFileMap_3587_, lean_object* v_getFileName_3588_, lean_object* v_inst_3589_, lean_object* v___f_3590_, lean_object* v___f_3591_, lean_object* v___f_3592_, lean_object* v_inst_3593_, lean_object* v___f_3594_, lean_object* v_inst_3595_, lean_object* v_____do__lift_3596_){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3600_ = l_Lean_KVMap_instValueBool;
v___x_3601_ = l_Lean_KVMap_instValueString;
v___x_3602_ = l_Lean_trace_profiler_output;
v___x_3603_ = l_Lean_Option_get_x3f___redArg(v___x_3601_, v_____do__lift_3596_, v___x_3602_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v___x_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3604_ = l_Lean_trace_profiler_serve;
v___x_3605_ = l_Lean_Option_get___redArg(v___x_3600_, v_____do__lift_3596_, v___x_3604_);
v___x_3606_ = lean_unbox(v___x_3605_);
lean_dec(v___x_3605_);
if (v___x_3606_ == 0)
{
uint8_t v___x_3607_; lean_object* v___x_3608_; lean_object* v___f_3609_; lean_object* v___f_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3607_ = 1;
v___x_3608_ = lean_box(v___x_3607_);
lean_inc_ref_n(v_inst_3589_, 2);
lean_inc_n(v_toBind_3586_, 2);
lean_inc(v_toPure_3584_);
v___f_3609_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_3609_, 0, v_toPure_3584_);
lean_closure_set(v___f_3609_, 1, v___x_3608_);
lean_closure_set(v___f_3609_, 2, v_logMessage_3585_);
lean_closure_set(v___f_3609_, 3, v_toBind_3586_);
lean_closure_set(v___f_3609_, 4, v_toMonadFileMap_3587_);
lean_closure_set(v___f_3609_, 5, v_getFileName_3588_);
lean_closure_set(v___f_3609_, 6, v_inst_3589_);
lean_closure_set(v___f_3609_, 7, v___f_3590_);
lean_closure_set(v___f_3609_, 8, v___f_3591_);
lean_closure_set(v___f_3609_, 9, v___f_3592_);
v___f_3610_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_3610_, 0, v_inst_3593_);
lean_closure_set(v___f_3610_, 1, v___f_3594_);
lean_closure_set(v___f_3610_, 2, v_toPure_3584_);
lean_closure_set(v___f_3610_, 3, v_toBind_3586_);
lean_closure_set(v___f_3610_, 4, v_inst_3589_);
lean_closure_set(v___f_3610_, 5, v___f_3609_);
v___x_3611_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3589_, v_inst_3595_);
v___x_3612_ = lean_apply_4(v_toBind_3586_, lean_box(0), lean_box(0), v___x_3611_, v___f_3610_);
return v___x_3612_;
}
else
{
lean_dec_ref(v_inst_3595_);
lean_dec_ref(v___f_3594_);
lean_dec_ref(v_inst_3593_);
lean_dec_ref(v___f_3592_);
lean_dec_ref(v___f_3591_);
lean_dec(v___f_3590_);
lean_dec_ref(v_inst_3589_);
lean_dec(v_getFileName_3588_);
lean_dec(v_toMonadFileMap_3587_);
lean_dec(v_toBind_3586_);
lean_dec(v_logMessage_3585_);
goto v___jp_3597_;
}
}
else
{
lean_dec_ref_known(v___x_3603_, 1);
lean_dec_ref(v_inst_3595_);
lean_dec_ref(v___f_3594_);
lean_dec_ref(v_inst_3593_);
lean_dec_ref(v___f_3592_);
lean_dec_ref(v___f_3591_);
lean_dec(v___f_3590_);
lean_dec_ref(v_inst_3589_);
lean_dec(v_getFileName_3588_);
lean_dec(v_toMonadFileMap_3587_);
lean_dec(v_toBind_3586_);
lean_dec(v_logMessage_3585_);
goto v___jp_3597_;
}
v___jp_3597_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = lean_box(0);
v___x_3599_ = lean_apply_2(v_toPure_3584_, lean_box(0), v___x_3598_);
return v___x_3599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object* v_toPure_3613_, lean_object* v_logMessage_3614_, lean_object* v_toBind_3615_, lean_object* v_toMonadFileMap_3616_, lean_object* v_getFileName_3617_, lean_object* v_inst_3618_, lean_object* v___f_3619_, lean_object* v___f_3620_, lean_object* v___f_3621_, lean_object* v_inst_3622_, lean_object* v___f_3623_, lean_object* v_inst_3624_, lean_object* v_____do__lift_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Lean_addTraceAsMessages___redArg___lam__10(v_toPure_3613_, v_logMessage_3614_, v_toBind_3615_, v_toMonadFileMap_3616_, v_getFileName_3617_, v_inst_3618_, v___f_3619_, v___f_3620_, v___f_3621_, v_inst_3622_, v___f_3623_, v_inst_3624_, v_____do__lift_3625_);
lean_dec_ref(v_____do__lift_3625_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object* v_inst_3632_, lean_object* v_inst_3633_, lean_object* v_inst_3634_, lean_object* v_inst_3635_, lean_object* v_inst_3636_){
_start:
{
lean_object* v___f_3637_; lean_object* v_toApplicative_3638_; lean_object* v_toBind_3639_; lean_object* v_getOptionsUnrestricted_3640_; lean_object* v_toPure_3641_; lean_object* v_toMonadFileMap_3642_; lean_object* v_getFileName_3643_; lean_object* v_logMessage_3644_; lean_object* v___f_3645_; lean_object* v___f_3646_; lean_object* v___f_3647_; lean_object* v___f_3648_; lean_object* v___x_3649_; 
v___f_3637_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__1));
v_toApplicative_3638_ = lean_ctor_get(v_inst_3633_, 0);
v_toBind_3639_ = lean_ctor_get(v_inst_3633_, 1);
lean_inc_n(v_toBind_3639_, 2);
v_getOptionsUnrestricted_3640_ = lean_ctor_get(v_inst_3632_, 1);
lean_inc(v_getOptionsUnrestricted_3640_);
lean_dec_ref(v_inst_3632_);
v_toPure_3641_ = lean_ctor_get(v_toApplicative_3638_, 1);
lean_inc_n(v_toPure_3641_, 2);
v_toMonadFileMap_3642_ = lean_ctor_get(v_inst_3635_, 0);
lean_inc(v_toMonadFileMap_3642_);
v_getFileName_3643_ = lean_ctor_get(v_inst_3635_, 2);
lean_inc(v_getFileName_3643_);
v_logMessage_3644_ = lean_ctor_get(v_inst_3635_, 4);
lean_inc(v_logMessage_3644_);
lean_dec_ref(v_inst_3635_);
v___f_3645_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__2));
v___f_3646_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__3));
v___f_3647_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3647_, 0, v_toPure_3641_);
v___f_3648_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__10___boxed), 13, 12);
lean_closure_set(v___f_3648_, 0, v_toPure_3641_);
lean_closure_set(v___f_3648_, 1, v_logMessage_3644_);
lean_closure_set(v___f_3648_, 2, v_toBind_3639_);
lean_closure_set(v___f_3648_, 3, v_toMonadFileMap_3642_);
lean_closure_set(v___f_3648_, 4, v_getFileName_3643_);
lean_closure_set(v___f_3648_, 5, v_inst_3633_);
lean_closure_set(v___f_3648_, 6, v___f_3647_);
lean_closure_set(v___f_3648_, 7, v___f_3645_);
lean_closure_set(v___f_3648_, 8, v___f_3646_);
lean_closure_set(v___f_3648_, 9, v_inst_3634_);
lean_closure_set(v___f_3648_, 10, v___f_3637_);
lean_closure_set(v___f_3648_, 11, v_inst_3636_);
v___x_3649_ = lean_apply_4(v_toBind_3639_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3640_, v___f_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object* v_m_3650_, lean_object* v_inst_3651_, lean_object* v_inst_3652_, lean_object* v_inst_3653_, lean_object* v_inst_3654_, lean_object* v_inst_3655_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_addTraceAsMessages___redArg(v_inst_3651_, v_inst_3652_, v_inst_3653_, v_inst_3654_, v_inst_3655_);
return v___x_3656_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3698_ = lean_unsigned_to_nat(2826257906u);
v___x_3699_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3700_ = l_Lean_Name_num___override(v___x_3699_, v___x_3698_);
return v___x_3700_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3702_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3703_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3704_ = l_Lean_Name_str___override(v___x_3703_, v___x_3702_);
return v___x_3704_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3706_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3707_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3708_ = l_Lean_Name_str___override(v___x_3707_, v___x_3706_);
return v___x_3708_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3709_ = lean_unsigned_to_nat(2u);
v___x_3710_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3711_ = l_Lean_Name_num___override(v___x_3710_, v___x_3709_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3713_; uint8_t v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3713_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3714_ = 0;
v___x_3715_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3716_ = l_Lean_registerTraceClass(v___x_3713_, v___x_3714_, v___x_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object* v_a_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
return v_res_3718_;
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
