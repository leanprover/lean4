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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
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
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_MessageData_format___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BaseIO_toIO___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueString;
lean_object* l_Lean_Option_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_262_, 1);
if (lean_obj_tag(v_val_263_) == 1)
{
uint8_t v_v_264_; 
v_v_264_ = lean_ctor_get_uint8(v_val_263_, 0);
lean_dec_ref_known(v_val_263_, 0);
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
uint8_t v_hasTrace_351_; uint8_t v___x_352_; 
v_hasTrace_351_ = lean_ctor_get_uint8(v_opts_348_, sizeof(void*)*1);
v___x_352_ = lean_bool_not(v_hasTrace_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = l_Lean_inheritedTraceOptions;
v___x_354_ = lean_st_ref_get(v___x_353_);
if (v_hasTrace_351_ == 0)
{
lean_dec(v___x_354_);
lean_dec(v_cls_349_);
lean_dec_ref(v_opts_348_);
return v_hasTrace_351_;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_355_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_356_ = l_Lean_Name_append(v___x_355_, v_cls_349_);
v___x_357_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_354_, v_opts_348_, v___x_356_);
lean_dec(v___x_356_);
lean_dec_ref(v_opts_348_);
lean_dec(v___x_354_);
return v___x_357_;
}
}
else
{
uint8_t v___x_358_; 
lean_dec(v_cls_349_);
lean_dec_ref(v_opts_348_);
v___x_358_ = 0;
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object* v_opts_359_, lean_object* v_cls_360_, lean_object* v_a_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = lean_is_trace_class_enabled(v_opts_359_, v_cls_360_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object* v_toPure_364_, lean_object* v_s_365_){
_start:
{
lean_object* v_traces_366_; lean_object* v___x_367_; 
v_traces_366_ = lean_ctor_get(v_s_365_, 0);
lean_inc_ref(v_traces_366_);
lean_dec_ref(v_s_365_);
v___x_367_ = lean_apply_2(v_toPure_364_, lean_box(0), v_traces_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object* v_inst_368_, lean_object* v_inst_369_){
_start:
{
lean_object* v_toApplicative_370_; lean_object* v_toBind_371_; lean_object* v_getTraceState_372_; lean_object* v_toPure_373_; lean_object* v___f_374_; lean_object* v___x_375_; 
v_toApplicative_370_ = lean_ctor_get(v_inst_368_, 0);
lean_inc_ref(v_toApplicative_370_);
v_toBind_371_ = lean_ctor_get(v_inst_368_, 1);
lean_inc(v_toBind_371_);
lean_dec_ref(v_inst_368_);
v_getTraceState_372_ = lean_ctor_get(v_inst_369_, 1);
lean_inc(v_getTraceState_372_);
lean_dec_ref(v_inst_369_);
v_toPure_373_ = lean_ctor_get(v_toApplicative_370_, 1);
lean_inc(v_toPure_373_);
lean_dec_ref(v_toApplicative_370_);
v___f_374_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_374_, 0, v_toPure_373_);
v___x_375_ = lean_apply_4(v_toBind_371_, lean_box(0), lean_box(0), v_getTraceState_372_, v___f_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object* v_m_376_, lean_object* v_inst_377_, lean_object* v_inst_378_){
_start:
{
lean_object* v_toApplicative_379_; lean_object* v_toBind_380_; lean_object* v_getTraceState_381_; lean_object* v_toPure_382_; lean_object* v___f_383_; lean_object* v___x_384_; 
v_toApplicative_379_ = lean_ctor_get(v_inst_377_, 0);
lean_inc_ref(v_toApplicative_379_);
v_toBind_380_ = lean_ctor_get(v_inst_377_, 1);
lean_inc(v_toBind_380_);
lean_dec_ref(v_inst_377_);
v_getTraceState_381_ = lean_ctor_get(v_inst_378_, 1);
lean_inc(v_getTraceState_381_);
lean_dec_ref(v_inst_378_);
v_toPure_382_ = lean_ctor_get(v_toApplicative_379_, 1);
lean_inc(v_toPure_382_);
lean_dec_ref(v_toApplicative_379_);
v___f_383_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_383_, 0, v_toPure_382_);
v___x_384_ = lean_apply_4(v_toBind_380_, lean_box(0), lean_box(0), v_getTraceState_381_, v___f_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object* v_f_385_, lean_object* v_s_386_){
_start:
{
uint64_t v_tid_387_; lean_object* v_traces_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
v_tid_387_ = lean_ctor_get_uint64(v_s_386_, sizeof(void*)*1);
v_traces_388_ = lean_ctor_get(v_s_386_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_s_386_);
if (v_isSharedCheck_396_ == 0)
{
v___x_390_ = v_s_386_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_traces_388_);
lean_dec(v_s_386_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_apply_1(v_f_385_, v_traces_388_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
lean_ctor_set_uint64(v_reuseFailAlloc_395_, sizeof(void*)*1, v_tid_387_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object* v_inst_397_, lean_object* v_f_398_){
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
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object* v_m_402_, lean_object* v_inst_403_, lean_object* v_f_404_){
_start:
{
lean_object* v_modifyTraceState_405_; lean_object* v___f_406_; lean_object* v___x_407_; 
v_modifyTraceState_405_ = lean_ctor_get(v_inst_403_, 0);
lean_inc(v_modifyTraceState_405_);
lean_dec_ref(v_inst_403_);
v___f_406_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_406_, 0, v_f_404_);
v___x_407_ = lean_apply_1(v_modifyTraceState_405_, v___f_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object* v_s_408_, lean_object* v_x_409_){
_start:
{
lean_inc_ref(v_s_408_);
return v_s_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object* v_s_410_, lean_object* v_x_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_setTraceState___redArg___lam__0(v_s_410_, v_x_411_);
lean_dec_ref(v_x_411_);
lean_dec_ref(v_s_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object* v_inst_413_, lean_object* v_s_414_){
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
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object* v_m_418_, lean_object* v_inst_419_, lean_object* v_s_420_){
_start:
{
lean_object* v_modifyTraceState_421_; lean_object* v___f_422_; lean_object* v___x_423_; 
v_modifyTraceState_421_ = lean_ctor_get(v_inst_419_, 0);
lean_inc(v_modifyTraceState_421_);
lean_dec_ref(v_inst_419_);
v___f_422_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_422_, 0, v_s_420_);
v___x_423_ = lean_apply_1(v_modifyTraceState_421_, v___f_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object* v_s_424_){
_start:
{
uint64_t v_tid_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_435_; 
v_tid_425_ = lean_ctor_get_uint64(v_s_424_, sizeof(void*)*1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_s_424_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; 
v_unused_436_ = lean_ctor_get(v_s_424_, 0);
lean_dec(v_unused_436_);
v___x_427_ = v_s_424_;
v_isShared_428_ = v_isSharedCheck_435_;
goto v_resetjp_426_;
}
else
{
lean_dec(v_s_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_435_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_429_ = lean_unsigned_to_nat(32u);
v___x_430_ = lean_mk_empty_array_with_capacity(v___x_429_);
lean_dec_ref(v___x_430_);
v___x_431_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__1, &l_Lean_instInhabitedTraceState_default___closed__1_once, _init_l_Lean_instInhabitedTraceState_default___closed__1);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_431_);
v___x_433_ = v___x_427_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
lean_ctor_set_uint64(v_reuseFailAlloc_434_, sizeof(void*)*1, v_tid_425_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object* v_toPure_437_, lean_object* v_oldTraces_438_, lean_object* v_____r_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = lean_apply_2(v_toPure_437_, lean_box(0), v_oldTraces_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object* v_toPure_441_, lean_object* v_modifyTraceState_442_, lean_object* v___f_443_, lean_object* v_toBind_444_, lean_object* v_oldTraces_445_){
_start:
{
lean_object* v___f_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___f_446_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_446_, 0, v_toPure_441_);
lean_closure_set(v___f_446_, 1, v_oldTraces_445_);
v___x_447_ = lean_apply_1(v_modifyTraceState_442_, v___f_443_);
v___x_448_ = lean_apply_4(v_toBind_444_, lean_box(0), lean_box(0), v___x_447_, v___f_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object* v_inst_450_, lean_object* v_inst_451_){
_start:
{
lean_object* v_toApplicative_452_; lean_object* v_toBind_453_; lean_object* v_modifyTraceState_454_; lean_object* v_getTraceState_455_; lean_object* v_toPure_456_; lean_object* v___f_457_; lean_object* v___f_458_; lean_object* v___f_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_toApplicative_452_ = lean_ctor_get(v_inst_450_, 0);
lean_inc_ref(v_toApplicative_452_);
v_toBind_453_ = lean_ctor_get(v_inst_450_, 1);
lean_inc_n(v_toBind_453_, 3);
lean_dec_ref(v_inst_450_);
v_modifyTraceState_454_ = lean_ctor_get(v_inst_451_, 0);
lean_inc(v_modifyTraceState_454_);
v_getTraceState_455_ = lean_ctor_get(v_inst_451_, 1);
lean_inc(v_getTraceState_455_);
lean_dec_ref(v_inst_451_);
v_toPure_456_ = lean_ctor_get(v_toApplicative_452_, 1);
lean_inc_n(v_toPure_456_, 2);
lean_dec_ref(v_toApplicative_452_);
v___f_457_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0));
v___f_458_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_458_, 0, v_toPure_456_);
lean_closure_set(v___f_458_, 1, v_modifyTraceState_454_);
lean_closure_set(v___f_458_, 2, v___f_457_);
lean_closure_set(v___f_458_, 3, v_toBind_453_);
v___f_459_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_459_, 0, v_toPure_456_);
v___x_460_ = lean_apply_4(v_toBind_453_, lean_box(0), lean_box(0), v_getTraceState_455_, v___f_459_);
v___x_461_ = lean_apply_4(v_toBind_453_, lean_box(0), lean_box(0), v___x_460_, v___f_458_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object* v_m_462_, lean_object* v_inst_463_, lean_object* v_inst_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_463_, v_inst_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object* v_ref_466_, lean_object* v_msg_467_, lean_object* v_s_468_){
_start:
{
uint64_t v_tid_469_; lean_object* v_traces_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_479_; 
v_tid_469_ = lean_ctor_get_uint64(v_s_468_, sizeof(void*)*1);
v_traces_470_ = lean_ctor_get(v_s_468_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_s_468_);
if (v_isSharedCheck_479_ == 0)
{
v___x_472_ = v_s_468_;
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_traces_470_);
lean_dec(v_s_468_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v_ref_466_);
lean_ctor_set(v___x_474_, 1, v_msg_467_);
v___x_475_ = l_Lean_PersistentArray_push___redArg(v_traces_470_, v___x_474_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
lean_ctor_set_uint64(v_reuseFailAlloc_478_, sizeof(void*)*1, v_tid_469_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object* v_inst_480_, lean_object* v_ref_481_, lean_object* v_msg_482_){
_start:
{
lean_object* v_modifyTraceState_483_; lean_object* v___f_484_; lean_object* v___x_485_; 
v_modifyTraceState_483_ = lean_ctor_get(v_inst_480_, 0);
lean_inc(v_modifyTraceState_483_);
lean_dec_ref(v_inst_480_);
v___f_484_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__0), 3, 2);
lean_closure_set(v___f_484_, 0, v_ref_481_);
lean_closure_set(v___f_484_, 1, v_msg_482_);
v___x_485_ = lean_apply_1(v_modifyTraceState_483_, v___f_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_msg_488_, lean_object* v_toBind_489_, lean_object* v_ref_490_){
_start:
{
lean_object* v___f_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___f_491_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__1), 3, 2);
lean_closure_set(v___f_491_, 0, v_inst_486_);
lean_closure_set(v___f_491_, 1, v_ref_490_);
v___x_492_ = lean_apply_1(v_inst_487_, v_msg_488_);
v___x_493_ = lean_apply_4(v_toBind_489_, lean_box(0), lean_box(0), v___x_492_, v___f_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_msg_498_){
_start:
{
lean_object* v_toBind_499_; lean_object* v_getRef_500_; lean_object* v___f_501_; lean_object* v___x_502_; 
v_toBind_499_ = lean_ctor_get(v_inst_494_, 1);
lean_inc_n(v_toBind_499_, 2);
lean_dec_ref(v_inst_494_);
v_getRef_500_ = lean_ctor_get(v_inst_496_, 0);
lean_inc(v_getRef_500_);
lean_dec_ref(v_inst_496_);
v___f_501_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__2), 5, 4);
lean_closure_set(v___f_501_, 0, v_inst_495_);
lean_closure_set(v___f_501_, 1, v_inst_497_);
lean_closure_set(v___f_501_, 2, v_msg_498_);
lean_closure_set(v___f_501_, 3, v_toBind_499_);
v___x_502_ = lean_apply_4(v_toBind_499_, lean_box(0), lean_box(0), v_getRef_500_, v___f_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object* v_m_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_msg_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_addRawTrace___redArg(v_inst_504_, v_inst_505_, v_inst_506_, v_inst_507_, v_msg_508_);
return v___x_509_;
}
}
static double _init_l_Lean_addTrace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_510_; double v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_float_of_nat(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object* v_cls_515_, lean_object* v_msg_516_, lean_object* v_ref_517_, lean_object* v_s_518_){
_start:
{
uint64_t v_tid_519_; lean_object* v_traces_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_536_; 
v_tid_519_ = lean_ctor_get_uint64(v_s_518_, sizeof(void*)*1);
v_traces_520_ = lean_ctor_get(v_s_518_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_s_518_);
if (v_isSharedCheck_536_ == 0)
{
v___x_522_ = v_s_518_;
v_isShared_523_ = v_isSharedCheck_536_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_traces_520_);
lean_dec(v_s_518_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_536_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; double v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_524_ = lean_box(0);
v___x_525_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
v___x_526_ = 0;
v___x_527_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_528_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_528_, 0, v_cls_515_);
lean_ctor_set(v___x_528_, 1, v___x_524_);
lean_ctor_set(v___x_528_, 2, v___x_527_);
lean_ctor_set_float(v___x_528_, sizeof(void*)*3, v___x_525_);
lean_ctor_set_float(v___x_528_, sizeof(void*)*3 + 8, v___x_525_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*3 + 16, v___x_526_);
v___x_529_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
v___x_530_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v_msg_516_);
lean_ctor_set(v___x_530_, 2, v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_ref_517_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_PersistentArray_push___redArg(v_traces_520_, v___x_531_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_532_);
v___x_534_ = v___x_522_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
lean_ctor_set_uint64(v_reuseFailAlloc_535_, sizeof(void*)*1, v_tid_519_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object* v_inst_537_, lean_object* v_cls_538_, lean_object* v_ref_539_, lean_object* v_msg_540_){
_start:
{
lean_object* v_modifyTraceState_541_; lean_object* v___f_542_; lean_object* v___x_543_; 
v_modifyTraceState_541_ = lean_ctor_get(v_inst_537_, 0);
lean_inc(v_modifyTraceState_541_);
lean_dec_ref(v_inst_537_);
v___f_542_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_542_, 0, v_cls_538_);
lean_closure_set(v___f_542_, 1, v_msg_540_);
lean_closure_set(v___f_542_, 2, v_ref_539_);
v___x_543_ = lean_apply_1(v_modifyTraceState_541_, v___f_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object* v_inst_544_, lean_object* v_cls_545_, lean_object* v_inst_546_, lean_object* v_msg_547_, lean_object* v_toBind_548_, lean_object* v_ref_549_){
_start:
{
lean_object* v___f_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___f_550_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__1), 4, 3);
lean_closure_set(v___f_550_, 0, v_inst_544_);
lean_closure_set(v___f_550_, 1, v_cls_545_);
lean_closure_set(v___f_550_, 2, v_ref_549_);
v___x_551_ = lean_apply_1(v_inst_546_, v_msg_547_);
v___x_552_ = lean_apply_4(v_toBind_548_, lean_box(0), lean_box(0), v___x_551_, v___f_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_inst_556_, lean_object* v_cls_557_, lean_object* v_msg_558_){
_start:
{
lean_object* v_toBind_559_; lean_object* v_getRef_560_; lean_object* v___f_561_; lean_object* v___x_562_; 
v_toBind_559_ = lean_ctor_get(v_inst_553_, 1);
lean_inc_n(v_toBind_559_, 2);
lean_dec_ref(v_inst_553_);
v_getRef_560_ = lean_ctor_get(v_inst_555_, 0);
lean_inc(v_getRef_560_);
lean_dec_ref(v_inst_555_);
v___f_561_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__2), 6, 5);
lean_closure_set(v___f_561_, 0, v_inst_554_);
lean_closure_set(v___f_561_, 1, v_cls_557_);
lean_closure_set(v___f_561_, 2, v_inst_556_);
lean_closure_set(v___f_561_, 3, v_msg_558_);
lean_closure_set(v___f_561_, 4, v_toBind_559_);
v___x_562_ = lean_apply_4(v_toBind_559_, lean_box(0), lean_box(0), v_getRef_560_, v___f_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object* v_m_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_cls_568_, lean_object* v_msg_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_addTrace___redArg(v_inst_564_, v_inst_565_, v_inst_566_, v_inst_567_, v_cls_568_, v_msg_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0(lean_object* v_toPure_571_, lean_object* v_msg_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_cls_577_, uint8_t v_____do__lift_578_){
_start:
{
if (v_____do__lift_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_cls_577_);
lean_dec(v_inst_576_);
lean_dec_ref(v_inst_575_);
lean_dec_ref(v_inst_574_);
lean_dec_ref(v_inst_573_);
lean_dec_ref(v_msg_572_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_apply_2(v_toPure_571_, lean_box(0), v___x_579_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_toPure_571_);
v___x_581_ = lean_box(0);
v___x_582_ = lean_apply_1(v_msg_572_, v___x_581_);
v___x_583_ = l_Lean_addTrace___redArg(v_inst_573_, v_inst_574_, v_inst_575_, v_inst_576_, v_cls_577_, v___x_582_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object* v_toPure_584_, lean_object* v_msg_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_cls_590_, lean_object* v_____do__lift_591_){
_start:
{
uint8_t v_____do__lift_148__boxed_592_; lean_object* v_res_593_; 
v_____do__lift_148__boxed_592_ = lean_unbox(v_____do__lift_591_);
v_res_593_ = l_Lean_trace___redArg___lam__0(v_toPure_584_, v_msg_585_, v_inst_586_, v_inst_587_, v_inst_588_, v_inst_589_, v_cls_590_, v_____do__lift_148__boxed_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_cls_599_, lean_object* v_msg_600_){
_start:
{
lean_object* v_toApplicative_601_; lean_object* v_toBind_602_; lean_object* v_getInheritedTraceOptions_603_; lean_object* v_toPure_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_toApplicative_601_ = lean_ctor_get(v_inst_594_, 0);
v_toBind_602_ = lean_ctor_get(v_inst_594_, 1);
lean_inc_n(v_toBind_602_, 3);
v_getInheritedTraceOptions_603_ = lean_ctor_get(v_inst_595_, 2);
lean_inc(v_getInheritedTraceOptions_603_);
v_toPure_604_ = lean_ctor_get(v_toApplicative_601_, 1);
lean_inc_n(v_toPure_604_, 2);
lean_inc(v_cls_599_);
v___f_605_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_605_, 0, v_toPure_604_);
lean_closure_set(v___f_605_, 1, v_msg_600_);
lean_closure_set(v___f_605_, 2, v_inst_594_);
lean_closure_set(v___f_605_, 3, v_inst_595_);
lean_closure_set(v___f_605_, 4, v_inst_596_);
lean_closure_set(v___f_605_, 5, v_inst_597_);
lean_closure_set(v___f_605_, 6, v_cls_599_);
v___f_606_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_606_, 0, v_toPure_604_);
lean_closure_set(v___f_606_, 1, v_cls_599_);
lean_closure_set(v___f_606_, 2, v_toBind_602_);
lean_closure_set(v___f_606_, 3, v_inst_598_);
v___x_607_ = lean_apply_4(v_toBind_602_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_603_, v___f_606_);
v___x_608_ = lean_apply_4(v_toBind_602_, lean_box(0), lean_box(0), v___x_607_, v___f_605_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace(lean_object* v_m_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_cls_615_, lean_object* v_msg_616_){
_start:
{
lean_object* v_toApplicative_617_; lean_object* v_toBind_618_; lean_object* v_getInheritedTraceOptions_619_; lean_object* v_toPure_620_; lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_toApplicative_617_ = lean_ctor_get(v_inst_610_, 0);
v_toBind_618_ = lean_ctor_get(v_inst_610_, 1);
lean_inc_n(v_toBind_618_, 3);
v_getInheritedTraceOptions_619_ = lean_ctor_get(v_inst_611_, 2);
lean_inc(v_getInheritedTraceOptions_619_);
v_toPure_620_ = lean_ctor_get(v_toApplicative_617_, 1);
lean_inc_n(v_toPure_620_, 2);
lean_inc(v_cls_615_);
v___f_621_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_621_, 0, v_toPure_620_);
lean_closure_set(v___f_621_, 1, v_msg_616_);
lean_closure_set(v___f_621_, 2, v_inst_610_);
lean_closure_set(v___f_621_, 3, v_inst_611_);
lean_closure_set(v___f_621_, 4, v_inst_612_);
lean_closure_set(v___f_621_, 5, v_inst_613_);
lean_closure_set(v___f_621_, 6, v_cls_615_);
v___f_622_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_622_, 0, v_toPure_620_);
lean_closure_set(v___f_622_, 1, v_cls_615_);
lean_closure_set(v___f_622_, 2, v_toBind_618_);
lean_closure_set(v___f_622_, 3, v_inst_614_);
v___x_623_ = lean_apply_4(v_toBind_618_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_619_, v___f_622_);
v___x_624_ = lean_apply_4(v_toBind_618_, lean_box(0), lean_box(0), v___x_623_, v___f_621_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_cls_629_, lean_object* v_msg_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_addTrace___redArg(v_inst_625_, v_inst_626_, v_inst_627_, v_inst_628_, v_cls_629_, v_msg_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1(lean_object* v_toPure_632_, lean_object* v_toBind_633_, lean_object* v_mkMsg_634_, lean_object* v___f_635_, uint8_t v_____do__lift_636_){
_start:
{
if (v_____do__lift_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v___f_635_);
lean_dec(v_mkMsg_634_);
lean_dec(v_toBind_633_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_apply_2(v_toPure_632_, lean_box(0), v___x_637_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
lean_dec(v_toPure_632_);
v___x_639_ = lean_apply_4(v_toBind_633_, lean_box(0), lean_box(0), v_mkMsg_634_, v___f_635_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object* v_toPure_640_, lean_object* v_toBind_641_, lean_object* v_mkMsg_642_, lean_object* v___f_643_, lean_object* v_____do__lift_644_){
_start:
{
uint8_t v_____do__lift_154__boxed_645_; lean_object* v_res_646_; 
v_____do__lift_154__boxed_645_ = lean_unbox(v_____do__lift_644_);
v_res_646_ = l_Lean_traceM___redArg___lam__1(v_toPure_640_, v_toBind_641_, v_mkMsg_642_, v___f_643_, v_____do__lift_154__boxed_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_cls_652_, lean_object* v_mkMsg_653_){
_start:
{
lean_object* v_toApplicative_654_; lean_object* v_toBind_655_; lean_object* v_getInheritedTraceOptions_656_; lean_object* v_toPure_657_; lean_object* v___f_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_toApplicative_654_ = lean_ctor_get(v_inst_647_, 0);
v_toBind_655_ = lean_ctor_get(v_inst_647_, 1);
lean_inc_n(v_toBind_655_, 4);
v_getInheritedTraceOptions_656_ = lean_ctor_get(v_inst_648_, 2);
lean_inc(v_getInheritedTraceOptions_656_);
v_toPure_657_ = lean_ctor_get(v_toApplicative_654_, 1);
lean_inc_n(v_toPure_657_, 2);
lean_inc(v_cls_652_);
v___f_658_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_658_, 0, v_inst_647_);
lean_closure_set(v___f_658_, 1, v_inst_648_);
lean_closure_set(v___f_658_, 2, v_inst_649_);
lean_closure_set(v___f_658_, 3, v_inst_650_);
lean_closure_set(v___f_658_, 4, v_cls_652_);
v___f_659_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_659_, 0, v_toPure_657_);
lean_closure_set(v___f_659_, 1, v_toBind_655_);
lean_closure_set(v___f_659_, 2, v_mkMsg_653_);
lean_closure_set(v___f_659_, 3, v___f_658_);
v___f_660_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_660_, 0, v_toPure_657_);
lean_closure_set(v___f_660_, 1, v_cls_652_);
lean_closure_set(v___f_660_, 2, v_toBind_655_);
lean_closure_set(v___f_660_, 3, v_inst_651_);
v___x_661_ = lean_apply_4(v_toBind_655_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_656_, v___f_660_);
v___x_662_ = lean_apply_4(v_toBind_655_, lean_box(0), lean_box(0), v___x_661_, v___f_659_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object* v_m_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_cls_669_, lean_object* v_mkMsg_670_){
_start:
{
lean_object* v_toApplicative_671_; lean_object* v_toBind_672_; lean_object* v_getInheritedTraceOptions_673_; lean_object* v_toPure_674_; lean_object* v___f_675_; lean_object* v___f_676_; lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_toApplicative_671_ = lean_ctor_get(v_inst_664_, 0);
v_toBind_672_ = lean_ctor_get(v_inst_664_, 1);
lean_inc_n(v_toBind_672_, 4);
v_getInheritedTraceOptions_673_ = lean_ctor_get(v_inst_665_, 2);
lean_inc(v_getInheritedTraceOptions_673_);
v_toPure_674_ = lean_ctor_get(v_toApplicative_671_, 1);
lean_inc_n(v_toPure_674_, 2);
lean_inc(v_cls_669_);
v___f_675_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_675_, 0, v_inst_664_);
lean_closure_set(v___f_675_, 1, v_inst_665_);
lean_closure_set(v___f_675_, 2, v_inst_666_);
lean_closure_set(v___f_675_, 3, v_inst_667_);
lean_closure_set(v___f_675_, 4, v_cls_669_);
v___f_676_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_676_, 0, v_toPure_674_);
lean_closure_set(v___f_676_, 1, v_toBind_672_);
lean_closure_set(v___f_676_, 2, v_mkMsg_670_);
lean_closure_set(v___f_676_, 3, v___f_675_);
v___f_677_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_677_, 0, v_toPure_674_);
lean_closure_set(v___f_677_, 1, v_cls_669_);
lean_closure_set(v___f_677_, 2, v_toBind_672_);
lean_closure_set(v___f_677_, 3, v_inst_668_);
v___x_678_ = lean_apply_4(v_toBind_672_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_673_, v___f_677_);
v___x_679_ = lean_apply_4(v_toBind_672_, lean_box(0), lean_box(0), v___x_678_, v___f_676_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object* v_x_680_){
_start:
{
lean_object* v_msg_681_; 
v_msg_681_ = lean_ctor_get(v_x_680_, 1);
lean_inc_ref(v_msg_681_);
return v_msg_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object* v_x_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_682_);
lean_dec_ref(v_x_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object* v_ref_684_, lean_object* v_msg_685_, lean_object* v_oldTraces_686_, lean_object* v_s_687_){
_start:
{
uint64_t v_tid_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_697_; 
v_tid_688_ = lean_ctor_get_uint64(v_s_687_, sizeof(void*)*1);
v_isSharedCheck_697_ = !lean_is_exclusive(v_s_687_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v_s_687_, 0);
lean_dec(v_unused_698_);
v___x_690_ = v_s_687_;
v_isShared_691_ = v_isSharedCheck_697_;
goto v_resetjp_689_;
}
else
{
lean_dec(v_s_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_697_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_ref_684_);
lean_ctor_set(v___x_692_, 1, v_msg_685_);
v___x_693_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_686_, v___x_692_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_693_);
v___x_695_ = v___x_690_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
lean_ctor_set_uint64(v_reuseFailAlloc_696_, sizeof(void*)*1, v_tid_688_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object* v_ref_699_, lean_object* v_oldTraces_700_, lean_object* v_modifyTraceState_701_, lean_object* v_msg_702_){
_start:
{
lean_object* v___f_703_; lean_object* v___x_704_; 
v___f_703_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0), 4, 3);
lean_closure_set(v___f_703_, 0, v_ref_699_);
lean_closure_set(v___f_703_, 1, v_msg_702_);
lean_closure_set(v___f_703_, 2, v_oldTraces_700_);
v___x_704_ = lean_apply_1(v_modifyTraceState_701_, v___f_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object* v___f_724_, lean_object* v_data_725_, lean_object* v_msg_726_, lean_object* v_inst_727_, lean_object* v_toBind_728_, lean_object* v___f_729_, lean_object* v_____do__lift_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; size_t v_sz_733_; size_t v___x_734_; lean_object* v___x_735_; lean_object* v_msg_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_731_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_730_);
v___x_732_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v_sz_733_ = lean_array_size(v___x_731_);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_732_, v___f_724_, v_sz_733_, v___x_734_, v___x_731_);
v_msg_736_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_736_, 0, v_data_725_);
lean_ctor_set(v_msg_736_, 1, v_msg_726_);
lean_ctor_set(v_msg_736_, 2, v___x_735_);
v___x_737_ = lean_apply_1(v_inst_727_, v_msg_736_);
v___x_738_ = lean_apply_4(v_toBind_728_, lean_box(0), lean_box(0), v___x_737_, v___f_729_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object* v___f_739_, lean_object* v_data_740_, lean_object* v_msg_741_, lean_object* v_inst_742_, lean_object* v_toBind_743_, lean_object* v___f_744_, lean_object* v_____do__lift_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(v___f_739_, v_data_740_, v_msg_741_, v_inst_742_, v_toBind_743_, v___f_744_, v_____do__lift_745_);
lean_dec_ref(v_____do__lift_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object* v_ref_747_, lean_object* v_withRef_748_, lean_object* v___x_749_, lean_object* v_oldRef_750_){
_start:
{
lean_object* v_ref_751_; lean_object* v___x_752_; 
v_ref_751_ = l_Lean_replaceRef(v_ref_747_, v_oldRef_750_);
v___x_752_ = lean_apply_3(v_withRef_748_, lean_box(0), v_ref_751_, v___x_749_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object* v_ref_753_, lean_object* v_withRef_754_, lean_object* v___x_755_, lean_object* v_oldRef_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(v_ref_753_, v_withRef_754_, v___x_755_, v_oldRef_756_);
lean_dec(v_oldRef_756_);
lean_dec(v_ref_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_oldTraces_763_, lean_object* v_data_764_, lean_object* v_ref_765_, lean_object* v_msg_766_){
_start:
{
lean_object* v_toApplicative_767_; lean_object* v_toBind_768_; lean_object* v_modifyTraceState_769_; lean_object* v_getTraceState_770_; lean_object* v_toPure_771_; lean_object* v_getRef_772_; lean_object* v_withRef_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___f_780_; lean_object* v___x_781_; 
v_toApplicative_767_ = lean_ctor_get(v_inst_759_, 0);
lean_inc_ref(v_toApplicative_767_);
v_toBind_768_ = lean_ctor_get(v_inst_759_, 1);
lean_inc_n(v_toBind_768_, 4);
lean_dec_ref(v_inst_759_);
v_modifyTraceState_769_ = lean_ctor_get(v_inst_760_, 0);
lean_inc(v_modifyTraceState_769_);
v_getTraceState_770_ = lean_ctor_get(v_inst_760_, 1);
lean_inc(v_getTraceState_770_);
lean_dec_ref(v_inst_760_);
v_toPure_771_ = lean_ctor_get(v_toApplicative_767_, 1);
lean_inc(v_toPure_771_);
lean_dec_ref(v_toApplicative_767_);
v_getRef_772_ = lean_ctor_get(v_inst_761_, 0);
lean_inc(v_getRef_772_);
v_withRef_773_ = lean_ctor_get(v_inst_761_, 1);
lean_inc(v_withRef_773_);
lean_dec_ref(v_inst_761_);
v___f_774_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_774_, 0, v_toPure_771_);
v___x_775_ = lean_apply_4(v_toBind_768_, lean_box(0), lean_box(0), v_getTraceState_770_, v___f_774_);
v___f_776_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0));
lean_inc(v_ref_765_);
v___f_777_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2), 4, 3);
lean_closure_set(v___f_777_, 0, v_ref_765_);
lean_closure_set(v___f_777_, 1, v_oldTraces_763_);
lean_closure_set(v___f_777_, 2, v_modifyTraceState_769_);
v___f_778_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_778_, 0, v___f_776_);
lean_closure_set(v___f_778_, 1, v_data_764_);
lean_closure_set(v___f_778_, 2, v_msg_766_);
lean_closure_set(v___f_778_, 3, v_inst_762_);
lean_closure_set(v___f_778_, 4, v_toBind_768_);
lean_closure_set(v___f_778_, 5, v___f_777_);
v___x_779_ = lean_apply_4(v_toBind_768_, lean_box(0), lean_box(0), v___x_775_, v___f_778_);
v___f_780_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_780_, 0, v_ref_765_);
lean_closure_set(v___f_780_, 1, v_withRef_773_);
lean_closure_set(v___f_780_, 2, v___x_779_);
v___x_781_ = lean_apply_4(v_toBind_768_, lean_box(0), lean_box(0), v_getRef_772_, v___f_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object* v_m_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_oldTraces_787_, lean_object* v_data_788_, lean_object* v_ref_789_, lean_object* v_msg_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_783_, v_inst_784_, v_inst_785_, v_inst_786_, v_oldTraces_787_, v_data_788_, v_ref_789_, v_msg_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object* v_name_792_, lean_object* v_decl_793_, lean_object* v_ref_794_){
_start:
{
lean_object* v_defValue_796_; lean_object* v_descr_797_; lean_object* v_deprecation_x3f_798_; lean_object* v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_defValue_796_ = lean_ctor_get(v_decl_793_, 0);
v_descr_797_ = lean_ctor_get(v_decl_793_, 1);
v_deprecation_x3f_798_ = lean_ctor_get(v_decl_793_, 2);
v___x_799_ = lean_alloc_ctor(1, 0, 1);
v___x_800_ = lean_unbox(v_defValue_796_);
lean_ctor_set_uint8(v___x_799_, 0, v___x_800_);
lean_inc(v_deprecation_x3f_798_);
lean_inc_ref(v_descr_797_);
lean_inc_n(v_name_792_, 2);
v___x_801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_801_, 0, v_name_792_);
lean_ctor_set(v___x_801_, 1, v_ref_794_);
lean_ctor_set(v___x_801_, 2, v___x_799_);
lean_ctor_set(v___x_801_, 3, v_descr_797_);
lean_ctor_set(v___x_801_, 4, v_deprecation_x3f_798_);
v___x_802_ = lean_register_option(v_name_792_, v___x_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_810_; 
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v___x_802_, 0);
lean_dec(v_unused_811_);
v___x_804_ = v___x_802_;
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
else
{
lean_dec(v___x_802_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
lean_inc(v_defValue_796_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_name_792_);
lean_ctor_set(v___x_806_, 1, v_defValue_796_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_806_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_name_792_);
v_a_812_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_802_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_802_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_820_, lean_object* v_decl_821_, lean_object* v_ref_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_820_, v_decl_821_, v_ref_822_);
lean_dec_ref(v_decl_821_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_840_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_841_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_842_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_843_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_840_, v___x_841_, v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object* v_name_846_, lean_object* v_decl_847_, lean_object* v_ref_848_){
_start:
{
lean_object* v_defValue_850_; lean_object* v_descr_851_; lean_object* v_deprecation_x3f_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_defValue_850_ = lean_ctor_get(v_decl_847_, 0);
v_descr_851_ = lean_ctor_get(v_decl_847_, 1);
v_deprecation_x3f_852_ = lean_ctor_get(v_decl_847_, 2);
lean_inc(v_defValue_850_);
v___x_853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_853_, 0, v_defValue_850_);
lean_inc(v_deprecation_x3f_852_);
lean_inc_ref(v_descr_851_);
lean_inc_n(v_name_846_, 2);
v___x_854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_854_, 0, v_name_846_);
lean_ctor_set(v___x_854_, 1, v_ref_848_);
lean_ctor_set(v___x_854_, 2, v___x_853_);
lean_ctor_set(v___x_854_, 3, v_descr_851_);
lean_ctor_set(v___x_854_, 4, v_deprecation_x3f_852_);
v___x_855_ = lean_register_option(v_name_846_, v___x_854_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_863_; 
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v___x_855_, 0);
lean_dec(v_unused_864_);
v___x_857_ = v___x_855_;
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
else
{
lean_dec(v___x_855_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
lean_inc(v_defValue_850_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_name_846_);
lean_ctor_set(v___x_859_, 1, v_defValue_850_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_859_);
v___x_861_ = v___x_857_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec(v_name_846_);
v_a_865_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_855_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_855_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_873_, lean_object* v_decl_874_, lean_object* v_ref_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_873_, v_decl_874_, v_ref_875_);
lean_dec_ref(v_decl_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_894_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_895_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_896_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_897_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_894_, v___x_895_, v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_917_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_918_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_919_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_920_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_917_, v___x_918_, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object* v_name_923_, lean_object* v_decl_924_, lean_object* v_ref_925_){
_start:
{
lean_object* v_defValue_927_; lean_object* v_descr_928_; lean_object* v_deprecation_x3f_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_defValue_927_ = lean_ctor_get(v_decl_924_, 0);
v_descr_928_ = lean_ctor_get(v_decl_924_, 1);
v_deprecation_x3f_929_ = lean_ctor_get(v_decl_924_, 2);
lean_inc(v_defValue_927_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v_defValue_927_);
lean_inc(v_deprecation_x3f_929_);
lean_inc_ref(v_descr_928_);
lean_inc_n(v_name_923_, 2);
v___x_931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_931_, 0, v_name_923_);
lean_ctor_set(v___x_931_, 1, v_ref_925_);
lean_ctor_set(v___x_931_, 2, v___x_930_);
lean_ctor_set(v___x_931_, 3, v_descr_928_);
lean_ctor_set(v___x_931_, 4, v_deprecation_x3f_929_);
v___x_932_ = lean_register_option(v_name_923_, v___x_931_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v___x_932_, 0);
lean_dec(v_unused_941_);
v___x_934_ = v___x_932_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_dec(v___x_932_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
lean_inc(v_defValue_927_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_name_923_);
lean_ctor_set(v___x_936_, 1, v_defValue_927_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_936_);
v___x_938_ = v___x_934_;
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
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_name_923_);
v_a_942_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_932_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_932_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_950_, lean_object* v_decl_951_, lean_object* v_ref_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_950_, v_decl_951_, v_ref_952_);
lean_dec_ref(v_decl_951_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_971_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_972_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_973_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_974_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_971_, v___x_972_, v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_994_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_995_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_996_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_997_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_994_, v___x_995_, v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4____boxed(lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
return v_res_999_;
}
}
LEAN_EXPORT uint8_t l_Lean_trace_profiler_isExporting(lean_object* v_opts_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1001_ = l_Lean_KVMap_instValueBool;
v___x_1002_ = l_Lean_KVMap_instValueString;
v___x_1003_ = l_Lean_trace_profiler_output;
v___x_1004_ = l_Lean_Option_get_x3f___redArg(v___x_1002_, v_opts_1000_, v___x_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = l_Lean_trace_profiler_serve;
v___x_1006_ = l_Lean_Option_get___redArg(v___x_1001_, v_opts_1000_, v___x_1005_);
v___x_1007_ = lean_unbox(v___x_1006_);
lean_dec(v___x_1006_);
return v___x_1007_;
}
else
{
uint8_t v___x_1008_; 
lean_dec_ref_known(v___x_1004_, 1);
v___x_1008_ = 1;
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_isExporting___boxed(lean_object* v_opts_1009_){
_start:
{
uint8_t v_res_1010_; lean_object* v_r_1011_; 
v_res_1010_ = l_Lean_trace_profiler_isExporting(v_opts_1009_);
lean_dec_ref(v_opts_1009_);
v_r_1011_ = lean_box(v_res_1010_);
return v_r_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1031_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1032_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1033_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1034_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_1031_, v___x_1032_, v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
return v_res_1036_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1037_; double v___x_1038_; 
v___x_1037_ = lean_unsigned_to_nat(1000000000u);
v___x_1038_ = lean_float_of_nat(v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object* v_toApplicative_1039_, lean_object* v_start_1040_, lean_object* v_a_1041_, lean_object* v_stop_1042_){
_start:
{
lean_object* v_toPure_1043_; double v___x_1044_; double v___x_1045_; double v___x_1046_; double v___x_1047_; double v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_toPure_1043_ = lean_ctor_get(v_toApplicative_1039_, 1);
lean_inc(v_toPure_1043_);
lean_dec_ref(v_toApplicative_1039_);
v___x_1044_ = lean_float_of_nat(v_start_1040_);
v___x_1045_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1046_ = lean_float_div(v___x_1044_, v___x_1045_);
v___x_1047_ = lean_float_of_nat(v_stop_1042_);
v___x_1048_ = lean_float_div(v___x_1047_, v___x_1045_);
v___x_1049_ = lean_box_float(v___x_1046_);
v___x_1050_ = lean_box_float(v___x_1048_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_a_1041_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_apply_2(v_toPure_1043_, lean_box(0), v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object* v_toApplicative_1054_, lean_object* v_start_1055_, lean_object* v_toBind_1056_, lean_object* v___x_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v___f_1059_; lean_object* v___x_1060_; 
v___f_1059_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1059_, 0, v_toApplicative_1054_);
lean_closure_set(v___f_1059_, 1, v_start_1055_);
lean_closure_set(v___f_1059_, 2, v_a_1058_);
v___x_1060_ = lean_apply_4(v_toBind_1056_, lean_box(0), lean_box(0), v___x_1057_, v___f_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object* v_toApplicative_1061_, lean_object* v_toBind_1062_, lean_object* v___x_1063_, lean_object* v_act_1064_, lean_object* v_start_1065_){
_start:
{
lean_object* v___f_1066_; lean_object* v___x_1067_; 
lean_inc(v_toBind_1062_);
v___f_1066_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1066_, 0, v_toApplicative_1061_);
lean_closure_set(v___f_1066_, 1, v_start_1065_);
lean_closure_set(v___f_1066_, 2, v_toBind_1062_);
lean_closure_set(v___f_1066_, 3, v___x_1063_);
v___x_1067_ = lean_apply_4(v_toBind_1062_, lean_box(0), lean_box(0), v_act_1064_, v___f_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object* v_toApplicative_1068_, lean_object* v_start_1069_, lean_object* v_a_1070_, lean_object* v_stop_1071_){
_start:
{
lean_object* v_toPure_1072_; double v___x_1073_; double v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_toPure_1072_ = lean_ctor_get(v_toApplicative_1068_, 1);
lean_inc(v_toPure_1072_);
lean_dec_ref(v_toApplicative_1068_);
v___x_1073_ = lean_float_of_nat(v_start_1069_);
v___x_1074_ = lean_float_of_nat(v_stop_1071_);
v___x_1075_ = lean_box_float(v___x_1073_);
v___x_1076_ = lean_box_float(v___x_1074_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_a_1070_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_apply_2(v_toPure_1072_, lean_box(0), v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object* v_toApplicative_1080_, lean_object* v_start_1081_, lean_object* v_toBind_1082_, lean_object* v___x_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v___f_1085_; lean_object* v___x_1086_; 
v___f_1085_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1085_, 0, v_toApplicative_1080_);
lean_closure_set(v___f_1085_, 1, v_start_1081_);
lean_closure_set(v___f_1085_, 2, v_a_1084_);
v___x_1086_ = lean_apply_4(v_toBind_1082_, lean_box(0), lean_box(0), v___x_1083_, v___f_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object* v_toApplicative_1087_, lean_object* v_toBind_1088_, lean_object* v___x_1089_, lean_object* v_act_1090_, lean_object* v_start_1091_){
_start:
{
lean_object* v___f_1092_; lean_object* v___x_1093_; 
lean_inc(v_toBind_1088_);
v___f_1092_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1092_, 0, v_toApplicative_1087_);
lean_closure_set(v___f_1092_, 1, v_start_1091_);
lean_closure_set(v___f_1092_, 2, v_toBind_1088_);
lean_closure_set(v___f_1092_, 3, v___x_1089_);
v___x_1093_ = lean_apply_4(v_toBind_1088_, lean_box(0), lean_box(0), v_act_1090_, v___f_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_opts_1098_, lean_object* v_act_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1100_ = l_Lean_KVMap_instValueBool;
v___x_1101_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1102_ = l_Lean_Option_get___redArg(v___x_1100_, v_opts_1098_, v___x_1101_);
v___x_1103_ = lean_unbox(v___x_1102_);
lean_dec(v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v_toApplicative_1104_; lean_object* v_toBind_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; 
v_toApplicative_1104_ = lean_ctor_get(v_inst_1096_, 0);
lean_inc_ref(v_toApplicative_1104_);
v_toBind_1105_ = lean_ctor_get(v_inst_1096_, 1);
lean_inc_n(v_toBind_1105_, 2);
lean_dec_ref(v_inst_1096_);
v___x_1106_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1107_ = lean_apply_2(v_inst_1097_, lean_box(0), v___x_1106_);
lean_inc(v___x_1107_);
v___f_1108_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1108_, 0, v_toApplicative_1104_);
lean_closure_set(v___f_1108_, 1, v_toBind_1105_);
lean_closure_set(v___f_1108_, 2, v___x_1107_);
lean_closure_set(v___f_1108_, 3, v_act_1099_);
v___x_1109_ = lean_apply_4(v_toBind_1105_, lean_box(0), lean_box(0), v___x_1107_, v___f_1108_);
return v___x_1109_;
}
else
{
lean_object* v_toApplicative_1110_; lean_object* v_toBind_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___f_1114_; lean_object* v___x_1115_; 
v_toApplicative_1110_ = lean_ctor_get(v_inst_1096_, 0);
lean_inc_ref(v_toApplicative_1110_);
v_toBind_1111_ = lean_ctor_get(v_inst_1096_, 1);
lean_inc_n(v_toBind_1111_, 2);
lean_dec_ref(v_inst_1096_);
v___x_1112_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1113_ = lean_apply_2(v_inst_1097_, lean_box(0), v___x_1112_);
lean_inc(v___x_1113_);
v___f_1114_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1114_, 0, v_toApplicative_1110_);
lean_closure_set(v___f_1114_, 1, v_toBind_1111_);
lean_closure_set(v___f_1114_, 2, v___x_1113_);
lean_closure_set(v___f_1114_, 3, v_act_1099_);
v___x_1115_ = lean_apply_4(v_toBind_1111_, lean_box(0), lean_box(0), v___x_1113_, v___f_1114_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_opts_1118_, lean_object* v_act_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(v_inst_1116_, v_inst_1117_, v_opts_1118_, v_act_1119_);
lean_dec_ref(v_opts_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object* v_00_u03b1_1121_, lean_object* v_m_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_opts_1125_, lean_object* v_act_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1127_ = l_Lean_KVMap_instValueBool;
v___x_1128_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1129_ = l_Lean_Option_get___redArg(v___x_1127_, v_opts_1125_, v___x_1128_);
v___x_1130_ = lean_unbox(v___x_1129_);
lean_dec(v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v_toApplicative_1131_; lean_object* v_toBind_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; 
v_toApplicative_1131_ = lean_ctor_get(v_inst_1123_, 0);
lean_inc_ref(v_toApplicative_1131_);
v_toBind_1132_ = lean_ctor_get(v_inst_1123_, 1);
lean_inc_n(v_toBind_1132_, 2);
lean_dec_ref(v_inst_1123_);
v___x_1133_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1134_ = lean_apply_2(v_inst_1124_, lean_box(0), v___x_1133_);
lean_inc(v___x_1134_);
v___f_1135_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1135_, 0, v_toApplicative_1131_);
lean_closure_set(v___f_1135_, 1, v_toBind_1132_);
lean_closure_set(v___f_1135_, 2, v___x_1134_);
lean_closure_set(v___f_1135_, 3, v_act_1126_);
v___x_1136_ = lean_apply_4(v_toBind_1132_, lean_box(0), lean_box(0), v___x_1134_, v___f_1135_);
return v___x_1136_;
}
else
{
lean_object* v_toApplicative_1137_; lean_object* v_toBind_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___f_1141_; lean_object* v___x_1142_; 
v_toApplicative_1137_ = lean_ctor_get(v_inst_1123_, 0);
lean_inc_ref(v_toApplicative_1137_);
v_toBind_1138_ = lean_ctor_get(v_inst_1123_, 1);
lean_inc_n(v_toBind_1138_, 2);
lean_dec_ref(v_inst_1123_);
v___x_1139_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1140_ = lean_apply_2(v_inst_1124_, lean_box(0), v___x_1139_);
lean_inc(v___x_1140_);
v___f_1141_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1141_, 0, v_toApplicative_1137_);
lean_closure_set(v___f_1141_, 1, v_toBind_1138_);
lean_closure_set(v___f_1141_, 2, v___x_1140_);
lean_closure_set(v___f_1141_, 3, v_act_1126_);
v___x_1142_ = lean_apply_4(v_toBind_1138_, lean_box(0), lean_box(0), v___x_1140_, v___f_1141_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_m_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_opts_1147_, lean_object* v_act_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(v_00_u03b1_1143_, v_m_1144_, v_inst_1145_, v_inst_1146_, v_opts_1147_, v_act_1148_);
lean_dec_ref(v_opts_1147_);
return v_res_1149_;
}
}
static double _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0(void){
_start:
{
lean_object* v___x_1150_; double v___x_1151_; 
v___x_1150_ = lean_unsigned_to_nat(1000u);
v___x_1151_ = lean_float_of_nat(v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object* v_o_1152_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1153_ = l_Lean_KVMap_instValueBool;
v___x_1154_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1155_ = l_Lean_Option_get___redArg(v___x_1153_, v_o_1152_, v___x_1154_);
v___x_1156_ = lean_unbox(v___x_1155_);
lean_dec(v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; double v___x_1160_; double v___x_1161_; double v___x_1162_; 
v___x_1157_ = l_Lean_KVMap_instValueNat;
v___x_1158_ = l_Lean_trace_profiler_threshold;
v___x_1159_ = l_Lean_Option_get___redArg(v___x_1157_, v_o_1152_, v___x_1158_);
v___x_1160_ = lean_float_of_nat(v___x_1159_);
v___x_1161_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1162_ = lean_float_div(v___x_1160_, v___x_1161_);
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; double v___x_1166_; 
v___x_1163_ = l_Lean_KVMap_instValueNat;
v___x_1164_ = l_Lean_trace_profiler_threshold;
v___x_1165_ = l_Lean_Option_get___redArg(v___x_1163_, v_o_1152_, v___x_1164_);
v___x_1166_ = lean_float_of_nat(v___x_1165_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object* v_o_1167_){
_start:
{
double v_res_1168_; lean_object* v_r_1169_; 
v_res_1168_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1167_);
lean_dec_ref(v_o_1167_);
v_r_1169_ = lean_box_float(v_res_1168_);
return v_r_1169_;
}
}
static lean_object* _init_l_Lean_instMonadAlwaysExceptEIO___closed__0(void){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object* v_00_u03b5_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___closed__0, &l_Lean_instMonadAlwaysExceptEIO___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___closed__0);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object* v_inst_1173_, lean_object* v_always_1174_){
_start:
{
lean_object* v___f_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; 
lean_inc_ref(v_always_1174_);
v___f_1175_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1175_, 0, v_always_1174_);
lean_closure_set(v___f_1175_, 1, v_inst_1173_);
v___f_1176_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_1176_, 0, v_always_1174_);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___f_1175_);
lean_ctor_set(v___x_1177_, 1, v___f_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object* v_m_1178_, lean_object* v_inst_1179_, lean_object* v_00_u03b5_1180_, lean_object* v_00_u03c3_1181_, lean_object* v_always_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_1179_, v_always_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object* v_always_1184_){
_start:
{
lean_object* v___f_1185_; lean_object* v___f_1186_; lean_object* v___x_1187_; 
lean_inc_ref(v_always_1184_);
v___f_1185_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1185_, 0, v_always_1184_);
v___f_1186_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1186_, 0, v_always_1184_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___f_1185_);
lean_ctor_set(v___x_1187_, 1, v___f_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object* v_m_1188_, lean_object* v_00_u03b5_1189_, lean_object* v_00_u03c9_1190_, lean_object* v_00_u03c3_1191_, lean_object* v_always_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object* v_always_1194_){
_start:
{
lean_object* v___f_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; 
lean_inc_ref(v_always_1194_);
v___f_1195_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1195_, 0, v_always_1194_);
v___f_1196_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1196_, 0, v_always_1194_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___f_1195_);
lean_ctor_set(v___x_1197_, 1, v___f_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object* v_m_1198_, lean_object* v_00_u03b5_1199_, lean_object* v_00_u03c1_1200_, lean_object* v_always_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object* v_always_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1204_, v_inst_1205_, v_inst_1206_, v_always_1203_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object* v_00_u03b1_1208_, lean_object* v_m_1209_, lean_object* v_00_u03b5_1210_, lean_object* v_00_u03c9_1211_, lean_object* v_00_u03b2_1212_, lean_object* v_always_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1214_, v_inst_1215_, v_inst_1216_, v_always_1213_);
return v___x_1217_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___lam__0(lean_object* v_x_1224_){
_start:
{
if (lean_obj_tag(v_x_1224_) == 0)
{
uint8_t v___x_1225_; 
v___x_1225_ = 2;
return v___x_1225_;
}
else
{
lean_object* v_a_1226_; uint8_t v___x_1227_; 
v_a_1226_ = lean_ctor_get(v_x_1224_, 0);
v___x_1227_ = lean_unbox(v_a_1226_);
if (v___x_1227_ == 0)
{
uint8_t v___x_1228_; 
v___x_1228_ = 1;
return v___x_1228_;
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = 0;
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object* v_x_1230_){
_start:
{
uint8_t v_res_1231_; lean_object* v_r_1232_; 
v_res_1231_ = l_Lean_instExceptToTraceResultBool___lam__0(v_x_1230_);
lean_dec_ref(v_x_1230_);
v_r_1232_ = lean_box(v_res_1231_);
return v_r_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object* v_00_u03b5_1234_){
_start:
{
lean_object* v___f_1235_; 
v___f_1235_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___closed__0));
return v___f_1235_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___lam__0(lean_object* v_x_1236_){
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
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object* v_x_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Lean_instExceptToTraceResultOption___lam__0(v_x_1241_);
lean_dec_ref(v_x_1241_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object* v_00_u03b1_1245_, lean_object* v_00_u03b5_1246_){
_start:
{
lean_object* v___f_1247_; 
v___f_1247_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___closed__0));
return v___f_1247_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultExpr___lam__0(lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1248_) == 0)
{
uint8_t v___x_1249_; 
v___x_1249_ = 2;
return v___x_1249_;
}
else
{
lean_object* v_a_1250_; uint8_t v___x_1251_; 
v_a_1250_ = lean_ctor_get(v_x_1248_, 0);
v___x_1251_ = l_Lean_Expr_hasSyntheticSorry(v_a_1250_);
if (v___x_1251_ == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = 0;
return v___x_1252_;
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = 1;
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___lam__0___boxed(lean_object* v_x_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Lean_instExceptToTraceResultExpr___lam__0(v_x_1254_);
lean_dec_ref(v_x_1254_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr(lean_object* v_00_u03b5_1258_){
_start:
{
lean_object* v___f_1259_; 
v___f_1259_ = ((lean_object*)(l_Lean_instExceptToTraceResultExpr___closed__0));
return v___f_1259_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object* v_x_1260_){
_start:
{
if (lean_obj_tag(v_x_1260_) == 0)
{
uint8_t v___x_1261_; 
v___x_1261_ = 2;
return v___x_1261_;
}
else
{
uint8_t v___x_1262_; 
v___x_1262_ = 0;
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object* v_x_1263_){
_start:
{
uint8_t v_res_1264_; lean_object* v_r_1265_; 
v_res_1264_ = l_Lean_instExceptToTraceResult___lam__0(v_x_1263_);
lean_dec_ref(v_x_1263_);
v_r_1265_ = lean_box(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object* v_00_u03b1_1267_, lean_object* v_00_u03b5_1268_){
_start:
{
lean_object* v___f_1269_; 
v___f_1269_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
return v___f_1269_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___redArg(lean_object* v_inst_1270_, lean_object* v_e_1271_){
_start:
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = lean_apply_1(v_inst_1270_, v_e_1271_);
v___x_1273_ = lean_unbox(v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___redArg___boxed(lean_object* v_inst_1274_, lean_object* v_e_1275_){
_start:
{
uint8_t v_res_1276_; lean_object* v_r_1277_; 
v_res_1276_ = l_Except_toTraceResult___redArg(v_inst_1274_, v_e_1275_);
v_r_1277_ = lean_box(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult(lean_object* v_00_u03b1_1278_, lean_object* v_00_u03b5_1279_, lean_object* v_inst_1280_, lean_object* v_e_1281_){
_start:
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_apply_1(v_inst_1280_, v_e_1281_);
v___x_1283_ = lean_unbox(v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_00_u03b5_1285_, lean_object* v_inst_1286_, lean_object* v_e_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Except_toTraceResult(v_00_u03b1_1284_, v_00_u03b5_1285_, v_inst_1286_, v_e_1287_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0));
v___x_1292_ = l_Lean_stringToMessageData(v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object* v_inst_1293_, lean_object* v_x_1294_){
_start:
{
lean_object* v_toApplicative_1295_; lean_object* v_toPure_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_toApplicative_1295_ = lean_ctor_get(v_inst_1293_, 0);
lean_inc_ref(v_toApplicative_1295_);
lean_dec_ref(v_inst_1293_);
v_toPure_1296_ = lean_ctor_get(v_toApplicative_1295_, 1);
lean_inc(v_toPure_1296_);
lean_dec_ref(v_toApplicative_1295_);
v___x_1297_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1);
v___x_1298_ = lean_apply_2(v_toPure_1296_, lean_box(0), v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(lean_object* v_inst_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(v_inst_1299_, v_x_1300_);
lean_dec(v_x_1300_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object* v_oldTraces_1302_, lean_object* v_s_1303_){
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object* v_always_1314_, lean_object* v_inst_1315_, lean_object* v_fst_1316_, lean_object* v_____r_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1314_);
v___x_1319_ = l_MonadExcept_ofExcept___redArg(v_inst_1315_, v___x_1318_, v_fst_1316_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object* v_inst_1320_, lean_object* v___x_1321_, lean_object* v_fst_1322_, lean_object* v_____r_1323_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_MonadExcept_ofExcept___redArg(v_inst_1320_, v___x_1321_, v_fst_1322_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_oldTraces_1329_, lean_object* v_ref_1330_, lean_object* v_toBind_1331_, lean_object* v___f_1332_, lean_object* v_inst_1333_, lean_object* v_fst_1334_, lean_object* v_cls_1335_, uint8_t v_collapsed_1336_, lean_object* v_tag_1337_, uint8_t v___x_1338_, double v_fst_1339_, double v_snd_1340_, lean_object* v_m_1341_){
_start:
{
lean_object* v_data_1343_; lean_object* v_result_1346_; lean_object* v___x_1347_; double v___x_1348_; lean_object* v_data_1349_; 
v_result_1346_ = lean_apply_1(v_inst_1333_, v_fst_1334_);
v___x_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1347_, 0, v_result_1346_);
v___x_1348_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_1337_);
lean_inc_ref(v___x_1347_);
lean_inc(v_cls_1335_);
v_data_1349_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1349_, 0, v_cls_1335_);
lean_ctor_set(v_data_1349_, 1, v___x_1347_);
lean_ctor_set(v_data_1349_, 2, v_tag_1337_);
lean_ctor_set_float(v_data_1349_, sizeof(void*)*3, v___x_1348_);
lean_ctor_set_float(v_data_1349_, sizeof(void*)*3 + 8, v___x_1348_);
lean_ctor_set_uint8(v_data_1349_, sizeof(void*)*3 + 16, v_collapsed_1336_);
if (v___x_1338_ == 0)
{
lean_dec_ref_known(v___x_1347_, 1);
lean_dec_ref(v_tag_1337_);
lean_dec(v_cls_1335_);
v_data_1343_ = v_data_1349_;
goto v___jp_1342_;
}
else
{
lean_object* v_data_1350_; 
lean_dec_ref_known(v_data_1349_, 3);
v_data_1350_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1350_, 0, v_cls_1335_);
lean_ctor_set(v_data_1350_, 1, v___x_1347_);
lean_ctor_set(v_data_1350_, 2, v_tag_1337_);
lean_ctor_set_float(v_data_1350_, sizeof(void*)*3, v_fst_1339_);
lean_ctor_set_float(v_data_1350_, sizeof(void*)*3 + 8, v_snd_1340_);
lean_ctor_set_uint8(v_data_1350_, sizeof(void*)*3 + 16, v_collapsed_1336_);
v_data_1343_ = v_data_1350_;
goto v___jp_1342_;
}
v___jp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_1325_, v_inst_1326_, v_inst_1327_, v_inst_1328_, v_oldTraces_1329_, v_data_1343_, v_ref_1330_, v_m_1341_);
v___x_1345_ = lean_apply_4(v_toBind_1331_, lean_box(0), lean_box(0), v___x_1344_, v___f_1332_);
return v___x_1345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_1351_ = _args[0];
lean_object* v_inst_1352_ = _args[1];
lean_object* v_inst_1353_ = _args[2];
lean_object* v_inst_1354_ = _args[3];
lean_object* v_oldTraces_1355_ = _args[4];
lean_object* v_ref_1356_ = _args[5];
lean_object* v_toBind_1357_ = _args[6];
lean_object* v___f_1358_ = _args[7];
lean_object* v_inst_1359_ = _args[8];
lean_object* v_fst_1360_ = _args[9];
lean_object* v_cls_1361_ = _args[10];
lean_object* v_collapsed_1362_ = _args[11];
lean_object* v_tag_1363_ = _args[12];
lean_object* v___x_1364_ = _args[13];
lean_object* v_fst_1365_ = _args[14];
lean_object* v_snd_1366_ = _args[15];
lean_object* v_m_1367_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1368_; uint8_t v___x_608__boxed_1369_; double v_fst_609__boxed_1370_; double v_snd_610__boxed_1371_; lean_object* v_res_1372_; 
v_collapsed_boxed_1368_ = lean_unbox(v_collapsed_1362_);
v___x_608__boxed_1369_ = lean_unbox(v___x_1364_);
v_fst_609__boxed_1370_ = lean_unbox_float(v_fst_1365_);
lean_dec_ref(v_fst_1365_);
v_snd_610__boxed_1371_ = lean_unbox_float(v_snd_1366_);
lean_dec_ref(v_snd_1366_);
v_res_1372_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1351_, v_inst_1352_, v_inst_1353_, v_inst_1354_, v_oldTraces_1355_, v_ref_1356_, v_toBind_1357_, v___f_1358_, v_inst_1359_, v_fst_1360_, v_cls_1361_, v_collapsed_boxed_1368_, v_tag_1363_, v___x_608__boxed_1369_, v_fst_609__boxed_1370_, v_snd_610__boxed_1371_, v_m_1367_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(lean_object* v_always_1373_, lean_object* v_inst_1374_, lean_object* v_fst_1375_, lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_oldTraces_1379_, lean_object* v_toBind_1380_, lean_object* v_inst_1381_, lean_object* v_cls_1382_, uint8_t v_collapsed_1383_, lean_object* v_tag_1384_, uint8_t v___x_1385_, double v_fst_1386_, double v_snd_1387_, lean_object* v_msg_1388_, lean_object* v___f_1389_, lean_object* v_ref_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v_tryCatch_1392_; lean_object* v___f_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___f_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_inc_ref(v_always_1373_);
v___x_1391_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1373_);
v_tryCatch_1392_ = lean_ctor_get(v_always_1373_, 1);
lean_inc(v_tryCatch_1392_);
lean_dec_ref(v_always_1373_);
lean_inc_ref_n(v_fst_1375_, 2);
lean_inc_ref(v_inst_1374_);
v___f_1393_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1393_, 0, v_inst_1374_);
lean_closure_set(v___f_1393_, 1, v___x_1391_);
lean_closure_set(v___f_1393_, 2, v_fst_1375_);
v___x_1394_ = lean_box(v_collapsed_1383_);
v___x_1395_ = lean_box(v___x_1385_);
v___x_1396_ = lean_box_float(v_fst_1386_);
v___x_1397_ = lean_box_float(v_snd_1387_);
lean_inc(v_toBind_1380_);
v___f_1398_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1398_, 0, v_inst_1374_);
lean_closure_set(v___f_1398_, 1, v_inst_1376_);
lean_closure_set(v___f_1398_, 2, v_inst_1377_);
lean_closure_set(v___f_1398_, 3, v_inst_1378_);
lean_closure_set(v___f_1398_, 4, v_oldTraces_1379_);
lean_closure_set(v___f_1398_, 5, v_ref_1390_);
lean_closure_set(v___f_1398_, 6, v_toBind_1380_);
lean_closure_set(v___f_1398_, 7, v___f_1393_);
lean_closure_set(v___f_1398_, 8, v_inst_1381_);
lean_closure_set(v___f_1398_, 9, v_fst_1375_);
lean_closure_set(v___f_1398_, 10, v_cls_1382_);
lean_closure_set(v___f_1398_, 11, v___x_1394_);
lean_closure_set(v___f_1398_, 12, v_tag_1384_);
lean_closure_set(v___f_1398_, 13, v___x_1395_);
lean_closure_set(v___f_1398_, 14, v___x_1396_);
lean_closure_set(v___f_1398_, 15, v___x_1397_);
v___x_1399_ = lean_apply_1(v_msg_1388_, v_fst_1375_);
v___x_1400_ = lean_apply_3(v_tryCatch_1392_, lean_box(0), v___x_1399_, v___f_1389_);
v___x_1401_ = lean_apply_4(v_toBind_1380_, lean_box(0), lean_box(0), v___x_1400_, v___f_1398_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_always_1402_ = _args[0];
lean_object* v_inst_1403_ = _args[1];
lean_object* v_fst_1404_ = _args[2];
lean_object* v_inst_1405_ = _args[3];
lean_object* v_inst_1406_ = _args[4];
lean_object* v_inst_1407_ = _args[5];
lean_object* v_oldTraces_1408_ = _args[6];
lean_object* v_toBind_1409_ = _args[7];
lean_object* v_inst_1410_ = _args[8];
lean_object* v_cls_1411_ = _args[9];
lean_object* v_collapsed_1412_ = _args[10];
lean_object* v_tag_1413_ = _args[11];
lean_object* v___x_1414_ = _args[12];
lean_object* v_fst_1415_ = _args[13];
lean_object* v_snd_1416_ = _args[14];
lean_object* v_msg_1417_ = _args[15];
lean_object* v___f_1418_ = _args[16];
lean_object* v_ref_1419_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_1420_; uint8_t v___x_648__boxed_1421_; double v_fst_649__boxed_1422_; double v_snd_650__boxed_1423_; lean_object* v_res_1424_; 
v_collapsed_boxed_1420_ = lean_unbox(v_collapsed_1412_);
v___x_648__boxed_1421_ = lean_unbox(v___x_1414_);
v_fst_649__boxed_1422_ = lean_unbox_float(v_fst_1415_);
lean_dec_ref(v_fst_1415_);
v_snd_650__boxed_1423_ = lean_unbox_float(v_snd_1416_);
lean_dec_ref(v_snd_1416_);
v_res_1424_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(v_always_1402_, v_inst_1403_, v_fst_1404_, v_inst_1405_, v_inst_1406_, v_inst_1407_, v_oldTraces_1408_, v_toBind_1409_, v_inst_1410_, v_cls_1411_, v_collapsed_boxed_1420_, v_tag_1413_, v___x_648__boxed_1421_, v_fst_649__boxed_1422_, v_snd_650__boxed_1423_, v_msg_1417_, v___f_1418_, v_ref_1419_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v_always_1429_, lean_object* v_inst_1430_, lean_object* v_cls_1431_, uint8_t v_collapsed_1432_, lean_object* v_tag_1433_, lean_object* v_opts_1434_, uint8_t v_clsEnabled_1435_, lean_object* v_oldTraces_1436_, lean_object* v_msg_1437_, lean_object* v_resStartStop_1438_){
_start:
{
lean_object* v___x_1439_; lean_object* v_snd_1440_; lean_object* v_fst_1441_; lean_object* v_fst_1442_; lean_object* v_snd_1443_; lean_object* v___f_1444_; lean_object* v___f_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___y_1456_; double v___y_1462_; uint8_t v___x_1467_; 
v___x_1439_ = l_Lean_KVMap_instValueBool;
v_snd_1440_ = lean_ctor_get(v_resStartStop_1438_, 1);
lean_inc(v_snd_1440_);
v_fst_1441_ = lean_ctor_get(v_resStartStop_1438_, 0);
lean_inc_n(v_fst_1441_, 2);
lean_dec_ref(v_resStartStop_1438_);
v_fst_1442_ = lean_ctor_get(v_snd_1440_, 0);
lean_inc(v_fst_1442_);
v_snd_1443_ = lean_ctor_get(v_snd_1440_, 1);
lean_inc(v_snd_1443_);
lean_dec(v_snd_1440_);
lean_inc_ref_n(v_inst_1425_, 2);
v___f_1444_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1444_, 0, v_inst_1425_);
lean_inc_ref(v_oldTraces_1436_);
v___f_1445_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1445_, 0, v_oldTraces_1436_);
lean_inc_ref(v_always_1429_);
v___f_1446_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1446_, 0, v_always_1429_);
lean_closure_set(v___f_1446_, 1, v_inst_1425_);
lean_closure_set(v___f_1446_, 2, v_fst_1441_);
v___x_1447_ = l_Lean_trace_profiler;
v___x_1448_ = l_Lean_Option_get___redArg(v___x_1439_, v_opts_1434_, v___x_1447_);
v___x_1467_ = lean_unbox(v___x_1448_);
if (v___x_1467_ == 0)
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_unbox(v___x_1448_);
v___y_1456_ = v___x_1468_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1470_ = l_Lean_Option_get___redArg(v___x_1439_, v_opts_1434_, v___x_1469_);
v___x_1471_ = lean_unbox(v___x_1470_);
lean_dec(v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; double v___x_1475_; double v___x_1476_; double v___x_1477_; 
v___x_1472_ = l_Lean_KVMap_instValueNat;
v___x_1473_ = l_Lean_trace_profiler_threshold;
v___x_1474_ = l_Lean_Option_get___redArg(v___x_1472_, v_opts_1434_, v___x_1473_);
v___x_1475_ = lean_float_of_nat(v___x_1474_);
v___x_1476_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1477_ = lean_float_div(v___x_1475_, v___x_1476_);
v___y_1462_ = v___x_1477_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; double v___x_1481_; 
v___x_1478_ = l_Lean_KVMap_instValueNat;
v___x_1479_ = l_Lean_trace_profiler_threshold;
v___x_1480_ = l_Lean_Option_get___redArg(v___x_1478_, v_opts_1434_, v___x_1479_);
v___x_1481_ = lean_float_of_nat(v___x_1480_);
v___y_1462_ = v___x_1481_;
goto v___jp_1461_;
}
}
v___jp_1449_:
{
lean_object* v_toBind_1450_; lean_object* v_getRef_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; lean_object* v___x_1454_; 
v_toBind_1450_ = lean_ctor_get(v_inst_1425_, 1);
lean_inc_n(v_toBind_1450_, 2);
v_getRef_1451_ = lean_ctor_get(v_inst_1427_, 0);
lean_inc(v_getRef_1451_);
v___x_1452_ = lean_box(v_collapsed_1432_);
v___f_1453_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed), 18, 17);
lean_closure_set(v___f_1453_, 0, v_always_1429_);
lean_closure_set(v___f_1453_, 1, v_inst_1425_);
lean_closure_set(v___f_1453_, 2, v_fst_1441_);
lean_closure_set(v___f_1453_, 3, v_inst_1426_);
lean_closure_set(v___f_1453_, 4, v_inst_1427_);
lean_closure_set(v___f_1453_, 5, v_inst_1428_);
lean_closure_set(v___f_1453_, 6, v_oldTraces_1436_);
lean_closure_set(v___f_1453_, 7, v_toBind_1450_);
lean_closure_set(v___f_1453_, 8, v_inst_1430_);
lean_closure_set(v___f_1453_, 9, v_cls_1431_);
lean_closure_set(v___f_1453_, 10, v___x_1452_);
lean_closure_set(v___f_1453_, 11, v_tag_1433_);
lean_closure_set(v___f_1453_, 12, v___x_1448_);
lean_closure_set(v___f_1453_, 13, v_fst_1442_);
lean_closure_set(v___f_1453_, 14, v_snd_1443_);
lean_closure_set(v___f_1453_, 15, v_msg_1437_);
lean_closure_set(v___f_1453_, 16, v___f_1444_);
v___x_1454_ = lean_apply_4(v_toBind_1450_, lean_box(0), lean_box(0), v_getRef_1451_, v___f_1453_);
return v___x_1454_;
}
v___jp_1455_:
{
if (v_clsEnabled_1435_ == 0)
{
if (v___y_1456_ == 0)
{
lean_object* v_toBind_1457_; lean_object* v_modifyTraceState_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec(v___x_1448_);
lean_dec_ref(v___f_1444_);
lean_dec(v_snd_1443_);
lean_dec(v_fst_1442_);
lean_dec(v_fst_1441_);
lean_dec(v_msg_1437_);
lean_dec_ref(v_oldTraces_1436_);
lean_dec_ref(v_tag_1433_);
lean_dec(v_cls_1431_);
lean_dec_ref(v_inst_1430_);
lean_dec_ref(v_always_1429_);
lean_dec(v_inst_1428_);
lean_dec_ref(v_inst_1427_);
v_toBind_1457_ = lean_ctor_get(v_inst_1425_, 1);
lean_inc(v_toBind_1457_);
lean_dec_ref(v_inst_1425_);
v_modifyTraceState_1458_ = lean_ctor_get(v_inst_1426_, 0);
lean_inc(v_modifyTraceState_1458_);
lean_dec_ref(v_inst_1426_);
v___x_1459_ = lean_apply_1(v_modifyTraceState_1458_, v___f_1445_);
v___x_1460_ = lean_apply_4(v_toBind_1457_, lean_box(0), lean_box(0), v___x_1459_, v___f_1446_);
return v___x_1460_;
}
else
{
lean_dec_ref(v___f_1446_);
lean_dec_ref(v___f_1445_);
goto v___jp_1449_;
}
}
else
{
lean_dec_ref(v___f_1446_);
lean_dec_ref(v___f_1445_);
goto v___jp_1449_;
}
}
v___jp_1461_:
{
double v___x_1463_; double v___x_1464_; double v___x_1465_; uint8_t v___x_1466_; 
v___x_1463_ = lean_unbox_float(v_snd_1443_);
v___x_1464_ = lean_unbox_float(v_fst_1442_);
v___x_1465_ = lean_float_sub(v___x_1463_, v___x_1464_);
v___x_1466_ = lean_float_decLt(v___y_1462_, v___x_1465_);
v___y_1456_ = v___x_1466_;
goto v___jp_1455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object* v_inst_1482_, lean_object* v_inst_1483_, lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_always_1486_, lean_object* v_inst_1487_, lean_object* v_cls_1488_, lean_object* v_collapsed_1489_, lean_object* v_tag_1490_, lean_object* v_opts_1491_, lean_object* v_clsEnabled_1492_, lean_object* v_oldTraces_1493_, lean_object* v_msg_1494_, lean_object* v_resStartStop_1495_){
_start:
{
uint8_t v_collapsed_boxed_1496_; uint8_t v_clsEnabled_boxed_1497_; lean_object* v_res_1498_; 
v_collapsed_boxed_1496_ = lean_unbox(v_collapsed_1489_);
v_clsEnabled_boxed_1497_ = lean_unbox(v_clsEnabled_1492_);
v_res_1498_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1482_, v_inst_1483_, v_inst_1484_, v_inst_1485_, v_always_1486_, v_inst_1487_, v_cls_1488_, v_collapsed_boxed_1496_, v_tag_1490_, v_opts_1491_, v_clsEnabled_boxed_1497_, v_oldTraces_1493_, v_msg_1494_, v_resStartStop_1495_);
lean_dec_ref(v_opts_1491_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object* v_00_u03b1_1499_, lean_object* v_m_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_00_u03b5_1505_, lean_object* v_always_1506_, lean_object* v_inst_1507_, lean_object* v_cls_1508_, uint8_t v_collapsed_1509_, lean_object* v_tag_1510_, lean_object* v_opts_1511_, uint8_t v_clsEnabled_1512_, lean_object* v_oldTraces_1513_, lean_object* v_msg_1514_, lean_object* v_resStartStop_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1501_, v_inst_1502_, v_inst_1503_, v_inst_1504_, v_always_1506_, v_inst_1507_, v_cls_1508_, v_collapsed_1509_, v_tag_1510_, v_opts_1511_, v_clsEnabled_1512_, v_oldTraces_1513_, v_msg_1514_, v_resStartStop_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_1517_ = _args[0];
lean_object* v_m_1518_ = _args[1];
lean_object* v_inst_1519_ = _args[2];
lean_object* v_inst_1520_ = _args[3];
lean_object* v_inst_1521_ = _args[4];
lean_object* v_inst_1522_ = _args[5];
lean_object* v_00_u03b5_1523_ = _args[6];
lean_object* v_always_1524_ = _args[7];
lean_object* v_inst_1525_ = _args[8];
lean_object* v_cls_1526_ = _args[9];
lean_object* v_collapsed_1527_ = _args[10];
lean_object* v_tag_1528_ = _args[11];
lean_object* v_opts_1529_ = _args[12];
lean_object* v_clsEnabled_1530_ = _args[13];
lean_object* v_oldTraces_1531_ = _args[14];
lean_object* v_msg_1532_ = _args[15];
lean_object* v_resStartStop_1533_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1534_; uint8_t v_clsEnabled_boxed_1535_; lean_object* v_res_1536_; 
v_collapsed_boxed_1534_ = lean_unbox(v_collapsed_1527_);
v_clsEnabled_boxed_1535_ = lean_unbox(v_clsEnabled_1530_);
v_res_1536_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(v_00_u03b1_1517_, v_m_1518_, v_inst_1519_, v_inst_1520_, v_inst_1521_, v_inst_1522_, v_00_u03b5_1523_, v_always_1524_, v_inst_1525_, v_cls_1526_, v_collapsed_boxed_1534_, v_tag_1528_, v_opts_1529_, v_clsEnabled_boxed_1535_, v_oldTraces_1531_, v_msg_1532_, v_resStartStop_1533_);
lean_dec_ref(v_opts_1529_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_always_1541_, lean_object* v_inst_1542_, lean_object* v_cls_1543_, uint8_t v_collapsed_1544_, lean_object* v_tag_1545_, lean_object* v_opts_1546_, uint8_t v_clsEnabled_1547_, lean_object* v_oldTraces_1548_, lean_object* v_msg_1549_, lean_object* v_resStartStop_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1537_, v_inst_1538_, v_inst_1539_, v_inst_1540_, v_always_1541_, v_inst_1542_, v_cls_1543_, v_collapsed_1544_, v_tag_1545_, v_opts_1546_, v_clsEnabled_1547_, v_oldTraces_1548_, v_msg_1549_, v_resStartStop_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_always_1556_, lean_object* v_inst_1557_, lean_object* v_cls_1558_, lean_object* v_collapsed_1559_, lean_object* v_tag_1560_, lean_object* v_opts_1561_, lean_object* v_clsEnabled_1562_, lean_object* v_oldTraces_1563_, lean_object* v_msg_1564_, lean_object* v_resStartStop_1565_){
_start:
{
uint8_t v_collapsed_boxed_1566_; uint8_t v_clsEnabled_boxed_1567_; lean_object* v_res_1568_; 
v_collapsed_boxed_1566_ = lean_unbox(v_collapsed_1559_);
v_clsEnabled_boxed_1567_ = lean_unbox(v_clsEnabled_1562_);
v_res_1568_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1552_, v_inst_1553_, v_inst_1554_, v_inst_1555_, v_always_1556_, v_inst_1557_, v_cls_1558_, v_collapsed_boxed_1566_, v_tag_1560_, v_opts_1561_, v_clsEnabled_boxed_1567_, v_oldTraces_1563_, v_msg_1564_, v_resStartStop_1565_);
lean_dec_ref(v_opts_1561_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object* v_toPure_1569_, lean_object* v_ex_1570_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_ex_1570_);
v___x_1572_ = lean_apply_2(v_toPure_1569_, lean_box(0), v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object* v_toPure_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_a_1574_);
v___x_1576_ = lean_apply_2(v_toPure_1573_, lean_box(0), v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object* v_start_1577_, lean_object* v_a_1578_, lean_object* v_toPure_1579_, lean_object* v_stop_1580_){
_start:
{
double v___x_1581_; double v___x_1582_; double v___x_1583_; double v___x_1584_; double v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1581_ = lean_float_of_nat(v_start_1577_);
v___x_1582_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1583_ = lean_float_div(v___x_1581_, v___x_1582_);
v___x_1584_ = lean_float_of_nat(v_stop_1580_);
v___x_1585_ = lean_float_div(v___x_1584_, v___x_1582_);
v___x_1586_ = lean_box_float(v___x_1583_);
v___x_1587_ = lean_box_float(v___x_1585_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_a_1578_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_apply_2(v_toPure_1579_, lean_box(0), v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object* v_start_1591_, lean_object* v_toPure_1592_, lean_object* v_toBind_1593_, lean_object* v___x_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___f_1596_; lean_object* v___x_1597_; 
v___f_1596_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1596_, 0, v_start_1591_);
lean_closure_set(v___f_1596_, 1, v_a_1595_);
lean_closure_set(v___f_1596_, 2, v_toPure_1592_);
v___x_1597_ = lean_apply_4(v_toBind_1593_, lean_box(0), lean_box(0), v___x_1594_, v___f_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object* v_toPure_1598_, lean_object* v_toBind_1599_, lean_object* v___x_1600_, lean_object* v___x_1601_, lean_object* v_start_1602_){
_start:
{
lean_object* v___f_1603_; lean_object* v___x_1604_; 
lean_inc(v_toBind_1599_);
v___f_1603_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1603_, 0, v_start_1602_);
lean_closure_set(v___f_1603_, 1, v_toPure_1598_);
lean_closure_set(v___f_1603_, 2, v_toBind_1599_);
lean_closure_set(v___f_1603_, 3, v___x_1600_);
v___x_1604_ = lean_apply_4(v_toBind_1599_, lean_box(0), lean_box(0), v___x_1601_, v___f_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object* v_start_1605_, lean_object* v_a_1606_, lean_object* v_toPure_1607_, lean_object* v_stop_1608_){
_start:
{
double v___x_1609_; double v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1609_ = lean_float_of_nat(v_start_1605_);
v___x_1610_ = lean_float_of_nat(v_stop_1608_);
v___x_1611_ = lean_box_float(v___x_1609_);
v___x_1612_ = lean_box_float(v___x_1610_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v_a_1606_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_apply_2(v_toPure_1607_, lean_box(0), v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object* v_start_1616_, lean_object* v_toPure_1617_, lean_object* v_toBind_1618_, lean_object* v___x_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v___f_1621_; lean_object* v___x_1622_; 
v___f_1621_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__6), 4, 3);
lean_closure_set(v___f_1621_, 0, v_start_1616_);
lean_closure_set(v___f_1621_, 1, v_a_1620_);
lean_closure_set(v___f_1621_, 2, v_toPure_1617_);
v___x_1622_ = lean_apply_4(v_toBind_1618_, lean_box(0), lean_box(0), v___x_1619_, v___f_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object* v_toPure_1623_, lean_object* v_toBind_1624_, lean_object* v___x_1625_, lean_object* v___x_1626_, lean_object* v_start_1627_){
_start:
{
lean_object* v___f_1628_; lean_object* v___x_1629_; 
lean_inc(v_toBind_1624_);
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1628_, 0, v_start_1627_);
lean_closure_set(v___f_1628_, 1, v_toPure_1623_);
lean_closure_set(v___f_1628_, 2, v_toBind_1624_);
lean_closure_set(v___f_1628_, 3, v___x_1625_);
v___x_1629_ = lean_apply_4(v_toBind_1624_, lean_box(0), lean_box(0), v___x_1626_, v___f_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object* v_always_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_cls_1636_, uint8_t v_collapsed_1637_, lean_object* v_tag_1638_, lean_object* v_opts_1639_, uint8_t v_clsEnabled_1640_, lean_object* v_msg_1641_, lean_object* v_toPure_1642_, lean_object* v_toBind_1643_, lean_object* v_k_1644_, lean_object* v_inst_1645_, lean_object* v_oldTraces_1646_){
_start:
{
lean_object* v_tryCatch_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___f_1650_; lean_object* v___f_1651_; lean_object* v___f_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v_tryCatch_1647_ = lean_ctor_get(v_always_1630_, 1);
lean_inc(v_tryCatch_1647_);
v___x_1648_ = lean_box(v_collapsed_1637_);
v___x_1649_ = lean_box(v_clsEnabled_1640_);
lean_inc_ref(v_opts_1639_);
v___f_1650_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1650_, 0, v_inst_1631_);
lean_closure_set(v___f_1650_, 1, v_inst_1632_);
lean_closure_set(v___f_1650_, 2, v_inst_1633_);
lean_closure_set(v___f_1650_, 3, v_inst_1634_);
lean_closure_set(v___f_1650_, 4, v_always_1630_);
lean_closure_set(v___f_1650_, 5, v_inst_1635_);
lean_closure_set(v___f_1650_, 6, v_cls_1636_);
lean_closure_set(v___f_1650_, 7, v___x_1648_);
lean_closure_set(v___f_1650_, 8, v_tag_1638_);
lean_closure_set(v___f_1650_, 9, v_opts_1639_);
lean_closure_set(v___f_1650_, 10, v___x_1649_);
lean_closure_set(v___f_1650_, 11, v_oldTraces_1646_);
lean_closure_set(v___f_1650_, 12, v_msg_1641_);
lean_inc_n(v_toPure_1642_, 2);
v___f_1651_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1651_, 0, v_toPure_1642_);
v___f_1652_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1652_, 0, v_toPure_1642_);
lean_inc(v_toBind_1643_);
v___x_1653_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v_k_1644_, v___f_1652_);
v___x_1654_ = lean_apply_3(v_tryCatch_1647_, lean_box(0), v___x_1653_, v___f_1651_);
v___x_1655_ = l_Lean_KVMap_instValueBool;
v___x_1656_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1657_ = l_Lean_Option_get___redArg(v___x_1655_, v_opts_1639_, v___x_1656_);
lean_dec_ref(v_opts_1639_);
v___x_1658_ = lean_unbox(v___x_1657_);
lean_dec(v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___f_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1659_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1660_ = lean_apply_2(v_inst_1645_, lean_box(0), v___x_1659_);
lean_inc(v___x_1660_);
lean_inc_n(v_toBind_1643_, 2);
v___f_1661_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1661_, 0, v_toPure_1642_);
lean_closure_set(v___f_1661_, 1, v_toBind_1643_);
lean_closure_set(v___f_1661_, 2, v___x_1660_);
lean_closure_set(v___f_1661_, 3, v___x_1654_);
v___x_1662_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v___x_1660_, v___f_1661_);
v___x_1663_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v___x_1662_, v___f_1650_);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___f_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1664_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1665_ = lean_apply_2(v_inst_1645_, lean_box(0), v___x_1664_);
lean_inc(v___x_1665_);
lean_inc_n(v_toBind_1643_, 2);
v___f_1666_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_1666_, 0, v_toPure_1642_);
lean_closure_set(v___f_1666_, 1, v_toBind_1643_);
lean_closure_set(v___f_1666_, 2, v___x_1665_);
lean_closure_set(v___f_1666_, 3, v___x_1654_);
v___x_1667_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v___x_1665_, v___f_1666_);
v___x_1668_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v___x_1667_, v___f_1650_);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_always_1669_ = _args[0];
lean_object* v_inst_1670_ = _args[1];
lean_object* v_inst_1671_ = _args[2];
lean_object* v_inst_1672_ = _args[3];
lean_object* v_inst_1673_ = _args[4];
lean_object* v_inst_1674_ = _args[5];
lean_object* v_cls_1675_ = _args[6];
lean_object* v_collapsed_1676_ = _args[7];
lean_object* v_tag_1677_ = _args[8];
lean_object* v_opts_1678_ = _args[9];
lean_object* v_clsEnabled_1679_ = _args[10];
lean_object* v_msg_1680_ = _args[11];
lean_object* v_toPure_1681_ = _args[12];
lean_object* v_toBind_1682_ = _args[13];
lean_object* v_k_1683_ = _args[14];
lean_object* v_inst_1684_ = _args[15];
lean_object* v_oldTraces_1685_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1686_; uint8_t v_clsEnabled_boxed_1687_; lean_object* v_res_1688_; 
v_collapsed_boxed_1686_ = lean_unbox(v_collapsed_1676_);
v_clsEnabled_boxed_1687_ = lean_unbox(v_clsEnabled_1679_);
v_res_1688_ = l_Lean_withTraceNode___redArg___lam__9(v_always_1669_, v_inst_1670_, v_inst_1671_, v_inst_1672_, v_inst_1673_, v_inst_1674_, v_cls_1675_, v_collapsed_boxed_1686_, v_tag_1677_, v_opts_1678_, v_clsEnabled_boxed_1687_, v_msg_1680_, v_toPure_1681_, v_toBind_1682_, v_k_1683_, v_inst_1684_, v_oldTraces_1685_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object* v_always_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_cls_1695_, uint8_t v_collapsed_1696_, lean_object* v_tag_1697_, lean_object* v_opts_1698_, lean_object* v_msg_1699_, lean_object* v_toPure_1700_, lean_object* v_toBind_1701_, lean_object* v_k_1702_, lean_object* v_inst_1703_, uint8_t v_clsEnabled_1704_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___f_1707_; 
v___x_1705_ = lean_box(v_collapsed_1696_);
v___x_1706_ = lean_box(v_clsEnabled_1704_);
lean_inc(v_k_1702_);
lean_inc(v_toBind_1701_);
lean_inc_ref(v_opts_1698_);
lean_inc_ref(v_inst_1691_);
lean_inc_ref(v_inst_1690_);
v___f_1707_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_1707_, 0, v_always_1689_);
lean_closure_set(v___f_1707_, 1, v_inst_1690_);
lean_closure_set(v___f_1707_, 2, v_inst_1691_);
lean_closure_set(v___f_1707_, 3, v_inst_1692_);
lean_closure_set(v___f_1707_, 4, v_inst_1693_);
lean_closure_set(v___f_1707_, 5, v_inst_1694_);
lean_closure_set(v___f_1707_, 6, v_cls_1695_);
lean_closure_set(v___f_1707_, 7, v___x_1705_);
lean_closure_set(v___f_1707_, 8, v_tag_1697_);
lean_closure_set(v___f_1707_, 9, v_opts_1698_);
lean_closure_set(v___f_1707_, 10, v___x_1706_);
lean_closure_set(v___f_1707_, 11, v_msg_1699_);
lean_closure_set(v___f_1707_, 12, v_toPure_1700_);
lean_closure_set(v___f_1707_, 13, v_toBind_1701_);
lean_closure_set(v___f_1707_, 14, v_k_1702_);
lean_closure_set(v___f_1707_, 15, v_inst_1703_);
if (v_clsEnabled_1704_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1711_ = l_Lean_KVMap_instValueBool;
v___x_1712_ = l_Lean_trace_profiler;
v___x_1713_ = l_Lean_Option_get___redArg(v___x_1711_, v_opts_1698_, v___x_1712_);
lean_dec_ref(v_opts_1698_);
v___x_1714_ = lean_unbox(v___x_1713_);
lean_dec(v___x_1713_);
if (v___x_1714_ == 0)
{
lean_dec_ref(v___f_1707_);
lean_dec(v_toBind_1701_);
lean_dec_ref(v_inst_1691_);
lean_dec_ref(v_inst_1690_);
return v_k_1702_;
}
else
{
lean_dec(v_k_1702_);
goto v___jp_1708_;
}
}
else
{
lean_dec(v_k_1702_);
lean_dec_ref(v_opts_1698_);
goto v___jp_1708_;
}
v___jp_1708_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1690_, v_inst_1691_);
v___x_1710_ = lean_apply_4(v_toBind_1701_, lean_box(0), lean_box(0), v___x_1709_, v___f_1707_);
return v___x_1710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object* v_always_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_cls_1721_, lean_object* v_collapsed_1722_, lean_object* v_tag_1723_, lean_object* v_opts_1724_, lean_object* v_msg_1725_, lean_object* v_toPure_1726_, lean_object* v_toBind_1727_, lean_object* v_k_1728_, lean_object* v_inst_1729_, lean_object* v_clsEnabled_1730_){
_start:
{
uint8_t v_collapsed_boxed_1731_; uint8_t v_clsEnabled_boxed_1732_; lean_object* v_res_1733_; 
v_collapsed_boxed_1731_ = lean_unbox(v_collapsed_1722_);
v_clsEnabled_boxed_1732_ = lean_unbox(v_clsEnabled_1730_);
v_res_1733_ = l_Lean_withTraceNode___redArg___lam__10(v_always_1715_, v_inst_1716_, v_inst_1717_, v_inst_1718_, v_inst_1719_, v_inst_1720_, v_cls_1721_, v_collapsed_boxed_1731_, v_tag_1723_, v_opts_1724_, v_msg_1725_, v_toPure_1726_, v_toBind_1727_, v_k_1728_, v_inst_1729_, v_clsEnabled_boxed_1732_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object* v_inst_1734_, lean_object* v_toApplicative_1735_, lean_object* v_always_1736_, lean_object* v_inst_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_cls_1741_, uint8_t v_collapsed_1742_, lean_object* v_tag_1743_, lean_object* v_msg_1744_, lean_object* v_toBind_1745_, lean_object* v_k_1746_, lean_object* v_inst_1747_, lean_object* v_inst_1748_, lean_object* v_opts_1749_){
_start:
{
uint8_t v_hasTrace_1750_; uint8_t v___x_1751_; 
v_hasTrace_1750_ = lean_ctor_get_uint8(v_opts_1749_, sizeof(void*)*1);
v___x_1751_ = lean_bool_not(v_hasTrace_1750_);
if (v___x_1751_ == 0)
{
lean_object* v_getInheritedTraceOptions_1752_; lean_object* v_toPure_1753_; lean_object* v___x_1754_; lean_object* v___f_1755_; lean_object* v___f_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_getInheritedTraceOptions_1752_ = lean_ctor_get(v_inst_1734_, 2);
lean_inc(v_getInheritedTraceOptions_1752_);
v_toPure_1753_ = lean_ctor_get(v_toApplicative_1735_, 1);
lean_inc_n(v_toPure_1753_, 2);
lean_dec_ref(v_toApplicative_1735_);
v___x_1754_ = lean_box(v_collapsed_1742_);
lean_inc_n(v_toBind_1745_, 3);
lean_inc(v_cls_1741_);
v___f_1755_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_1755_, 0, v_always_1736_);
lean_closure_set(v___f_1755_, 1, v_inst_1737_);
lean_closure_set(v___f_1755_, 2, v_inst_1734_);
lean_closure_set(v___f_1755_, 3, v_inst_1738_);
lean_closure_set(v___f_1755_, 4, v_inst_1739_);
lean_closure_set(v___f_1755_, 5, v_inst_1740_);
lean_closure_set(v___f_1755_, 6, v_cls_1741_);
lean_closure_set(v___f_1755_, 7, v___x_1754_);
lean_closure_set(v___f_1755_, 8, v_tag_1743_);
lean_closure_set(v___f_1755_, 9, v_opts_1749_);
lean_closure_set(v___f_1755_, 10, v_msg_1744_);
lean_closure_set(v___f_1755_, 11, v_toPure_1753_);
lean_closure_set(v___f_1755_, 12, v_toBind_1745_);
lean_closure_set(v___f_1755_, 13, v_k_1746_);
lean_closure_set(v___f_1755_, 14, v_inst_1747_);
v___f_1756_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1756_, 0, v_toPure_1753_);
lean_closure_set(v___f_1756_, 1, v_cls_1741_);
lean_closure_set(v___f_1756_, 2, v_toBind_1745_);
lean_closure_set(v___f_1756_, 3, v_inst_1748_);
v___x_1757_ = lean_apply_4(v_toBind_1745_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1752_, v___f_1756_);
v___x_1758_ = lean_apply_4(v_toBind_1745_, lean_box(0), lean_box(0), v___x_1757_, v___f_1755_);
return v___x_1758_;
}
else
{
lean_dec_ref(v_opts_1749_);
lean_dec(v_inst_1748_);
lean_dec(v_inst_1747_);
lean_dec(v_toBind_1745_);
lean_dec(v_msg_1744_);
lean_dec_ref(v_tag_1743_);
lean_dec(v_cls_1741_);
lean_dec_ref(v_inst_1740_);
lean_dec(v_inst_1739_);
lean_dec_ref(v_inst_1738_);
lean_dec_ref(v_inst_1737_);
lean_dec_ref(v_always_1736_);
lean_dec_ref(v_toApplicative_1735_);
lean_dec_ref(v_inst_1734_);
return v_k_1746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13___boxed(lean_object* v_inst_1759_, lean_object* v_toApplicative_1760_, lean_object* v_always_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_cls_1766_, lean_object* v_collapsed_1767_, lean_object* v_tag_1768_, lean_object* v_msg_1769_, lean_object* v_toBind_1770_, lean_object* v_k_1771_, lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_opts_1774_){
_start:
{
uint8_t v_collapsed_boxed_1775_; lean_object* v_res_1776_; 
v_collapsed_boxed_1775_ = lean_unbox(v_collapsed_1767_);
v_res_1776_ = l_Lean_withTraceNode___redArg___lam__13(v_inst_1759_, v_toApplicative_1760_, v_always_1761_, v_inst_1762_, v_inst_1763_, v_inst_1764_, v_inst_1765_, v_cls_1766_, v_collapsed_boxed_1775_, v_tag_1768_, v_msg_1769_, v_toBind_1770_, v_k_1771_, v_inst_1772_, v_inst_1773_, v_opts_1774_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_always_1782_, lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_cls_1785_, lean_object* v_msg_1786_, lean_object* v_k_1787_, uint8_t v_collapsed_1788_, lean_object* v_tag_1789_){
_start:
{
lean_object* v_toApplicative_1790_; lean_object* v_toBind_1791_; lean_object* v___x_1792_; lean_object* v___f_1793_; lean_object* v___x_1794_; 
v_toApplicative_1790_ = lean_ctor_get(v_inst_1777_, 0);
lean_inc_ref(v_toApplicative_1790_);
v_toBind_1791_ = lean_ctor_get(v_inst_1777_, 1);
lean_inc_n(v_toBind_1791_, 2);
v___x_1792_ = lean_box(v_collapsed_1788_);
lean_inc(v_inst_1781_);
v___f_1793_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1793_, 0, v_inst_1778_);
lean_closure_set(v___f_1793_, 1, v_toApplicative_1790_);
lean_closure_set(v___f_1793_, 2, v_always_1782_);
lean_closure_set(v___f_1793_, 3, v_inst_1777_);
lean_closure_set(v___f_1793_, 4, v_inst_1779_);
lean_closure_set(v___f_1793_, 5, v_inst_1780_);
lean_closure_set(v___f_1793_, 6, v_inst_1784_);
lean_closure_set(v___f_1793_, 7, v_cls_1785_);
lean_closure_set(v___f_1793_, 8, v___x_1792_);
lean_closure_set(v___f_1793_, 9, v_tag_1789_);
lean_closure_set(v___f_1793_, 10, v_msg_1786_);
lean_closure_set(v___f_1793_, 11, v_toBind_1791_);
lean_closure_set(v___f_1793_, 12, v_k_1787_);
lean_closure_set(v___f_1793_, 13, v_inst_1783_);
lean_closure_set(v___f_1793_, 14, v_inst_1781_);
v___x_1794_ = lean_apply_4(v_toBind_1791_, lean_box(0), lean_box(0), v_inst_1781_, v___f_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_, lean_object* v_inst_1799_, lean_object* v_always_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_cls_1803_, lean_object* v_msg_1804_, lean_object* v_k_1805_, lean_object* v_collapsed_1806_, lean_object* v_tag_1807_){
_start:
{
uint8_t v_collapsed_boxed_1808_; lean_object* v_res_1809_; 
v_collapsed_boxed_1808_ = lean_unbox(v_collapsed_1806_);
v_res_1809_ = l_Lean_withTraceNode___redArg(v_inst_1795_, v_inst_1796_, v_inst_1797_, v_inst_1798_, v_inst_1799_, v_always_1800_, v_inst_1801_, v_inst_1802_, v_cls_1803_, v_msg_1804_, v_k_1805_, v_collapsed_boxed_1808_, v_tag_1807_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object* v_00_u03b1_1810_, lean_object* v_m_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_00_u03b5_1817_, lean_object* v_always_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_cls_1821_, lean_object* v_msg_1822_, lean_object* v_k_1823_, uint8_t v_collapsed_1824_, lean_object* v_tag_1825_){
_start:
{
lean_object* v_toApplicative_1826_; lean_object* v_toBind_1827_; lean_object* v___x_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; 
v_toApplicative_1826_ = lean_ctor_get(v_inst_1812_, 0);
lean_inc_ref(v_toApplicative_1826_);
v_toBind_1827_ = lean_ctor_get(v_inst_1812_, 1);
lean_inc_n(v_toBind_1827_, 2);
v___x_1828_ = lean_box(v_collapsed_1824_);
lean_inc(v_inst_1816_);
v___f_1829_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1829_, 0, v_inst_1813_);
lean_closure_set(v___f_1829_, 1, v_toApplicative_1826_);
lean_closure_set(v___f_1829_, 2, v_always_1818_);
lean_closure_set(v___f_1829_, 3, v_inst_1812_);
lean_closure_set(v___f_1829_, 4, v_inst_1814_);
lean_closure_set(v___f_1829_, 5, v_inst_1815_);
lean_closure_set(v___f_1829_, 6, v_inst_1820_);
lean_closure_set(v___f_1829_, 7, v_cls_1821_);
lean_closure_set(v___f_1829_, 8, v___x_1828_);
lean_closure_set(v___f_1829_, 9, v_tag_1825_);
lean_closure_set(v___f_1829_, 10, v_msg_1822_);
lean_closure_set(v___f_1829_, 11, v_toBind_1827_);
lean_closure_set(v___f_1829_, 12, v_k_1823_);
lean_closure_set(v___f_1829_, 13, v_inst_1819_);
lean_closure_set(v___f_1829_, 14, v_inst_1816_);
v___x_1830_ = lean_apply_4(v_toBind_1827_, lean_box(0), lean_box(0), v_inst_1816_, v___f_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object* v_00_u03b1_1831_, lean_object* v_m_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_00_u03b5_1838_, lean_object* v_always_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_cls_1842_, lean_object* v_msg_1843_, lean_object* v_k_1844_, lean_object* v_collapsed_1845_, lean_object* v_tag_1846_){
_start:
{
uint8_t v_collapsed_boxed_1847_; lean_object* v_res_1848_; 
v_collapsed_boxed_1847_ = lean_unbox(v_collapsed_1845_);
v_res_1848_ = l_Lean_withTraceNode(v_00_u03b1_1831_, v_m_1832_, v_inst_1833_, v_inst_1834_, v_inst_1835_, v_inst_1836_, v_inst_1837_, v_00_u03b5_1838_, v_always_1839_, v_inst_1840_, v_inst_1841_, v_cls_1842_, v_msg_1843_, v_k_1844_, v_collapsed_boxed_1847_, v_tag_1846_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object* v_self_1849_){
_start:
{
lean_object* v_fst_1850_; 
v_fst_1850_ = lean_ctor_get(v_self_1849_, 0);
lean_inc(v_fst_1850_);
return v_fst_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object* v_self_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_1851_);
lean_dec_ref(v_self_1851_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object* v_toPure_1853_, lean_object* v_x_1854_){
_start:
{
if (lean_obj_tag(v_x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_a_1855_ = lean_ctor_get(v_x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v_x_1854_, 1);
v___x_1856_ = l_Lean_Exception_toMessageData(v_a_1855_);
v___x_1857_ = lean_apply_2(v_toPure_1853_, lean_box(0), v___x_1856_);
return v___x_1857_;
}
else
{
lean_object* v_a_1858_; lean_object* v_snd_1859_; lean_object* v___x_1860_; 
v_a_1858_ = lean_ctor_get(v_x_1854_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v_x_1854_, 1);
v_snd_1859_ = lean_ctor_get(v_a_1858_, 1);
lean_inc(v_snd_1859_);
lean_dec(v_a_1858_);
v___x_1860_ = lean_apply_2(v_toPure_1853_, lean_box(0), v_snd_1859_);
return v___x_1860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object* v_toPure_1861_, lean_object* v_ex_1862_){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_ex_1862_);
v___x_1864_ = lean_apply_2(v_toPure_1861_, lean_box(0), v___x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object* v_toPure_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_a_1866_);
v___x_1868_ = lean_apply_2(v_toPure_1865_, lean_box(0), v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v___f_1874_, lean_object* v_cls_1875_, uint8_t v_collapsed_1876_, lean_object* v_tag_1877_, lean_object* v_opts_1878_, uint8_t v_clsEnabled_1879_, lean_object* v_oldTraces_1880_, lean_object* v_msg_1881_, lean_object* v_resStartStop_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1869_, v_inst_1870_, v_inst_1871_, v_inst_1872_, v_inst_1873_, v___f_1874_, v_cls_1875_, v_collapsed_1876_, v_tag_1877_, v_opts_1878_, v_clsEnabled_1879_, v_oldTraces_1880_, v_msg_1881_, v_resStartStop_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3___boxed(lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v___f_1889_, lean_object* v_cls_1890_, lean_object* v_collapsed_1891_, lean_object* v_tag_1892_, lean_object* v_opts_1893_, lean_object* v_clsEnabled_1894_, lean_object* v_oldTraces_1895_, lean_object* v_msg_1896_, lean_object* v_resStartStop_1897_){
_start:
{
uint8_t v_collapsed_boxed_1898_; uint8_t v_clsEnabled_boxed_1899_; lean_object* v_res_1900_; 
v_collapsed_boxed_1898_ = lean_unbox(v_collapsed_1891_);
v_clsEnabled_boxed_1899_ = lean_unbox(v_clsEnabled_1894_);
v_res_1900_ = l_Lean_withTraceNode_x27___redArg___lam__3(v_inst_1884_, v_inst_1885_, v_inst_1886_, v_inst_1887_, v_inst_1888_, v___f_1889_, v_cls_1890_, v_collapsed_boxed_1898_, v_tag_1892_, v_opts_1893_, v_clsEnabled_boxed_1899_, v_oldTraces_1895_, v_msg_1896_, v_resStartStop_1897_);
lean_dec_ref(v_opts_1893_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object* v_start_1901_, lean_object* v_a_1902_, lean_object* v_toPure_1903_, lean_object* v_stop_1904_){
_start:
{
double v___x_1905_; double v___x_1906_; double v___x_1907_; double v___x_1908_; double v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1905_ = lean_float_of_nat(v_start_1901_);
v___x_1906_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1907_ = lean_float_div(v___x_1905_, v___x_1906_);
v___x_1908_ = lean_float_of_nat(v_stop_1904_);
v___x_1909_ = lean_float_div(v___x_1908_, v___x_1906_);
v___x_1910_ = lean_box_float(v___x_1907_);
v___x_1911_ = lean_box_float(v___x_1909_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_a_1902_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_apply_2(v_toPure_1903_, lean_box(0), v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object* v_start_1915_, lean_object* v_toPure_1916_, lean_object* v_toBind_1917_, lean_object* v___x_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___f_1920_; lean_object* v___x_1921_; 
v___f_1920_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__5), 4, 3);
lean_closure_set(v___f_1920_, 0, v_start_1915_);
lean_closure_set(v___f_1920_, 1, v_a_1919_);
lean_closure_set(v___f_1920_, 2, v_toPure_1916_);
v___x_1921_ = lean_apply_4(v_toBind_1917_, lean_box(0), lean_box(0), v___x_1918_, v___f_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object* v_toPure_1922_, lean_object* v_toBind_1923_, lean_object* v___x_1924_, lean_object* v___x_1925_, lean_object* v_start_1926_){
_start:
{
lean_object* v___f_1927_; lean_object* v___x_1928_; 
lean_inc(v_toBind_1923_);
v___f_1927_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__6), 5, 4);
lean_closure_set(v___f_1927_, 0, v_start_1926_);
lean_closure_set(v___f_1927_, 1, v_toPure_1922_);
lean_closure_set(v___f_1927_, 2, v_toBind_1923_);
lean_closure_set(v___f_1927_, 3, v___x_1924_);
v___x_1928_ = lean_apply_4(v_toBind_1923_, lean_box(0), lean_box(0), v___x_1925_, v___f_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object* v_start_1929_, lean_object* v_a_1930_, lean_object* v_toPure_1931_, lean_object* v_stop_1932_){
_start:
{
double v___x_1933_; double v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1933_ = lean_float_of_nat(v_start_1929_);
v___x_1934_ = lean_float_of_nat(v_stop_1932_);
v___x_1935_ = lean_box_float(v___x_1933_);
v___x_1936_ = lean_box_float(v___x_1934_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_a_1930_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_apply_2(v_toPure_1931_, lean_box(0), v___x_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object* v_start_1940_, lean_object* v_toPure_1941_, lean_object* v_toBind_1942_, lean_object* v___x_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v___f_1945_; lean_object* v___x_1946_; 
v___f_1945_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__8), 4, 3);
lean_closure_set(v___f_1945_, 0, v_start_1940_);
lean_closure_set(v___f_1945_, 1, v_a_1944_);
lean_closure_set(v___f_1945_, 2, v_toPure_1941_);
v___x_1946_ = lean_apply_4(v_toBind_1942_, lean_box(0), lean_box(0), v___x_1943_, v___f_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object* v_toPure_1947_, lean_object* v_toBind_1948_, lean_object* v___x_1949_, lean_object* v___x_1950_, lean_object* v_start_1951_){
_start:
{
lean_object* v___f_1952_; lean_object* v___x_1953_; 
lean_inc(v_toBind_1948_);
v___f_1952_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__9), 5, 4);
lean_closure_set(v___f_1952_, 0, v_start_1951_);
lean_closure_set(v___f_1952_, 1, v_toPure_1947_);
lean_closure_set(v___f_1952_, 2, v_toBind_1948_);
lean_closure_set(v___f_1952_, 3, v___x_1949_);
v___x_1953_ = lean_apply_4(v_toBind_1948_, lean_box(0), lean_box(0), v___x_1950_, v___f_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v___f_1959_, lean_object* v_cls_1960_, uint8_t v_collapsed_1961_, lean_object* v_tag_1962_, lean_object* v_opts_1963_, uint8_t v_clsEnabled_1964_, lean_object* v_msg_1965_, lean_object* v_toBind_1966_, lean_object* v_k_1967_, lean_object* v___f_1968_, lean_object* v___f_1969_, lean_object* v_inst_1970_, lean_object* v_toPure_1971_, lean_object* v_oldTraces_1972_){
_start:
{
lean_object* v_tryCatch_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___f_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v_tryCatch_1973_ = lean_ctor_get(v_inst_1954_, 1);
lean_inc(v_tryCatch_1973_);
v___x_1974_ = lean_box(v_collapsed_1961_);
v___x_1975_ = lean_box(v_clsEnabled_1964_);
lean_inc_ref(v_opts_1963_);
v___f_1976_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_1976_, 0, v_inst_1955_);
lean_closure_set(v___f_1976_, 1, v_inst_1956_);
lean_closure_set(v___f_1976_, 2, v_inst_1957_);
lean_closure_set(v___f_1976_, 3, v_inst_1958_);
lean_closure_set(v___f_1976_, 4, v_inst_1954_);
lean_closure_set(v___f_1976_, 5, v___f_1959_);
lean_closure_set(v___f_1976_, 6, v_cls_1960_);
lean_closure_set(v___f_1976_, 7, v___x_1974_);
lean_closure_set(v___f_1976_, 8, v_tag_1962_);
lean_closure_set(v___f_1976_, 9, v_opts_1963_);
lean_closure_set(v___f_1976_, 10, v___x_1975_);
lean_closure_set(v___f_1976_, 11, v_oldTraces_1972_);
lean_closure_set(v___f_1976_, 12, v_msg_1965_);
lean_inc(v_toBind_1966_);
v___x_1977_ = lean_apply_4(v_toBind_1966_, lean_box(0), lean_box(0), v_k_1967_, v___f_1968_);
v___x_1978_ = lean_apply_3(v_tryCatch_1973_, lean_box(0), v___x_1977_, v___f_1969_);
v___x_1979_ = l_Lean_KVMap_instValueBool;
v___x_1980_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1981_ = l_Lean_Option_get___redArg(v___x_1979_, v_opts_1963_, v___x_1980_);
lean_dec_ref(v_opts_1963_);
v___x_1982_ = lean_unbox(v___x_1981_);
lean_dec(v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___f_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1983_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1984_ = lean_apply_2(v_inst_1970_, lean_box(0), v___x_1983_);
lean_inc(v___x_1984_);
lean_inc_n(v_toBind_1966_, 2);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1985_, 0, v_toPure_1971_);
lean_closure_set(v___f_1985_, 1, v_toBind_1966_);
lean_closure_set(v___f_1985_, 2, v___x_1984_);
lean_closure_set(v___f_1985_, 3, v___x_1978_);
v___x_1986_ = lean_apply_4(v_toBind_1966_, lean_box(0), lean_box(0), v___x_1984_, v___f_1985_);
v___x_1987_ = lean_apply_4(v_toBind_1966_, lean_box(0), lean_box(0), v___x_1986_, v___f_1976_);
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1988_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1989_ = lean_apply_2(v_inst_1970_, lean_box(0), v___x_1988_);
lean_inc(v___x_1989_);
lean_inc_n(v_toBind_1966_, 2);
v___f_1990_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__10), 5, 4);
lean_closure_set(v___f_1990_, 0, v_toPure_1971_);
lean_closure_set(v___f_1990_, 1, v_toBind_1966_);
lean_closure_set(v___f_1990_, 2, v___x_1989_);
lean_closure_set(v___f_1990_, 3, v___x_1978_);
v___x_1991_ = lean_apply_4(v_toBind_1966_, lean_box(0), lean_box(0), v___x_1989_, v___f_1990_);
v___x_1992_ = lean_apply_4(v_toBind_1966_, lean_box(0), lean_box(0), v___x_1991_, v___f_1976_);
return v___x_1992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_1993_ = _args[0];
lean_object* v_inst_1994_ = _args[1];
lean_object* v_inst_1995_ = _args[2];
lean_object* v_inst_1996_ = _args[3];
lean_object* v_inst_1997_ = _args[4];
lean_object* v___f_1998_ = _args[5];
lean_object* v_cls_1999_ = _args[6];
lean_object* v_collapsed_2000_ = _args[7];
lean_object* v_tag_2001_ = _args[8];
lean_object* v_opts_2002_ = _args[9];
lean_object* v_clsEnabled_2003_ = _args[10];
lean_object* v_msg_2004_ = _args[11];
lean_object* v_toBind_2005_ = _args[12];
lean_object* v_k_2006_ = _args[13];
lean_object* v___f_2007_ = _args[14];
lean_object* v___f_2008_ = _args[15];
lean_object* v_inst_2009_ = _args[16];
lean_object* v_toPure_2010_ = _args[17];
lean_object* v_oldTraces_2011_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_2012_; uint8_t v_clsEnabled_boxed_2013_; lean_object* v_res_2014_; 
v_collapsed_boxed_2012_ = lean_unbox(v_collapsed_2000_);
v_clsEnabled_boxed_2013_ = lean_unbox(v_clsEnabled_2003_);
v_res_2014_ = l_Lean_withTraceNode_x27___redArg___lam__11(v_inst_1993_, v_inst_1994_, v_inst_1995_, v_inst_1996_, v_inst_1997_, v___f_1998_, v_cls_1999_, v_collapsed_boxed_2012_, v_tag_2001_, v_opts_2002_, v_clsEnabled_boxed_2013_, v_msg_2004_, v_toBind_2005_, v_k_2006_, v___f_2007_, v___f_2008_, v_inst_2009_, v_toPure_2010_, v_oldTraces_2011_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v___f_2020_, lean_object* v_cls_2021_, uint8_t v_collapsed_2022_, lean_object* v_tag_2023_, lean_object* v_opts_2024_, lean_object* v_msg_2025_, lean_object* v_toBind_2026_, lean_object* v_k_2027_, lean_object* v___f_2028_, lean_object* v___f_2029_, lean_object* v_inst_2030_, lean_object* v_toPure_2031_, uint8_t v_clsEnabled_2032_){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___f_2035_; 
v___x_2033_ = lean_box(v_collapsed_2022_);
v___x_2034_ = lean_box(v_clsEnabled_2032_);
lean_inc(v_k_2027_);
lean_inc(v_toBind_2026_);
lean_inc_ref(v_opts_2024_);
lean_inc_ref(v_inst_2017_);
lean_inc_ref(v_inst_2016_);
v___f_2035_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__11___boxed), 19, 18);
lean_closure_set(v___f_2035_, 0, v_inst_2015_);
lean_closure_set(v___f_2035_, 1, v_inst_2016_);
lean_closure_set(v___f_2035_, 2, v_inst_2017_);
lean_closure_set(v___f_2035_, 3, v_inst_2018_);
lean_closure_set(v___f_2035_, 4, v_inst_2019_);
lean_closure_set(v___f_2035_, 5, v___f_2020_);
lean_closure_set(v___f_2035_, 6, v_cls_2021_);
lean_closure_set(v___f_2035_, 7, v___x_2033_);
lean_closure_set(v___f_2035_, 8, v_tag_2023_);
lean_closure_set(v___f_2035_, 9, v_opts_2024_);
lean_closure_set(v___f_2035_, 10, v___x_2034_);
lean_closure_set(v___f_2035_, 11, v_msg_2025_);
lean_closure_set(v___f_2035_, 12, v_toBind_2026_);
lean_closure_set(v___f_2035_, 13, v_k_2027_);
lean_closure_set(v___f_2035_, 14, v___f_2028_);
lean_closure_set(v___f_2035_, 15, v___f_2029_);
lean_closure_set(v___f_2035_, 16, v_inst_2030_);
lean_closure_set(v___f_2035_, 17, v_toPure_2031_);
if (v_clsEnabled_2032_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2039_ = l_Lean_KVMap_instValueBool;
v___x_2040_ = l_Lean_trace_profiler;
v___x_2041_ = l_Lean_Option_get___redArg(v___x_2039_, v_opts_2024_, v___x_2040_);
lean_dec_ref(v_opts_2024_);
v___x_2042_ = lean_unbox(v___x_2041_);
lean_dec(v___x_2041_);
if (v___x_2042_ == 0)
{
lean_dec_ref(v___f_2035_);
lean_dec(v_toBind_2026_);
lean_dec_ref(v_inst_2017_);
lean_dec_ref(v_inst_2016_);
return v_k_2027_;
}
else
{
lean_dec(v_k_2027_);
goto v___jp_2036_;
}
}
else
{
lean_dec(v_k_2027_);
lean_dec_ref(v_opts_2024_);
goto v___jp_2036_;
}
v___jp_2036_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_2016_, v_inst_2017_);
v___x_2038_ = lean_apply_4(v_toBind_2026_, lean_box(0), lean_box(0), v___x_2037_, v___f_2035_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_inst_2043_ = _args[0];
lean_object* v_inst_2044_ = _args[1];
lean_object* v_inst_2045_ = _args[2];
lean_object* v_inst_2046_ = _args[3];
lean_object* v_inst_2047_ = _args[4];
lean_object* v___f_2048_ = _args[5];
lean_object* v_cls_2049_ = _args[6];
lean_object* v_collapsed_2050_ = _args[7];
lean_object* v_tag_2051_ = _args[8];
lean_object* v_opts_2052_ = _args[9];
lean_object* v_msg_2053_ = _args[10];
lean_object* v_toBind_2054_ = _args[11];
lean_object* v_k_2055_ = _args[12];
lean_object* v___f_2056_ = _args[13];
lean_object* v___f_2057_ = _args[14];
lean_object* v_inst_2058_ = _args[15];
lean_object* v_toPure_2059_ = _args[16];
lean_object* v_clsEnabled_2060_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2061_; uint8_t v_clsEnabled_boxed_2062_; lean_object* v_res_2063_; 
v_collapsed_boxed_2061_ = lean_unbox(v_collapsed_2050_);
v_clsEnabled_boxed_2062_ = lean_unbox(v_clsEnabled_2060_);
v_res_2063_ = l_Lean_withTraceNode_x27___redArg___lam__12(v_inst_2043_, v_inst_2044_, v_inst_2045_, v_inst_2046_, v_inst_2047_, v___f_2048_, v_cls_2049_, v_collapsed_boxed_2061_, v_tag_2051_, v_opts_2052_, v_msg_2053_, v_toBind_2054_, v_k_2055_, v___f_2056_, v___f_2057_, v_inst_2058_, v_toPure_2059_, v_clsEnabled_boxed_2062_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v___f_2069_, lean_object* v_cls_2070_, uint8_t v_collapsed_2071_, lean_object* v_tag_2072_, lean_object* v_msg_2073_, lean_object* v_toBind_2074_, lean_object* v_k_2075_, lean_object* v___f_2076_, lean_object* v___f_2077_, lean_object* v_inst_2078_, lean_object* v_toPure_2079_, lean_object* v___f_2080_, lean_object* v_opts_2081_){
_start:
{
uint8_t v_hasTrace_2082_; uint8_t v___x_2083_; 
v_hasTrace_2082_ = lean_ctor_get_uint8(v_opts_2081_, sizeof(void*)*1);
v___x_2083_ = lean_bool_not(v_hasTrace_2082_);
if (v___x_2083_ == 0)
{
lean_object* v_getInheritedTraceOptions_2084_; lean_object* v___x_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_getInheritedTraceOptions_2084_ = lean_ctor_get(v_inst_2064_, 2);
lean_inc(v_getInheritedTraceOptions_2084_);
v___x_2085_ = lean_box(v_collapsed_2071_);
lean_inc_n(v_toBind_2074_, 2);
v___f_2086_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_2086_, 0, v_inst_2065_);
lean_closure_set(v___f_2086_, 1, v_inst_2066_);
lean_closure_set(v___f_2086_, 2, v_inst_2064_);
lean_closure_set(v___f_2086_, 3, v_inst_2067_);
lean_closure_set(v___f_2086_, 4, v_inst_2068_);
lean_closure_set(v___f_2086_, 5, v___f_2069_);
lean_closure_set(v___f_2086_, 6, v_cls_2070_);
lean_closure_set(v___f_2086_, 7, v___x_2085_);
lean_closure_set(v___f_2086_, 8, v_tag_2072_);
lean_closure_set(v___f_2086_, 9, v_opts_2081_);
lean_closure_set(v___f_2086_, 10, v_msg_2073_);
lean_closure_set(v___f_2086_, 11, v_toBind_2074_);
lean_closure_set(v___f_2086_, 12, v_k_2075_);
lean_closure_set(v___f_2086_, 13, v___f_2076_);
lean_closure_set(v___f_2086_, 14, v___f_2077_);
lean_closure_set(v___f_2086_, 15, v_inst_2078_);
lean_closure_set(v___f_2086_, 16, v_toPure_2079_);
v___x_2087_ = lean_apply_4(v_toBind_2074_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2084_, v___f_2080_);
v___x_2088_ = lean_apply_4(v_toBind_2074_, lean_box(0), lean_box(0), v___x_2087_, v___f_2086_);
return v___x_2088_;
}
else
{
lean_dec_ref(v_opts_2081_);
lean_dec(v___f_2080_);
lean_dec(v_toPure_2079_);
lean_dec(v_inst_2078_);
lean_dec(v___f_2077_);
lean_dec(v___f_2076_);
lean_dec(v_toBind_2074_);
lean_dec(v_msg_2073_);
lean_dec_ref(v_tag_2072_);
lean_dec(v_cls_2070_);
lean_dec_ref(v___f_2069_);
lean_dec(v_inst_2068_);
lean_dec_ref(v_inst_2067_);
lean_dec_ref(v_inst_2066_);
lean_dec_ref(v_inst_2065_);
lean_dec_ref(v_inst_2064_);
return v_k_2075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_inst_2089_ = _args[0];
lean_object* v_inst_2090_ = _args[1];
lean_object* v_inst_2091_ = _args[2];
lean_object* v_inst_2092_ = _args[3];
lean_object* v_inst_2093_ = _args[4];
lean_object* v___f_2094_ = _args[5];
lean_object* v_cls_2095_ = _args[6];
lean_object* v_collapsed_2096_ = _args[7];
lean_object* v_tag_2097_ = _args[8];
lean_object* v_msg_2098_ = _args[9];
lean_object* v_toBind_2099_ = _args[10];
lean_object* v_k_2100_ = _args[11];
lean_object* v___f_2101_ = _args[12];
lean_object* v___f_2102_ = _args[13];
lean_object* v_inst_2103_ = _args[14];
lean_object* v_toPure_2104_ = _args[15];
lean_object* v___f_2105_ = _args[16];
lean_object* v_opts_2106_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2107_; lean_object* v_res_2108_; 
v_collapsed_boxed_2107_ = lean_unbox(v_collapsed_2096_);
v_res_2108_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_inst_2089_, v_inst_2090_, v_inst_2091_, v_inst_2092_, v_inst_2093_, v___f_2094_, v_cls_2095_, v_collapsed_boxed_2107_, v_tag_2097_, v_msg_2098_, v_toBind_2099_, v_k_2100_, v___f_2101_, v___f_2102_, v_inst_2103_, v_toPure_2104_, v___f_2105_, v_opts_2106_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_cls_2117_, lean_object* v_k_2118_, uint8_t v_collapsed_2119_, lean_object* v_tag_2120_){
_start:
{
lean_object* v_toApplicative_2121_; lean_object* v_toFunctor_2122_; lean_object* v_toBind_2123_; lean_object* v_toPure_2124_; lean_object* v_map_2125_; lean_object* v___f_2126_; lean_object* v_msg_2127_; lean_object* v___f_2128_; lean_object* v___f_2129_; lean_object* v___f_2130_; lean_object* v___f_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_toApplicative_2121_ = lean_ctor_get(v_inst_2110_, 0);
v_toFunctor_2122_ = lean_ctor_get(v_toApplicative_2121_, 0);
v_toBind_2123_ = lean_ctor_get(v_inst_2110_, 1);
lean_inc_n(v_toBind_2123_, 3);
v_toPure_2124_ = lean_ctor_get(v_toApplicative_2121_, 1);
lean_inc_n(v_toPure_2124_, 5);
v_map_2125_ = lean_ctor_get(v_toFunctor_2122_, 0);
lean_inc(v_map_2125_);
v___f_2126_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2127_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2127_, 0, v_toPure_2124_);
lean_inc(v_inst_2114_);
lean_inc(v_cls_2117_);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2128_, 0, v_toPure_2124_);
lean_closure_set(v___f_2128_, 1, v_cls_2117_);
lean_closure_set(v___f_2128_, 2, v_toBind_2123_);
lean_closure_set(v___f_2128_, 3, v_inst_2114_);
v___f_2129_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2129_, 0, v_toPure_2124_);
v___f_2130_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2130_, 0, v_toPure_2124_);
v___f_2131_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2132_ = lean_box(v_collapsed_2119_);
v___f_2133_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2133_, 0, v_inst_2111_);
lean_closure_set(v___f_2133_, 1, v_inst_2115_);
lean_closure_set(v___f_2133_, 2, v_inst_2110_);
lean_closure_set(v___f_2133_, 3, v_inst_2112_);
lean_closure_set(v___f_2133_, 4, v_inst_2113_);
lean_closure_set(v___f_2133_, 5, v___f_2131_);
lean_closure_set(v___f_2133_, 6, v_cls_2117_);
lean_closure_set(v___f_2133_, 7, v___x_2132_);
lean_closure_set(v___f_2133_, 8, v_tag_2120_);
lean_closure_set(v___f_2133_, 9, v_msg_2127_);
lean_closure_set(v___f_2133_, 10, v_toBind_2123_);
lean_closure_set(v___f_2133_, 11, v_k_2118_);
lean_closure_set(v___f_2133_, 12, v___f_2130_);
lean_closure_set(v___f_2133_, 13, v___f_2129_);
lean_closure_set(v___f_2133_, 14, v_inst_2116_);
lean_closure_set(v___f_2133_, 15, v_toPure_2124_);
lean_closure_set(v___f_2133_, 16, v___f_2128_);
v___x_2134_ = lean_apply_4(v_toBind_2123_, lean_box(0), lean_box(0), v_inst_2114_, v___f_2133_);
v___x_2135_ = lean_apply_4(v_map_2125_, lean_box(0), lean_box(0), v___f_2126_, v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_cls_2143_, lean_object* v_k_2144_, lean_object* v_collapsed_2145_, lean_object* v_tag_2146_){
_start:
{
uint8_t v_collapsed_boxed_2147_; lean_object* v_res_2148_; 
v_collapsed_boxed_2147_ = lean_unbox(v_collapsed_2145_);
v_res_2148_ = l_Lean_withTraceNode_x27___redArg(v_inst_2136_, v_inst_2137_, v_inst_2138_, v_inst_2139_, v_inst_2140_, v_inst_2141_, v_inst_2142_, v_cls_2143_, v_k_2144_, v_collapsed_boxed_2147_, v_tag_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object* v_00_u03b1_2149_, lean_object* v_m_2150_, lean_object* v_inst_2151_, lean_object* v_inst_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_, lean_object* v_inst_2155_, lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_cls_2158_, lean_object* v_k_2159_, uint8_t v_collapsed_2160_, lean_object* v_tag_2161_){
_start:
{
lean_object* v_toApplicative_2162_; lean_object* v_toFunctor_2163_; lean_object* v_toBind_2164_; lean_object* v_toPure_2165_; lean_object* v_map_2166_; lean_object* v___f_2167_; lean_object* v_msg_2168_; lean_object* v___f_2169_; lean_object* v___f_2170_; lean_object* v___f_2171_; lean_object* v___f_2172_; lean_object* v___x_2173_; lean_object* v___f_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_toApplicative_2162_ = lean_ctor_get(v_inst_2151_, 0);
v_toFunctor_2163_ = lean_ctor_get(v_toApplicative_2162_, 0);
v_toBind_2164_ = lean_ctor_get(v_inst_2151_, 1);
lean_inc_n(v_toBind_2164_, 3);
v_toPure_2165_ = lean_ctor_get(v_toApplicative_2162_, 1);
lean_inc_n(v_toPure_2165_, 5);
v_map_2166_ = lean_ctor_get(v_toFunctor_2163_, 0);
lean_inc(v_map_2166_);
v___f_2167_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2168_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2168_, 0, v_toPure_2165_);
lean_inc(v_inst_2155_);
lean_inc(v_cls_2158_);
v___f_2169_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2169_, 0, v_toPure_2165_);
lean_closure_set(v___f_2169_, 1, v_cls_2158_);
lean_closure_set(v___f_2169_, 2, v_toBind_2164_);
lean_closure_set(v___f_2169_, 3, v_inst_2155_);
v___f_2170_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2170_, 0, v_toPure_2165_);
v___f_2171_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2171_, 0, v_toPure_2165_);
v___f_2172_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2173_ = lean_box(v_collapsed_2160_);
v___f_2174_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2174_, 0, v_inst_2152_);
lean_closure_set(v___f_2174_, 1, v_inst_2156_);
lean_closure_set(v___f_2174_, 2, v_inst_2151_);
lean_closure_set(v___f_2174_, 3, v_inst_2153_);
lean_closure_set(v___f_2174_, 4, v_inst_2154_);
lean_closure_set(v___f_2174_, 5, v___f_2172_);
lean_closure_set(v___f_2174_, 6, v_cls_2158_);
lean_closure_set(v___f_2174_, 7, v___x_2173_);
lean_closure_set(v___f_2174_, 8, v_tag_2161_);
lean_closure_set(v___f_2174_, 9, v_msg_2168_);
lean_closure_set(v___f_2174_, 10, v_toBind_2164_);
lean_closure_set(v___f_2174_, 11, v_k_2159_);
lean_closure_set(v___f_2174_, 12, v___f_2171_);
lean_closure_set(v___f_2174_, 13, v___f_2170_);
lean_closure_set(v___f_2174_, 14, v_inst_2157_);
lean_closure_set(v___f_2174_, 15, v_toPure_2165_);
lean_closure_set(v___f_2174_, 16, v___f_2169_);
v___x_2175_ = lean_apply_4(v_toBind_2164_, lean_box(0), lean_box(0), v_inst_2155_, v___f_2174_);
v___x_2176_ = lean_apply_4(v_map_2166_, lean_box(0), lean_box(0), v___f_2167_, v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_m_2178_, lean_object* v_inst_2179_, lean_object* v_inst_2180_, lean_object* v_inst_2181_, lean_object* v_inst_2182_, lean_object* v_inst_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_cls_2186_, lean_object* v_k_2187_, lean_object* v_collapsed_2188_, lean_object* v_tag_2189_){
_start:
{
uint8_t v_collapsed_boxed_2190_; lean_object* v_res_2191_; 
v_collapsed_boxed_2190_ = lean_unbox(v_collapsed_2188_);
v_res_2191_ = l_Lean_withTraceNode_x27(v_00_u03b1_2177_, v_m_2178_, v_inst_2179_, v_inst_2180_, v_inst_2181_, v_inst_2182_, v_inst_2183_, v_inst_2184_, v_inst_2185_, v_cls_2186_, v_k_2187_, v_collapsed_boxed_2190_, v_tag_2189_);
return v_res_2191_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__4(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__3));
v___x_2201_ = l_Lean_mkAtom(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__5(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__4, &l_Lean_registerTraceClass___auto__1___closed__4_once, _init_l_Lean_registerTraceClass___auto__1___closed__4);
v___x_2203_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2204_ = lean_array_push(v___x_2203_, v___x_2202_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__6(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__5, &l_Lean_registerTraceClass___auto__1___closed__5_once, _init_l_Lean_registerTraceClass___auto__1___closed__5);
v___x_2206_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__2));
v___x_2207_ = lean_box(2);
v___x_2208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2206_);
lean_ctor_set(v___x_2208_, 2, v___x_2205_);
return v___x_2208_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__7(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__6, &l_Lean_registerTraceClass___auto__1___closed__6_once, _init_l_Lean_registerTraceClass___auto__1___closed__6);
v___x_2210_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_2211_ = lean_array_push(v___x_2210_, v___x_2209_);
return v___x_2211_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2212_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__7, &l_Lean_registerTraceClass___auto__1___closed__7_once, _init_l_Lean_registerTraceClass___auto__1___closed__7);
v___x_2213_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_2214_ = lean_box(2);
v___x_2215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___x_2213_);
lean_ctor_set(v___x_2215_, 2, v___x_2212_);
return v___x_2215_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__8, &l_Lean_registerTraceClass___auto__1___closed__8_once, _init_l_Lean_registerTraceClass___auto__1___closed__8);
v___x_2217_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2218_ = lean_array_push(v___x_2217_, v___x_2216_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2219_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__9, &l_Lean_registerTraceClass___auto__1___closed__9_once, _init_l_Lean_registerTraceClass___auto__1___closed__9);
v___x_2220_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2221_ = lean_box(2);
v___x_2222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___x_2220_);
lean_ctor_set(v___x_2222_, 2, v___x_2219_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__11(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__10, &l_Lean_registerTraceClass___auto__1___closed__10_once, _init_l_Lean_registerTraceClass___auto__1___closed__10);
v___x_2224_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2225_ = lean_array_push(v___x_2224_, v___x_2223_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2226_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__11, &l_Lean_registerTraceClass___auto__1___closed__11_once, _init_l_Lean_registerTraceClass___auto__1___closed__11);
v___x_2227_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_2228_ = lean_box(2);
v___x_2229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v___x_2227_);
lean_ctor_set(v___x_2229_, 2, v___x_2226_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__12, &l_Lean_registerTraceClass___auto__1___closed__12_once, _init_l_Lean_registerTraceClass___auto__1___closed__12);
v___x_2231_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2232_ = lean_array_push(v___x_2231_, v___x_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2233_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__13, &l_Lean_registerTraceClass___auto__1___closed__13_once, _init_l_Lean_registerTraceClass___auto__1___closed__13);
v___x_2234_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_2235_ = lean_box(2);
v___x_2236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set(v___x_2236_, 1, v___x_2234_);
lean_ctor_set(v___x_2236_, 2, v___x_2233_);
return v___x_2236_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1(void){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__14, &l_Lean_registerTraceClass___auto__1___closed__14_once, _init_l_Lean_registerTraceClass___auto__1___closed__14);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
if (lean_obj_tag(v_x_2239_) == 0)
{
return v_x_2238_;
}
else
{
lean_object* v_key_2240_; lean_object* v_value_2241_; lean_object* v_tail_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2268_; 
v_key_2240_ = lean_ctor_get(v_x_2239_, 0);
v_value_2241_ = lean_ctor_get(v_x_2239_, 1);
v_tail_2242_ = lean_ctor_get(v_x_2239_, 2);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_x_2239_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2244_ = v_x_2239_;
v_isShared_2245_ = v_isSharedCheck_2268_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_tail_2242_);
lean_inc(v_value_2241_);
lean_inc(v_key_2240_);
lean_dec(v_x_2239_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2268_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; uint64_t v___y_2248_; 
v___x_2246_ = lean_array_get_size(v_x_2238_);
if (lean_obj_tag(v_key_2240_) == 0)
{
uint64_t v___x_2266_; 
v___x_2266_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2248_ = v___x_2266_;
goto v___jp_2247_;
}
else
{
uint64_t v_hash_2267_; 
v_hash_2267_ = lean_ctor_get_uint64(v_key_2240_, sizeof(void*)*2);
v___y_2248_ = v_hash_2267_;
goto v___jp_2247_;
}
v___jp_2247_:
{
uint64_t v___x_2249_; uint64_t v___x_2250_; uint64_t v_fold_2251_; uint64_t v___x_2252_; uint64_t v___x_2253_; uint64_t v___x_2254_; size_t v___x_2255_; size_t v___x_2256_; size_t v___x_2257_; size_t v___x_2258_; size_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2249_ = 32ULL;
v___x_2250_ = lean_uint64_shift_right(v___y_2248_, v___x_2249_);
v_fold_2251_ = lean_uint64_xor(v___y_2248_, v___x_2250_);
v___x_2252_ = 16ULL;
v___x_2253_ = lean_uint64_shift_right(v_fold_2251_, v___x_2252_);
v___x_2254_ = lean_uint64_xor(v_fold_2251_, v___x_2253_);
v___x_2255_ = lean_uint64_to_usize(v___x_2254_);
v___x_2256_ = lean_usize_of_nat(v___x_2246_);
v___x_2257_ = ((size_t)1ULL);
v___x_2258_ = lean_usize_sub(v___x_2256_, v___x_2257_);
v___x_2259_ = lean_usize_land(v___x_2255_, v___x_2258_);
v___x_2260_ = lean_array_uget_borrowed(v_x_2238_, v___x_2259_);
lean_inc(v___x_2260_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 2, v___x_2260_);
v___x_2262_ = v___x_2244_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_key_2240_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_value_2241_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_array_uset(v_x_2238_, v___x_2259_, v___x_2262_);
v_x_2238_ = v___x_2263_;
v_x_2239_ = v_tail_2242_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object* v_i_2269_, lean_object* v_source_2270_, lean_object* v_target_2271_){
_start:
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = lean_array_get_size(v_source_2270_);
v___x_2273_ = lean_nat_dec_lt(v_i_2269_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_dec_ref(v_source_2270_);
lean_dec(v_i_2269_);
return v_target_2271_;
}
else
{
lean_object* v_es_2274_; lean_object* v___x_2275_; lean_object* v_source_2276_; lean_object* v_target_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_es_2274_ = lean_array_fget(v_source_2270_, v_i_2269_);
v___x_2275_ = lean_box(0);
v_source_2276_ = lean_array_fset(v_source_2270_, v_i_2269_, v___x_2275_);
v_target_2277_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_2271_, v_es_2274_);
v___x_2278_ = lean_unsigned_to_nat(1u);
v___x_2279_ = lean_nat_add(v_i_2269_, v___x_2278_);
lean_dec(v_i_2269_);
v_i_2269_ = v___x_2279_;
v_source_2270_ = v_source_2276_;
v_target_2271_ = v_target_2277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object* v_data_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v_nbuckets_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2282_ = lean_array_get_size(v_data_2281_);
v___x_2283_ = lean_unsigned_to_nat(2u);
v_nbuckets_2284_ = lean_nat_mul(v___x_2282_, v___x_2283_);
v___x_2285_ = lean_unsigned_to_nat(0u);
v___x_2286_ = lean_box(0);
v___x_2287_ = lean_mk_array(v_nbuckets_2284_, v___x_2286_);
v___x_2288_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_2285_, v_data_2281_, v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object* v_m_2289_, lean_object* v_a_2290_, lean_object* v_b_2291_){
_start:
{
lean_object* v_size_2292_; lean_object* v_buckets_2293_; lean_object* v___x_2294_; uint64_t v___y_2296_; 
v_size_2292_ = lean_ctor_get(v_m_2289_, 0);
v_buckets_2293_ = lean_ctor_get(v_m_2289_, 1);
v___x_2294_ = lean_array_get_size(v_buckets_2293_);
if (lean_obj_tag(v_a_2290_) == 0)
{
uint64_t v___x_2333_; 
v___x_2333_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2296_ = v___x_2333_;
goto v___jp_2295_;
}
else
{
uint64_t v_hash_2334_; 
v_hash_2334_ = lean_ctor_get_uint64(v_a_2290_, sizeof(void*)*2);
v___y_2296_ = v_hash_2334_;
goto v___jp_2295_;
}
v___jp_2295_:
{
uint64_t v___x_2297_; uint64_t v___x_2298_; uint64_t v_fold_2299_; uint64_t v___x_2300_; uint64_t v___x_2301_; uint64_t v___x_2302_; size_t v___x_2303_; size_t v___x_2304_; size_t v___x_2305_; size_t v___x_2306_; size_t v___x_2307_; lean_object* v_bkt_2308_; uint8_t v___x_2309_; 
v___x_2297_ = 32ULL;
v___x_2298_ = lean_uint64_shift_right(v___y_2296_, v___x_2297_);
v_fold_2299_ = lean_uint64_xor(v___y_2296_, v___x_2298_);
v___x_2300_ = 16ULL;
v___x_2301_ = lean_uint64_shift_right(v_fold_2299_, v___x_2300_);
v___x_2302_ = lean_uint64_xor(v_fold_2299_, v___x_2301_);
v___x_2303_ = lean_uint64_to_usize(v___x_2302_);
v___x_2304_ = lean_usize_of_nat(v___x_2294_);
v___x_2305_ = ((size_t)1ULL);
v___x_2306_ = lean_usize_sub(v___x_2304_, v___x_2305_);
v___x_2307_ = lean_usize_land(v___x_2303_, v___x_2306_);
v_bkt_2308_ = lean_array_uget_borrowed(v_buckets_2293_, v___x_2307_);
v___x_2309_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_2290_, v_bkt_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2330_; 
lean_inc_ref(v_buckets_2293_);
lean_inc(v_size_2292_);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_m_2289_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; lean_object* v_unused_2332_; 
v_unused_2331_ = lean_ctor_get(v_m_2289_, 1);
lean_dec(v_unused_2331_);
v_unused_2332_ = lean_ctor_get(v_m_2289_, 0);
lean_dec(v_unused_2332_);
v___x_2311_ = v_m_2289_;
v_isShared_2312_ = v_isSharedCheck_2330_;
goto v_resetjp_2310_;
}
else
{
lean_dec(v_m_2289_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2330_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v_size_x27_2314_; lean_object* v___x_2315_; lean_object* v_buckets_x27_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2313_ = lean_unsigned_to_nat(1u);
v_size_x27_2314_ = lean_nat_add(v_size_2292_, v___x_2313_);
lean_dec(v_size_2292_);
lean_inc(v_bkt_2308_);
v___x_2315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2315_, 0, v_a_2290_);
lean_ctor_set(v___x_2315_, 1, v_b_2291_);
lean_ctor_set(v___x_2315_, 2, v_bkt_2308_);
v_buckets_x27_2316_ = lean_array_uset(v_buckets_2293_, v___x_2307_, v___x_2315_);
v___x_2317_ = lean_unsigned_to_nat(4u);
v___x_2318_ = lean_nat_mul(v_size_x27_2314_, v___x_2317_);
v___x_2319_ = lean_unsigned_to_nat(3u);
v___x_2320_ = lean_nat_div(v___x_2318_, v___x_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_array_get_size(v_buckets_x27_2316_);
v___x_2322_ = lean_nat_dec_le(v___x_2320_, v___x_2321_);
lean_dec(v___x_2320_);
if (v___x_2322_ == 0)
{
lean_object* v_val_2323_; lean_object* v___x_2325_; 
v_val_2323_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_2316_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v_val_2323_);
lean_ctor_set(v___x_2311_, 0, v_size_x27_2314_);
v___x_2325_ = v___x_2311_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_size_x27_2314_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_val_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
else
{
lean_object* v___x_2328_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v_buckets_x27_2316_);
lean_ctor_set(v___x_2311_, 0, v_size_x27_2314_);
v___x_2328_ = v___x_2311_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_size_x27_2314_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_buckets_x27_2316_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
else
{
lean_dec(v_b_2291_);
lean_dec(v_a_2290_);
return v_m_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object* v_traceClassName_2338_, uint8_t v_inherited_2339_, lean_object* v_ref_2340_){
_start:
{
lean_object* v___x_2342_; lean_object* v_optionName_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2342_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v_optionName_2343_ = l_Lean_Name_append(v___x_2342_, v_traceClassName_2338_);
v___x_2344_ = ((lean_object*)(l_Lean_registerTraceClass___closed__0));
v___x_2345_ = ((lean_object*)(l_Lean_registerTraceClass___closed__1));
v___x_2346_ = lean_box(0);
lean_inc_n(v_optionName_2343_, 2);
v___x_2347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2347_, 0, v_optionName_2343_);
lean_ctor_set(v___x_2347_, 1, v_ref_2340_);
lean_ctor_set(v___x_2347_, 2, v___x_2344_);
lean_ctor_set(v___x_2347_, 3, v___x_2345_);
lean_ctor_set(v___x_2347_, 4, v___x_2346_);
v___x_2348_ = lean_register_option(v_optionName_2343_, v___x_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2364_; 
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v___x_2348_, 0);
lean_dec(v_unused_2365_);
v___x_2350_ = v___x_2348_;
v_isShared_2351_ = v_isSharedCheck_2364_;
goto v_resetjp_2349_;
}
else
{
lean_dec(v___x_2348_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2364_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
if (v_inherited_2339_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
lean_dec(v_optionName_2343_);
v___x_2352_ = lean_box(0);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2352_);
v___x_2354_ = v___x_2350_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
else
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2356_ = l_Lean_inheritedTraceOptions;
v___x_2357_ = lean_st_ref_take(v___x_2356_);
v___x_2358_ = lean_box(0);
v___x_2359_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2357_, v_optionName_2343_, v___x_2358_);
v___x_2360_ = lean_st_ref_set(v___x_2356_, v___x_2359_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2360_);
v___x_2362_ = v___x_2350_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_dec(v_optionName_2343_);
return v___x_2348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object* v_traceClassName_2366_, lean_object* v_inherited_2367_, lean_object* v_ref_2368_, lean_object* v_a_2369_){
_start:
{
uint8_t v_inherited_boxed_2370_; lean_object* v_res_2371_; 
v_inherited_boxed_2370_ = lean_unbox(v_inherited_2367_);
v_res_2371_ = l_Lean_registerTraceClass(v_traceClassName_2366_, v_inherited_boxed_2370_, v_ref_2368_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(lean_object* v_00_u03b2_2372_, lean_object* v_m_2373_, lean_object* v_a_2374_, lean_object* v_b_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v_m_2373_, v_a_2374_, v_b_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object* v_00_u03b2_2377_, lean_object* v_data_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_data_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2380_, lean_object* v_i_2381_, lean_object* v_source_2382_, lean_object* v_target_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_i_2381_, v_source_2382_, v_target_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2386_, v_x_2387_);
return v___x_2388_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_2399_ = l_String_toRawSubstring_x27(v___x_2398_);
return v___x_2399_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13));
v___x_2406_ = l_String_toRawSubstring_x27(v___x_2405_);
return v___x_2406_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18));
v___x_2412_ = l_String_toRawSubstring_x27(v___x_2411_);
return v___x_2412_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31(void){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Array_mkArray0(lean_box(0));
return v___x_2440_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41(void){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40));
v___x_2467_ = l_String_toRawSubstring_x27(v___x_2466_);
return v___x_2467_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57));
v___x_2503_ = l_String_toRawSubstring_x27(v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object* v_id_2525_, lean_object* v_s_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v_msg_2626_; lean_object* v_quotContext_2627_; lean_object* v_currMacroScope_2628_; lean_object* v_ref_2629_; lean_object* v___y_2630_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
lean_inc(v_s_2526_);
v___x_2676_ = l_Lean_Syntax_getKind(v_s_2526_);
v___x_2677_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49));
v___x_2678_ = lean_name_eq(v___x_2676_, v___x_2677_);
lean_dec(v___x_2676_);
if (v___x_2678_ == 0)
{
lean_object* v_quotContext_2679_; lean_object* v_currMacroScope_2680_; lean_object* v_ref_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v_quotContext_2679_ = lean_ctor_get(v_a_2527_, 1);
v_currMacroScope_2680_ = lean_ctor_get(v_a_2527_, 2);
v_ref_2681_ = lean_ctor_get(v_a_2527_, 5);
v___x_2682_ = l_Lean_SourceInfo_fromRef(v_ref_2681_, v___x_2678_);
v___x_2683_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51));
v___x_2684_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52));
v___x_2685_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
lean_inc_n(v___x_2682_, 8);
v___x_2686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2682_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2688_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2689_ = lean_box(0);
lean_inc_n(v_currMacroScope_2680_, 3);
lean_inc_n(v_quotContext_2679_, 3);
v___x_2690_ = l_Lean_addMacroScope(v_quotContext_2679_, v___x_2689_, v_currMacroScope_2680_);
v___x_2691_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55));
v___x_2692_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2682_);
lean_ctor_set(v___x_2692_, 1, v___x_2688_);
lean_ctor_set(v___x_2692_, 2, v___x_2690_);
lean_ctor_set(v___x_2692_, 3, v___x_2691_);
v___x_2693_ = l_Lean_Syntax_node1(v___x_2682_, v___x_2687_, v___x_2692_);
v___x_2694_ = l_Lean_Syntax_node2(v___x_2682_, v___x_2684_, v___x_2686_, v___x_2693_);
v___x_2695_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56));
v___x_2696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2682_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2698_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58);
v___x_2699_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59));
v___x_2700_ = l_Lean_addMacroScope(v_quotContext_2679_, v___x_2699_, v_currMacroScope_2680_);
v___x_2701_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64));
v___x_2702_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2682_);
lean_ctor_set(v___x_2702_, 1, v___x_2698_);
lean_ctor_set(v___x_2702_, 2, v___x_2700_);
lean_ctor_set(v___x_2702_, 3, v___x_2701_);
v___x_2703_ = l_Lean_Syntax_node1(v___x_2682_, v___x_2697_, v___x_2702_);
v___x_2704_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2705_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2682_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = l_Lean_Syntax_node5(v___x_2682_, v___x_2683_, v___x_2694_, v_s_2526_, v___x_2696_, v___x_2703_, v___x_2705_);
v_msg_2626_ = v___x_2706_;
v_quotContext_2627_ = v_quotContext_2679_;
v_currMacroScope_2628_ = v_currMacroScope_2680_;
v_ref_2629_ = v_ref_2681_;
v___y_2630_ = v_a_2528_;
goto v___jp_2625_;
}
else
{
lean_object* v_quotContext_2707_; lean_object* v_currMacroScope_2708_; lean_object* v_ref_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_quotContext_2707_ = lean_ctor_get(v_a_2527_, 1);
v_currMacroScope_2708_ = lean_ctor_get(v_a_2527_, 2);
v_ref_2709_ = lean_ctor_get(v_a_2527_, 5);
v___x_2710_ = 0;
v___x_2711_ = l_Lean_SourceInfo_fromRef(v_ref_2709_, v___x_2710_);
v___x_2712_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66));
v___x_2713_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67));
lean_inc(v___x_2711_);
v___x_2714_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2711_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
v___x_2715_ = l_Lean_Syntax_node2(v___x_2711_, v___x_2712_, v___x_2714_, v_s_2526_);
lean_inc(v_currMacroScope_2708_);
lean_inc(v_quotContext_2707_);
v_msg_2626_ = v___x_2715_;
v_quotContext_2627_ = v_quotContext_2707_;
v_currMacroScope_2628_ = v_currMacroScope_2708_;
v_ref_2629_ = v_ref_2709_;
v___y_2630_ = v_a_2528_;
goto v___jp_2625_;
}
v___jp_2529_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_inc_n(v___y_2545_, 8);
lean_inc(v___y_2540_);
lean_inc_n(v___y_2537_, 30);
v___x_2554_ = l_Lean_Syntax_node5(v___y_2537_, v___y_2540_, v___y_2548_, v___y_2545_, v___y_2545_, v___y_2538_, v___y_2553_);
lean_inc(v___y_2543_);
v___x_2555_ = l_Lean_Syntax_node1(v___y_2537_, v___y_2543_, v___x_2554_);
lean_inc(v___y_2533_);
v___x_2556_ = l_Lean_Syntax_node4(v___y_2537_, v___y_2533_, v___y_2531_, v___y_2545_, v___y_2552_, v___x_2555_);
lean_inc_n(v___y_2550_, 3);
v___x_2557_ = l_Lean_Syntax_node2(v___y_2537_, v___y_2550_, v___x_2556_, v___y_2545_);
v___x_2558_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0));
lean_inc_ref_n(v___y_2546_, 7);
lean_inc_ref_n(v___y_2535_, 7);
lean_inc_ref_n(v___y_2549_, 10);
v___x_2559_ = l_Lean_Name_mkStr4(v___y_2549_, v___y_2535_, v___y_2546_, v___x_2558_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1));
v___x_2561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___y_2537_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2));
v___x_2563_ = l_Lean_Name_mkStr4(v___y_2549_, v___y_2535_, v___y_2546_, v___x_2562_);
v___x_2564_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3));
v___x_2565_ = l_Lean_Name_mkStr4(v___y_2549_, v___y_2535_, v___y_2546_, v___x_2564_);
v___x_2566_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4));
v___x_2567_ = l_Lean_Name_mkStr4(v___y_2549_, v___y_2535_, v___y_2546_, v___x_2566_);
v___x_2568_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
v___x_2569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___y_2537_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2571_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2572_ = lean_box(0);
lean_inc_n(v___y_2551_, 2);
lean_inc_n(v___y_2539_, 2);
v___x_2573_ = l_Lean_addMacroScope(v___y_2539_, v___x_2572_, v___y_2551_);
v___x_2574_ = l_Lean_Name_mkStr1(v___y_2549_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_inc_n(v___y_2532_, 2);
v___x_2576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v___y_2532_);
v___x_2577_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2577_, 0, v___y_2537_);
lean_ctor_set(v___x_2577_, 1, v___x_2571_);
lean_ctor_set(v___x_2577_, 2, v___x_2573_);
lean_ctor_set(v___x_2577_, 3, v___x_2576_);
v___x_2578_ = l_Lean_Syntax_node1(v___y_2537_, v___x_2570_, v___x_2577_);
v___x_2579_ = l_Lean_Syntax_node2(v___y_2537_, v___x_2567_, v___x_2569_, v___x_2578_);
v___x_2580_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9));
v___x_2581_ = l_Lean_Name_mkStr4(v___y_2549_, v___y_2535_, v___y_2546_, v___x_2580_);
v___x_2582_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10));
v___x_2583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___y_2537_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11));
v___x_2585_ = l_Lean_Name_mkStr4(v___y_2549_, v___y_2535_, v___y_2546_, v___x_2584_);
v___x_2586_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12));
v___x_2587_ = l_Lean_Name_mkStr4(v___y_2549_, v___y_2535_, v___y_2546_, v___x_2586_);
v___x_2588_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14);
v___x_2589_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2590_ = l_Lean_Name_mkStr2(v___y_2549_, v___x_2589_);
lean_inc(v___x_2590_);
v___x_2591_ = l_Lean_addMacroScope(v___y_2539_, v___x_2590_, v___y_2551_);
v___x_2592_ = lean_box(0);
v___x_2593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2590_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v___y_2532_);
v___x_2595_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2595_, 0, v___y_2537_);
lean_ctor_set(v___x_2595_, 1, v___x_2588_);
lean_ctor_set(v___x_2595_, 2, v___x_2591_);
lean_ctor_set(v___x_2595_, 3, v___x_2594_);
lean_inc(v___y_2544_);
lean_inc_n(v___y_2530_, 4);
v___x_2596_ = l_Lean_Syntax_node1(v___y_2537_, v___y_2530_, v___y_2544_);
lean_inc(v___x_2587_);
v___x_2597_ = l_Lean_Syntax_node2(v___y_2537_, v___x_2587_, v___x_2595_, v___x_2596_);
lean_inc(v___x_2585_);
v___x_2598_ = l_Lean_Syntax_node1(v___y_2537_, v___x_2585_, v___x_2597_);
v___x_2599_ = l_Lean_Syntax_node2(v___y_2537_, v___x_2581_, v___x_2583_, v___x_2598_);
v___x_2600_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___y_2537_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = l_Lean_Syntax_node3(v___y_2537_, v___x_2565_, v___x_2579_, v___x_2599_, v___x_2601_);
v___x_2603_ = l_Lean_Syntax_node2(v___y_2537_, v___x_2563_, v___y_2545_, v___x_2602_);
v___x_2604_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17));
v___x_2605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___y_2537_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19);
v___x_2607_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20));
v___x_2608_ = l_Lean_Name_mkStr2(v___y_2549_, v___x_2607_);
lean_inc(v___x_2608_);
v___x_2609_ = l_Lean_addMacroScope(v___y_2539_, v___x_2608_, v___y_2551_);
v___x_2610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2592_);
v___x_2611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___y_2532_);
v___x_2612_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2612_, 0, v___y_2537_);
lean_ctor_set(v___x_2612_, 1, v___x_2606_);
lean_ctor_set(v___x_2612_, 2, v___x_2609_);
lean_ctor_set(v___x_2612_, 3, v___x_2611_);
v___x_2613_ = l_Lean_Syntax_node2(v___y_2537_, v___y_2530_, v___y_2544_, v___y_2534_);
v___x_2614_ = l_Lean_Syntax_node2(v___y_2537_, v___x_2587_, v___x_2612_, v___x_2613_);
v___x_2615_ = l_Lean_Syntax_node1(v___y_2537_, v___x_2585_, v___x_2614_);
v___x_2616_ = l_Lean_Syntax_node2(v___y_2537_, v___y_2550_, v___x_2615_, v___y_2545_);
v___x_2617_ = l_Lean_Syntax_node1(v___y_2537_, v___y_2530_, v___x_2616_);
lean_inc_n(v___y_2536_, 2);
v___x_2618_ = l_Lean_Syntax_node1(v___y_2537_, v___y_2536_, v___x_2617_);
v___x_2619_ = l_Lean_Syntax_node6(v___y_2537_, v___x_2559_, v___x_2561_, v___x_2603_, v___x_2605_, v___x_2618_, v___y_2545_, v___y_2545_);
v___x_2620_ = l_Lean_Syntax_node2(v___y_2537_, v___y_2550_, v___x_2619_, v___y_2545_);
v___x_2621_ = l_Lean_Syntax_node2(v___y_2537_, v___y_2530_, v___x_2557_, v___x_2620_);
v___x_2622_ = l_Lean_Syntax_node1(v___y_2537_, v___y_2536_, v___x_2621_);
lean_inc(v___y_2547_);
v___x_2623_ = l_Lean_Syntax_node2(v___y_2537_, v___y_2547_, v___y_2542_, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___y_2541_);
return v___x_2624_;
}
v___jp_2625_:
{
uint8_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2631_ = 0;
v___x_2632_ = l_Lean_SourceInfo_fromRef(v_ref_2629_, v___x_2631_);
v___x_2633_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0));
v___x_2634_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1));
v___x_2635_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__0));
v___x_2636_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22));
v___x_2637_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23));
lean_inc_n(v___x_2632_, 7);
v___x_2638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2632_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25));
v___x_2640_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2641_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27));
v___x_2642_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2643_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
v___x_2644_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2632_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31);
v___x_2646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2632_);
lean_ctor_set(v___x_2646_, 1, v___x_2640_);
lean_ctor_set(v___x_2646_, 2, v___x_2645_);
v___x_2647_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33));
lean_inc_ref(v___x_2646_);
v___x_2648_ = l_Lean_Syntax_node1(v___x_2632_, v___x_2647_, v___x_2646_);
v___x_2649_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35));
v___x_2650_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37));
v___x_2651_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39));
v___x_2652_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41);
v___x_2653_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42));
lean_inc(v_currMacroScope_2628_);
lean_inc(v_quotContext_2627_);
v___x_2654_ = l_Lean_addMacroScope(v_quotContext_2627_, v___x_2653_, v_currMacroScope_2628_);
v___x_2655_ = lean_box(0);
v___x_2656_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2632_);
lean_ctor_set(v___x_2656_, 1, v___x_2652_);
lean_ctor_set(v___x_2656_, 2, v___x_2654_);
lean_ctor_set(v___x_2656_, 3, v___x_2655_);
lean_inc_ref(v___x_2656_);
v___x_2657_ = l_Lean_Syntax_node1(v___x_2632_, v___x_2651_, v___x_2656_);
v___x_2658_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43));
v___x_2659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2632_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = l_Lean_Syntax_getId(v_id_2525_);
v___x_2661_ = l_Lean_Name_eraseMacroScopes(v___x_2660_);
lean_dec(v___x_2660_);
lean_inc(v___x_2661_);
v___x_2662_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2655_, v___x_2661_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_quoteNameMk(v___x_2661_);
v___y_2530_ = v___x_2640_;
v___y_2531_ = v___x_2644_;
v___y_2532_ = v___x_2655_;
v___y_2533_ = v___x_2642_;
v___y_2534_ = v_msg_2626_;
v___y_2535_ = v___x_2634_;
v___y_2536_ = v___x_2639_;
v___y_2537_ = v___x_2632_;
v___y_2538_ = v___x_2659_;
v___y_2539_ = v_quotContext_2627_;
v___y_2540_ = v___x_2650_;
v___y_2541_ = v___y_2630_;
v___y_2542_ = v___x_2638_;
v___y_2543_ = v___x_2649_;
v___y_2544_ = v___x_2656_;
v___y_2545_ = v___x_2646_;
v___y_2546_ = v___x_2635_;
v___y_2547_ = v___x_2636_;
v___y_2548_ = v___x_2657_;
v___y_2549_ = v___x_2633_;
v___y_2550_ = v___x_2641_;
v___y_2551_ = v_currMacroScope_2628_;
v___y_2552_ = v___x_2648_;
v___y_2553_ = v___x_2663_;
goto v___jp_2529_;
}
else
{
lean_object* v_val_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_dec(v___x_2661_);
v_val_2664_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_val_2664_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2665_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45));
v___x_2666_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46));
v___x_2667_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47));
v___x_2668_ = lean_string_intercalate(v___x_2667_, v_val_2664_);
v___x_2669_ = lean_string_append(v___x_2666_, v___x_2668_);
lean_dec_ref(v___x_2668_);
v___x_2670_ = lean_box(2);
v___x_2671_ = l_Lean_Syntax_mkNameLit(v___x_2669_, v___x_2670_);
v___x_2672_ = lean_unsigned_to_nat(1u);
v___x_2673_ = lean_mk_empty_array_with_capacity(v___x_2672_);
v___x_2674_ = lean_array_push(v___x_2673_, v___x_2671_);
v___x_2675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2670_);
lean_ctor_set(v___x_2675_, 1, v___x_2665_);
lean_ctor_set(v___x_2675_, 2, v___x_2674_);
v___y_2530_ = v___x_2640_;
v___y_2531_ = v___x_2644_;
v___y_2532_ = v___x_2655_;
v___y_2533_ = v___x_2642_;
v___y_2534_ = v_msg_2626_;
v___y_2535_ = v___x_2634_;
v___y_2536_ = v___x_2639_;
v___y_2537_ = v___x_2632_;
v___y_2538_ = v___x_2659_;
v___y_2539_ = v_quotContext_2627_;
v___y_2540_ = v___x_2650_;
v___y_2541_ = v___y_2630_;
v___y_2542_ = v___x_2638_;
v___y_2543_ = v___x_2649_;
v___y_2544_ = v___x_2656_;
v___y_2545_ = v___x_2646_;
v___y_2546_ = v___x_2635_;
v___y_2547_ = v___x_2636_;
v___y_2548_ = v___x_2657_;
v___y_2549_ = v___x_2633_;
v___y_2550_ = v___x_2641_;
v___y_2551_ = v_currMacroScope_2628_;
v___y_2552_ = v___x_2648_;
v___y_2553_ = v___x_2675_;
goto v___jp_2529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object* v_id_2716_, lean_object* v_s_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v_id_2716_, v_s_2717_, v_a_2718_, v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_id_2716_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object* v_x_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2778_ = ((lean_object*)(l_Lean_doElemTrace_x5b___x5d_____00__closed__1));
lean_inc(v_x_2775_);
v___x_2779_ = l_Lean_Syntax_isOfKind(v_x_2775_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
lean_dec(v_x_2775_);
v___x_2780_ = lean_box(1);
v___x_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
lean_ctor_set(v___x_2781_, 1, v_a_2777_);
return v___x_2781_;
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v_a_2787_; lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v___x_2782_ = lean_unsigned_to_nat(1u);
v___x_2783_ = l_Lean_Syntax_getArg(v_x_2775_, v___x_2782_);
v___x_2784_ = lean_unsigned_to_nat(3u);
v___x_2785_ = l_Lean_Syntax_getArg(v_x_2775_, v___x_2784_);
lean_dec(v_x_2775_);
v___x_2786_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v___x_2783_, v___x_2785_, v_a_2776_, v_a_2777_);
lean_dec(v___x_2783_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
v_a_2788_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2786_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_inc(v_a_2787_);
lean_dec(v___x_2786_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2787_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object* v_x_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(v_x_2796_, v_a_2797_, v_a_2798_);
lean_dec_ref(v_a_2797_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object* v_inst_2800_, lean_object* v_inst_2801_, lean_object* v_inst_2802_, lean_object* v_inst_2803_, lean_object* v_always_2804_, lean_object* v_inst_2805_, lean_object* v_cls_2806_, uint8_t v_collapsed_2807_, lean_object* v_tag_2808_, lean_object* v_opts_2809_, uint8_t v_clsEnabled_2810_, lean_object* v_oldTraces_2811_, lean_object* v_ref_2812_, lean_object* v_msg_2813_, lean_object* v_resStartStop_2814_){
_start:
{
lean_object* v___x_2815_; lean_object* v_snd_2816_; lean_object* v_fst_2817_; lean_object* v_fst_2818_; lean_object* v_snd_2819_; lean_object* v___f_2820_; lean_object* v___f_2821_; lean_object* v_data_2823_; lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___y_2839_; double v___y_2845_; uint8_t v___x_2850_; 
v___x_2815_ = l_Lean_KVMap_instValueBool;
v_snd_2816_ = lean_ctor_get(v_resStartStop_2814_, 1);
lean_inc(v_snd_2816_);
v_fst_2817_ = lean_ctor_get(v_resStartStop_2814_, 0);
lean_inc_n(v_fst_2817_, 2);
lean_dec_ref(v_resStartStop_2814_);
v_fst_2818_ = lean_ctor_get(v_snd_2816_, 0);
lean_inc(v_fst_2818_);
v_snd_2819_ = lean_ctor_get(v_snd_2816_, 1);
lean_inc(v_snd_2819_);
lean_dec(v_snd_2816_);
lean_inc_ref(v_oldTraces_2811_);
v___f_2820_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2820_, 0, v_oldTraces_2811_);
lean_inc_ref(v_inst_2800_);
v___f_2821_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2821_, 0, v_always_2804_);
lean_closure_set(v___f_2821_, 1, v_inst_2800_);
lean_closure_set(v___f_2821_, 2, v_fst_2817_);
v___x_2827_ = l_Lean_trace_profiler;
v___x_2828_ = l_Lean_Option_get___redArg(v___x_2815_, v_opts_2809_, v___x_2827_);
v___x_2850_ = lean_unbox(v___x_2828_);
if (v___x_2850_ == 0)
{
uint8_t v___x_2851_; 
v___x_2851_ = lean_unbox(v___x_2828_);
v___y_2839_ = v___x_2851_;
goto v___jp_2838_;
}
else
{
lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v___x_2852_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2853_ = l_Lean_Option_get___redArg(v___x_2815_, v_opts_2809_, v___x_2852_);
v___x_2854_ = lean_unbox(v___x_2853_);
lean_dec(v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; double v___x_2858_; double v___x_2859_; double v___x_2860_; 
v___x_2855_ = l_Lean_KVMap_instValueNat;
v___x_2856_ = l_Lean_trace_profiler_threshold;
v___x_2857_ = l_Lean_Option_get___redArg(v___x_2855_, v_opts_2809_, v___x_2856_);
v___x_2858_ = lean_float_of_nat(v___x_2857_);
v___x_2859_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_2860_ = lean_float_div(v___x_2858_, v___x_2859_);
v___y_2845_ = v___x_2860_;
goto v___jp_2844_;
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; double v___x_2864_; 
v___x_2861_ = l_Lean_KVMap_instValueNat;
v___x_2862_ = l_Lean_trace_profiler_threshold;
v___x_2863_ = l_Lean_Option_get___redArg(v___x_2861_, v_opts_2809_, v___x_2862_);
v___x_2864_ = lean_float_of_nat(v___x_2863_);
v___y_2845_ = v___x_2864_;
goto v___jp_2844_;
}
}
v___jp_2822_:
{
lean_object* v_toBind_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_toBind_2824_ = lean_ctor_get(v_inst_2800_, 1);
lean_inc(v_toBind_2824_);
v___x_2825_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_2800_, v_inst_2801_, v_inst_2802_, v_inst_2803_, v_oldTraces_2811_, v_data_2823_, v_ref_2812_, v_msg_2813_);
v___x_2826_ = lean_apply_4(v_toBind_2824_, lean_box(0), lean_box(0), v___x_2825_, v___f_2821_);
return v___x_2826_;
}
v___jp_2829_:
{
lean_object* v_result_2830_; lean_object* v___x_2831_; double v___x_2832_; lean_object* v_data_2833_; uint8_t v___x_2834_; 
v_result_2830_ = lean_apply_1(v_inst_2805_, v_fst_2817_);
v___x_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2831_, 0, v_result_2830_);
v___x_2832_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_2808_);
lean_inc_ref(v___x_2831_);
lean_inc(v_cls_2806_);
v_data_2833_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2833_, 0, v_cls_2806_);
lean_ctor_set(v_data_2833_, 1, v___x_2831_);
lean_ctor_set(v_data_2833_, 2, v_tag_2808_);
lean_ctor_set_float(v_data_2833_, sizeof(void*)*3, v___x_2832_);
lean_ctor_set_float(v_data_2833_, sizeof(void*)*3 + 8, v___x_2832_);
lean_ctor_set_uint8(v_data_2833_, sizeof(void*)*3 + 16, v_collapsed_2807_);
v___x_2834_ = lean_unbox(v___x_2828_);
lean_dec(v___x_2828_);
if (v___x_2834_ == 0)
{
lean_dec_ref_known(v___x_2831_, 1);
lean_dec(v_snd_2819_);
lean_dec(v_fst_2818_);
lean_dec_ref(v_tag_2808_);
lean_dec(v_cls_2806_);
v_data_2823_ = v_data_2833_;
goto v___jp_2822_;
}
else
{
lean_object* v_data_2835_; double v___x_2836_; double v___x_2837_; 
lean_dec_ref_known(v_data_2833_, 3);
v_data_2835_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2835_, 0, v_cls_2806_);
lean_ctor_set(v_data_2835_, 1, v___x_2831_);
lean_ctor_set(v_data_2835_, 2, v_tag_2808_);
v___x_2836_ = lean_unbox_float(v_fst_2818_);
lean_dec(v_fst_2818_);
lean_ctor_set_float(v_data_2835_, sizeof(void*)*3, v___x_2836_);
v___x_2837_ = lean_unbox_float(v_snd_2819_);
lean_dec(v_snd_2819_);
lean_ctor_set_float(v_data_2835_, sizeof(void*)*3 + 8, v___x_2837_);
lean_ctor_set_uint8(v_data_2835_, sizeof(void*)*3 + 16, v_collapsed_2807_);
v_data_2823_ = v_data_2835_;
goto v___jp_2822_;
}
}
v___jp_2838_:
{
if (v_clsEnabled_2810_ == 0)
{
if (v___y_2839_ == 0)
{
lean_object* v_toBind_2840_; lean_object* v_modifyTraceState_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_dec(v___x_2828_);
lean_dec(v_snd_2819_);
lean_dec(v_fst_2818_);
lean_dec(v_fst_2817_);
lean_dec_ref(v_msg_2813_);
lean_dec(v_ref_2812_);
lean_dec_ref(v_oldTraces_2811_);
lean_dec_ref(v_tag_2808_);
lean_dec(v_cls_2806_);
lean_dec_ref(v_inst_2805_);
lean_dec(v_inst_2803_);
lean_dec_ref(v_inst_2802_);
v_toBind_2840_ = lean_ctor_get(v_inst_2800_, 1);
lean_inc(v_toBind_2840_);
lean_dec_ref(v_inst_2800_);
v_modifyTraceState_2841_ = lean_ctor_get(v_inst_2801_, 0);
lean_inc(v_modifyTraceState_2841_);
lean_dec_ref(v_inst_2801_);
v___x_2842_ = lean_apply_1(v_modifyTraceState_2841_, v___f_2820_);
v___x_2843_ = lean_apply_4(v_toBind_2840_, lean_box(0), lean_box(0), v___x_2842_, v___f_2821_);
return v___x_2843_;
}
else
{
lean_dec_ref(v___f_2820_);
goto v___jp_2829_;
}
}
else
{
lean_dec_ref(v___f_2820_);
goto v___jp_2829_;
}
}
v___jp_2844_:
{
double v___x_2846_; double v___x_2847_; double v___x_2848_; uint8_t v___x_2849_; 
v___x_2846_ = lean_unbox_float(v_snd_2819_);
v___x_2847_ = lean_unbox_float(v_fst_2818_);
v___x_2848_ = lean_float_sub(v___x_2846_, v___x_2847_);
v___x_2849_ = lean_float_decLt(v___y_2845_, v___x_2848_);
v___y_2839_ = v___x_2849_;
goto v___jp_2838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object* v_inst_2865_, lean_object* v_inst_2866_, lean_object* v_inst_2867_, lean_object* v_inst_2868_, lean_object* v_always_2869_, lean_object* v_inst_2870_, lean_object* v_cls_2871_, lean_object* v_collapsed_2872_, lean_object* v_tag_2873_, lean_object* v_opts_2874_, lean_object* v_clsEnabled_2875_, lean_object* v_oldTraces_2876_, lean_object* v_ref_2877_, lean_object* v_msg_2878_, lean_object* v_resStartStop_2879_){
_start:
{
uint8_t v_collapsed_boxed_2880_; uint8_t v_clsEnabled_boxed_2881_; lean_object* v_res_2882_; 
v_collapsed_boxed_2880_ = lean_unbox(v_collapsed_2872_);
v_clsEnabled_boxed_2881_ = lean_unbox(v_clsEnabled_2875_);
v_res_2882_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2865_, v_inst_2866_, v_inst_2867_, v_inst_2868_, v_always_2869_, v_inst_2870_, v_cls_2871_, v_collapsed_boxed_2880_, v_tag_2873_, v_opts_2874_, v_clsEnabled_boxed_2881_, v_oldTraces_2876_, v_ref_2877_, v_msg_2878_, v_resStartStop_2879_);
lean_dec_ref(v_opts_2874_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object* v_00_u03b1_2883_, lean_object* v_m_2884_, lean_object* v_inst_2885_, lean_object* v_inst_2886_, lean_object* v_00_u03b5_2887_, lean_object* v_inst_2888_, lean_object* v_inst_2889_, lean_object* v_always_2890_, lean_object* v_inst_2891_, lean_object* v_cls_2892_, uint8_t v_collapsed_2893_, lean_object* v_tag_2894_, lean_object* v_opts_2895_, uint8_t v_clsEnabled_2896_, lean_object* v_oldTraces_2897_, lean_object* v_ref_2898_, lean_object* v_msg_2899_, lean_object* v_resStartStop_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2885_, v_inst_2886_, v_inst_2888_, v_inst_2889_, v_always_2890_, v_inst_2891_, v_cls_2892_, v_collapsed_2893_, v_tag_2894_, v_opts_2895_, v_clsEnabled_2896_, v_oldTraces_2897_, v_ref_2898_, v_msg_2899_, v_resStartStop_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_2902_ = _args[0];
lean_object* v_m_2903_ = _args[1];
lean_object* v_inst_2904_ = _args[2];
lean_object* v_inst_2905_ = _args[3];
lean_object* v_00_u03b5_2906_ = _args[4];
lean_object* v_inst_2907_ = _args[5];
lean_object* v_inst_2908_ = _args[6];
lean_object* v_always_2909_ = _args[7];
lean_object* v_inst_2910_ = _args[8];
lean_object* v_cls_2911_ = _args[9];
lean_object* v_collapsed_2912_ = _args[10];
lean_object* v_tag_2913_ = _args[11];
lean_object* v_opts_2914_ = _args[12];
lean_object* v_clsEnabled_2915_ = _args[13];
lean_object* v_oldTraces_2916_ = _args[14];
lean_object* v_ref_2917_ = _args[15];
lean_object* v_msg_2918_ = _args[16];
lean_object* v_resStartStop_2919_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2920_; uint8_t v_clsEnabled_boxed_2921_; lean_object* v_res_2922_; 
v_collapsed_boxed_2920_ = lean_unbox(v_collapsed_2912_);
v_clsEnabled_boxed_2921_ = lean_unbox(v_clsEnabled_2915_);
v_res_2922_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(v_00_u03b1_2902_, v_m_2903_, v_inst_2904_, v_inst_2905_, v_00_u03b5_2906_, v_inst_2907_, v_inst_2908_, v_always_2909_, v_inst_2910_, v_cls_2911_, v_collapsed_boxed_2920_, v_tag_2913_, v_opts_2914_, v_clsEnabled_boxed_2921_, v_oldTraces_2916_, v_ref_2917_, v_msg_2918_, v_resStartStop_2919_);
lean_dec_ref(v_opts_2914_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object* v_inst_2923_, lean_object* v_____do__lift_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_apply_1(v_inst_2923_, v_____do__lift_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object* v_inst_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_always_2930_, lean_object* v_inst_2931_, lean_object* v_cls_2932_, uint8_t v_collapsed_2933_, lean_object* v_tag_2934_, lean_object* v_opts_2935_, uint8_t v_clsEnabled_2936_, lean_object* v_oldTraces_2937_, lean_object* v_ref_2938_, lean_object* v_msg_2939_, lean_object* v_resStartStop_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2926_, v_inst_2927_, v_inst_2928_, v_inst_2929_, v_always_2930_, v_inst_2931_, v_cls_2932_, v_collapsed_2933_, v_tag_2934_, v_opts_2935_, v_clsEnabled_2936_, v_oldTraces_2937_, v_ref_2938_, v_msg_2939_, v_resStartStop_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_inst_2944_, lean_object* v_inst_2945_, lean_object* v_always_2946_, lean_object* v_inst_2947_, lean_object* v_cls_2948_, lean_object* v_collapsed_2949_, lean_object* v_tag_2950_, lean_object* v_opts_2951_, lean_object* v_clsEnabled_2952_, lean_object* v_oldTraces_2953_, lean_object* v_ref_2954_, lean_object* v_msg_2955_, lean_object* v_resStartStop_2956_){
_start:
{
uint8_t v_collapsed_boxed_2957_; uint8_t v_clsEnabled_boxed_2958_; lean_object* v_res_2959_; 
v_collapsed_boxed_2957_ = lean_unbox(v_collapsed_2949_);
v_clsEnabled_boxed_2958_ = lean_unbox(v_clsEnabled_2952_);
v_res_2959_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_2942_, v_inst_2943_, v_inst_2944_, v_inst_2945_, v_always_2946_, v_inst_2947_, v_cls_2948_, v_collapsed_boxed_2957_, v_tag_2950_, v_opts_2951_, v_clsEnabled_boxed_2958_, v_oldTraces_2953_, v_ref_2954_, v_msg_2955_, v_resStartStop_2956_);
lean_dec_ref(v_opts_2951_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object* v_always_2960_, lean_object* v_inst_2961_, lean_object* v_inst_2962_, lean_object* v_inst_2963_, lean_object* v_inst_2964_, lean_object* v_inst_2965_, lean_object* v_cls_2966_, uint8_t v_collapsed_2967_, lean_object* v_tag_2968_, lean_object* v_opts_2969_, uint8_t v_clsEnabled_2970_, lean_object* v_oldTraces_2971_, lean_object* v_ref_2972_, lean_object* v_toPure_2973_, lean_object* v_toBind_2974_, lean_object* v_k_2975_, lean_object* v_inst_2976_, lean_object* v_msg_2977_){
_start:
{
lean_object* v_tryCatch_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___f_2981_; lean_object* v___f_2982_; lean_object* v___f_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
v_tryCatch_2978_ = lean_ctor_get(v_always_2960_, 1);
lean_inc(v_tryCatch_2978_);
v___x_2979_ = lean_box(v_collapsed_2967_);
v___x_2980_ = lean_box(v_clsEnabled_2970_);
lean_inc_ref(v_opts_2969_);
v___f_2981_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__1___boxed), 15, 14);
lean_closure_set(v___f_2981_, 0, v_inst_2961_);
lean_closure_set(v___f_2981_, 1, v_inst_2962_);
lean_closure_set(v___f_2981_, 2, v_inst_2963_);
lean_closure_set(v___f_2981_, 3, v_inst_2964_);
lean_closure_set(v___f_2981_, 4, v_always_2960_);
lean_closure_set(v___f_2981_, 5, v_inst_2965_);
lean_closure_set(v___f_2981_, 6, v_cls_2966_);
lean_closure_set(v___f_2981_, 7, v___x_2979_);
lean_closure_set(v___f_2981_, 8, v_tag_2968_);
lean_closure_set(v___f_2981_, 9, v_opts_2969_);
lean_closure_set(v___f_2981_, 10, v___x_2980_);
lean_closure_set(v___f_2981_, 11, v_oldTraces_2971_);
lean_closure_set(v___f_2981_, 12, v_ref_2972_);
lean_closure_set(v___f_2981_, 13, v_msg_2977_);
lean_inc_n(v_toPure_2973_, 2);
v___f_2982_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2982_, 0, v_toPure_2973_);
v___f_2983_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2983_, 0, v_toPure_2973_);
lean_inc(v_toBind_2974_);
v___x_2984_ = lean_apply_4(v_toBind_2974_, lean_box(0), lean_box(0), v_k_2975_, v___f_2983_);
v___x_2985_ = lean_apply_3(v_tryCatch_2978_, lean_box(0), v___x_2984_, v___f_2982_);
v___x_2986_ = l_Lean_KVMap_instValueBool;
v___x_2987_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2988_ = l_Lean_Option_get___redArg(v___x_2986_, v_opts_2969_, v___x_2987_);
lean_dec_ref(v_opts_2969_);
v___x_2989_ = lean_unbox(v___x_2988_);
lean_dec(v___x_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___f_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2990_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_2991_ = lean_apply_2(v_inst_2976_, lean_box(0), v___x_2990_);
lean_inc(v___x_2991_);
lean_inc_n(v_toBind_2974_, 2);
v___f_2992_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_2992_, 0, v_toPure_2973_);
lean_closure_set(v___f_2992_, 1, v_toBind_2974_);
lean_closure_set(v___f_2992_, 2, v___x_2991_);
lean_closure_set(v___f_2992_, 3, v___x_2985_);
v___x_2993_ = lean_apply_4(v_toBind_2974_, lean_box(0), lean_box(0), v___x_2991_, v___f_2992_);
v___x_2994_ = lean_apply_4(v_toBind_2974_, lean_box(0), lean_box(0), v___x_2993_, v___f_2981_);
return v___x_2994_;
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___f_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2995_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_2996_ = lean_apply_2(v_inst_2976_, lean_box(0), v___x_2995_);
lean_inc(v___x_2996_);
lean_inc_n(v_toBind_2974_, 2);
v___f_2997_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_2997_, 0, v_toPure_2973_);
lean_closure_set(v___f_2997_, 1, v_toBind_2974_);
lean_closure_set(v___f_2997_, 2, v___x_2996_);
lean_closure_set(v___f_2997_, 3, v___x_2985_);
v___x_2998_ = lean_apply_4(v_toBind_2974_, lean_box(0), lean_box(0), v___x_2996_, v___f_2997_);
v___x_2999_ = lean_apply_4(v_toBind_2974_, lean_box(0), lean_box(0), v___x_2998_, v___f_2981_);
return v___x_2999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_3000_ = _args[0];
lean_object* v_inst_3001_ = _args[1];
lean_object* v_inst_3002_ = _args[2];
lean_object* v_inst_3003_ = _args[3];
lean_object* v_inst_3004_ = _args[4];
lean_object* v_inst_3005_ = _args[5];
lean_object* v_cls_3006_ = _args[6];
lean_object* v_collapsed_3007_ = _args[7];
lean_object* v_tag_3008_ = _args[8];
lean_object* v_opts_3009_ = _args[9];
lean_object* v_clsEnabled_3010_ = _args[10];
lean_object* v_oldTraces_3011_ = _args[11];
lean_object* v_ref_3012_ = _args[12];
lean_object* v_toPure_3013_ = _args[13];
lean_object* v_toBind_3014_ = _args[14];
lean_object* v_k_3015_ = _args[15];
lean_object* v_inst_3016_ = _args[16];
lean_object* v_msg_3017_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3018_; uint8_t v_clsEnabled_boxed_3019_; lean_object* v_res_3020_; 
v_collapsed_boxed_3018_ = lean_unbox(v_collapsed_3007_);
v_clsEnabled_boxed_3019_ = lean_unbox(v_clsEnabled_3010_);
v_res_3020_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_always_3000_, v_inst_3001_, v_inst_3002_, v_inst_3003_, v_inst_3004_, v_inst_3005_, v_cls_3006_, v_collapsed_boxed_3018_, v_tag_3008_, v_opts_3009_, v_clsEnabled_boxed_3019_, v_oldTraces_3011_, v_ref_3012_, v_toPure_3013_, v_toBind_3014_, v_k_3015_, v_inst_3016_, v_msg_3017_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object* v_always_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v_inst_3024_, lean_object* v_inst_3025_, lean_object* v_inst_3026_, lean_object* v_cls_3027_, uint8_t v_collapsed_3028_, lean_object* v_tag_3029_, lean_object* v_opts_3030_, uint8_t v_clsEnabled_3031_, lean_object* v_oldTraces_3032_, lean_object* v_toPure_3033_, lean_object* v_toBind_3034_, lean_object* v_k_3035_, lean_object* v_inst_3036_, lean_object* v_msg_3037_, lean_object* v___f_3038_, lean_object* v_withRef_3039_, lean_object* v_getRef_3040_, lean_object* v_ref_3041_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___f_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___f_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3042_ = lean_box(v_collapsed_3028_);
v___x_3043_ = lean_box(v_clsEnabled_3031_);
lean_inc_n(v_toBind_3034_, 3);
lean_inc(v_ref_3041_);
v___f_3044_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__10___boxed), 18, 17);
lean_closure_set(v___f_3044_, 0, v_always_3021_);
lean_closure_set(v___f_3044_, 1, v_inst_3022_);
lean_closure_set(v___f_3044_, 2, v_inst_3023_);
lean_closure_set(v___f_3044_, 3, v_inst_3024_);
lean_closure_set(v___f_3044_, 4, v_inst_3025_);
lean_closure_set(v___f_3044_, 5, v_inst_3026_);
lean_closure_set(v___f_3044_, 6, v_cls_3027_);
lean_closure_set(v___f_3044_, 7, v___x_3042_);
lean_closure_set(v___f_3044_, 8, v_tag_3029_);
lean_closure_set(v___f_3044_, 9, v_opts_3030_);
lean_closure_set(v___f_3044_, 10, v___x_3043_);
lean_closure_set(v___f_3044_, 11, v_oldTraces_3032_);
lean_closure_set(v___f_3044_, 12, v_ref_3041_);
lean_closure_set(v___f_3044_, 13, v_toPure_3033_);
lean_closure_set(v___f_3044_, 14, v_toBind_3034_);
lean_closure_set(v___f_3044_, 15, v_k_3035_);
lean_closure_set(v___f_3044_, 16, v_inst_3036_);
v___x_3045_ = lean_box(0);
v___x_3046_ = lean_apply_1(v_msg_3037_, v___x_3045_);
v___x_3047_ = lean_apply_4(v_toBind_3034_, lean_box(0), lean_box(0), v___x_3046_, v___f_3038_);
v___f_3048_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3048_, 0, v_ref_3041_);
lean_closure_set(v___f_3048_, 1, v_withRef_3039_);
lean_closure_set(v___f_3048_, 2, v___x_3047_);
v___x_3049_ = lean_apply_4(v_toBind_3034_, lean_box(0), lean_box(0), v_getRef_3040_, v___f_3048_);
v___x_3050_ = lean_apply_4(v_toBind_3034_, lean_box(0), lean_box(0), v___x_3049_, v___f_3044_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_3051_ = _args[0];
lean_object* v_inst_3052_ = _args[1];
lean_object* v_inst_3053_ = _args[2];
lean_object* v_inst_3054_ = _args[3];
lean_object* v_inst_3055_ = _args[4];
lean_object* v_inst_3056_ = _args[5];
lean_object* v_cls_3057_ = _args[6];
lean_object* v_collapsed_3058_ = _args[7];
lean_object* v_tag_3059_ = _args[8];
lean_object* v_opts_3060_ = _args[9];
lean_object* v_clsEnabled_3061_ = _args[10];
lean_object* v_oldTraces_3062_ = _args[11];
lean_object* v_toPure_3063_ = _args[12];
lean_object* v_toBind_3064_ = _args[13];
lean_object* v_k_3065_ = _args[14];
lean_object* v_inst_3066_ = _args[15];
lean_object* v_msg_3067_ = _args[16];
lean_object* v___f_3068_ = _args[17];
lean_object* v_withRef_3069_ = _args[18];
lean_object* v_getRef_3070_ = _args[19];
lean_object* v_ref_3071_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_3072_; uint8_t v_clsEnabled_boxed_3073_; lean_object* v_res_3074_; 
v_collapsed_boxed_3072_ = lean_unbox(v_collapsed_3058_);
v_clsEnabled_boxed_3073_ = lean_unbox(v_clsEnabled_3061_);
v_res_3074_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_always_3051_, v_inst_3052_, v_inst_3053_, v_inst_3054_, v_inst_3055_, v_inst_3056_, v_cls_3057_, v_collapsed_boxed_3072_, v_tag_3059_, v_opts_3060_, v_clsEnabled_boxed_3073_, v_oldTraces_3062_, v_toPure_3063_, v_toBind_3064_, v_k_3065_, v_inst_3066_, v_msg_3067_, v___f_3068_, v_withRef_3069_, v_getRef_3070_, v_ref_3071_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object* v_inst_3075_, lean_object* v_always_3076_, lean_object* v_inst_3077_, lean_object* v_inst_3078_, lean_object* v_inst_3079_, lean_object* v_inst_3080_, lean_object* v_cls_3081_, uint8_t v_collapsed_3082_, lean_object* v_tag_3083_, lean_object* v_opts_3084_, uint8_t v_clsEnabled_3085_, lean_object* v_toPure_3086_, lean_object* v_toBind_3087_, lean_object* v_k_3088_, lean_object* v_inst_3089_, lean_object* v_msg_3090_, lean_object* v___f_3091_, lean_object* v_oldTraces_3092_){
_start:
{
lean_object* v_getRef_3093_; lean_object* v_withRef_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; 
v_getRef_3093_ = lean_ctor_get(v_inst_3075_, 0);
lean_inc_n(v_getRef_3093_, 2);
v_withRef_3094_ = lean_ctor_get(v_inst_3075_, 1);
lean_inc(v_withRef_3094_);
v___x_3095_ = lean_box(v_collapsed_3082_);
v___x_3096_ = lean_box(v_clsEnabled_3085_);
lean_inc(v_toBind_3087_);
v___f_3097_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__3___boxed), 21, 20);
lean_closure_set(v___f_3097_, 0, v_always_3076_);
lean_closure_set(v___f_3097_, 1, v_inst_3077_);
lean_closure_set(v___f_3097_, 2, v_inst_3078_);
lean_closure_set(v___f_3097_, 3, v_inst_3075_);
lean_closure_set(v___f_3097_, 4, v_inst_3079_);
lean_closure_set(v___f_3097_, 5, v_inst_3080_);
lean_closure_set(v___f_3097_, 6, v_cls_3081_);
lean_closure_set(v___f_3097_, 7, v___x_3095_);
lean_closure_set(v___f_3097_, 8, v_tag_3083_);
lean_closure_set(v___f_3097_, 9, v_opts_3084_);
lean_closure_set(v___f_3097_, 10, v___x_3096_);
lean_closure_set(v___f_3097_, 11, v_oldTraces_3092_);
lean_closure_set(v___f_3097_, 12, v_toPure_3086_);
lean_closure_set(v___f_3097_, 13, v_toBind_3087_);
lean_closure_set(v___f_3097_, 14, v_k_3088_);
lean_closure_set(v___f_3097_, 15, v_inst_3089_);
lean_closure_set(v___f_3097_, 16, v_msg_3090_);
lean_closure_set(v___f_3097_, 17, v___f_3091_);
lean_closure_set(v___f_3097_, 18, v_withRef_3094_);
lean_closure_set(v___f_3097_, 19, v_getRef_3093_);
v___x_3098_ = lean_apply_4(v_toBind_3087_, lean_box(0), lean_box(0), v_getRef_3093_, v___f_3097_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_3099_ = _args[0];
lean_object* v_always_3100_ = _args[1];
lean_object* v_inst_3101_ = _args[2];
lean_object* v_inst_3102_ = _args[3];
lean_object* v_inst_3103_ = _args[4];
lean_object* v_inst_3104_ = _args[5];
lean_object* v_cls_3105_ = _args[6];
lean_object* v_collapsed_3106_ = _args[7];
lean_object* v_tag_3107_ = _args[8];
lean_object* v_opts_3108_ = _args[9];
lean_object* v_clsEnabled_3109_ = _args[10];
lean_object* v_toPure_3110_ = _args[11];
lean_object* v_toBind_3111_ = _args[12];
lean_object* v_k_3112_ = _args[13];
lean_object* v_inst_3113_ = _args[14];
lean_object* v_msg_3114_ = _args[15];
lean_object* v___f_3115_ = _args[16];
lean_object* v_oldTraces_3116_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3117_; uint8_t v_clsEnabled_boxed_3118_; lean_object* v_res_3119_; 
v_collapsed_boxed_3117_ = lean_unbox(v_collapsed_3106_);
v_clsEnabled_boxed_3118_ = lean_unbox(v_clsEnabled_3109_);
v_res_3119_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3099_, v_always_3100_, v_inst_3101_, v_inst_3102_, v_inst_3103_, v_inst_3104_, v_cls_3105_, v_collapsed_boxed_3117_, v_tag_3107_, v_opts_3108_, v_clsEnabled_boxed_3118_, v_toPure_3110_, v_toBind_3111_, v_k_3112_, v_inst_3113_, v_msg_3114_, v___f_3115_, v_oldTraces_3116_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object* v_inst_3120_, lean_object* v_always_3121_, lean_object* v_inst_3122_, lean_object* v_inst_3123_, lean_object* v_inst_3124_, lean_object* v_inst_3125_, lean_object* v_cls_3126_, uint8_t v_collapsed_3127_, lean_object* v_tag_3128_, lean_object* v_opts_3129_, lean_object* v_toPure_3130_, lean_object* v_toBind_3131_, lean_object* v_k_3132_, lean_object* v_inst_3133_, lean_object* v_msg_3134_, lean_object* v___f_3135_, uint8_t v_clsEnabled_3136_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___f_3139_; 
v___x_3137_ = lean_box(v_collapsed_3127_);
v___x_3138_ = lean_box(v_clsEnabled_3136_);
lean_inc(v_k_3132_);
lean_inc(v_toBind_3131_);
lean_inc_ref(v_opts_3129_);
lean_inc_ref(v_inst_3123_);
lean_inc_ref(v_inst_3122_);
v___f_3139_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__2___boxed), 18, 17);
lean_closure_set(v___f_3139_, 0, v_inst_3120_);
lean_closure_set(v___f_3139_, 1, v_always_3121_);
lean_closure_set(v___f_3139_, 2, v_inst_3122_);
lean_closure_set(v___f_3139_, 3, v_inst_3123_);
lean_closure_set(v___f_3139_, 4, v_inst_3124_);
lean_closure_set(v___f_3139_, 5, v_inst_3125_);
lean_closure_set(v___f_3139_, 6, v_cls_3126_);
lean_closure_set(v___f_3139_, 7, v___x_3137_);
lean_closure_set(v___f_3139_, 8, v_tag_3128_);
lean_closure_set(v___f_3139_, 9, v_opts_3129_);
lean_closure_set(v___f_3139_, 10, v___x_3138_);
lean_closure_set(v___f_3139_, 11, v_toPure_3130_);
lean_closure_set(v___f_3139_, 12, v_toBind_3131_);
lean_closure_set(v___f_3139_, 13, v_k_3132_);
lean_closure_set(v___f_3139_, 14, v_inst_3133_);
lean_closure_set(v___f_3139_, 15, v_msg_3134_);
lean_closure_set(v___f_3139_, 16, v___f_3135_);
if (v_clsEnabled_3136_ == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3143_ = l_Lean_KVMap_instValueBool;
v___x_3144_ = l_Lean_trace_profiler;
v___x_3145_ = l_Lean_Option_get___redArg(v___x_3143_, v_opts_3129_, v___x_3144_);
lean_dec_ref(v_opts_3129_);
v___x_3146_ = lean_unbox(v___x_3145_);
lean_dec(v___x_3145_);
if (v___x_3146_ == 0)
{
lean_dec_ref(v___f_3139_);
lean_dec(v_toBind_3131_);
lean_dec_ref(v_inst_3123_);
lean_dec_ref(v_inst_3122_);
return v_k_3132_;
}
else
{
lean_dec(v_k_3132_);
goto v___jp_3140_;
}
}
else
{
lean_dec(v_k_3132_);
lean_dec_ref(v_opts_3129_);
goto v___jp_3140_;
}
v___jp_3140_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3122_, v_inst_3123_);
v___x_3142_ = lean_apply_4(v_toBind_3131_, lean_box(0), lean_box(0), v___x_3141_, v___f_3139_);
return v___x_3142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_3147_ = _args[0];
lean_object* v_always_3148_ = _args[1];
lean_object* v_inst_3149_ = _args[2];
lean_object* v_inst_3150_ = _args[3];
lean_object* v_inst_3151_ = _args[4];
lean_object* v_inst_3152_ = _args[5];
lean_object* v_cls_3153_ = _args[6];
lean_object* v_collapsed_3154_ = _args[7];
lean_object* v_tag_3155_ = _args[8];
lean_object* v_opts_3156_ = _args[9];
lean_object* v_toPure_3157_ = _args[10];
lean_object* v_toBind_3158_ = _args[11];
lean_object* v_k_3159_ = _args[12];
lean_object* v_inst_3160_ = _args[13];
lean_object* v_msg_3161_ = _args[14];
lean_object* v___f_3162_ = _args[15];
lean_object* v_clsEnabled_3163_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3164_; uint8_t v_clsEnabled_boxed_3165_; lean_object* v_res_3166_; 
v_collapsed_boxed_3164_ = lean_unbox(v_collapsed_3154_);
v_clsEnabled_boxed_3165_ = lean_unbox(v_clsEnabled_3163_);
v_res_3166_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3147_, v_always_3148_, v_inst_3149_, v_inst_3150_, v_inst_3151_, v_inst_3152_, v_cls_3153_, v_collapsed_boxed_3164_, v_tag_3155_, v_opts_3156_, v_toPure_3157_, v_toBind_3158_, v_k_3159_, v_inst_3160_, v_msg_3161_, v___f_3162_, v_clsEnabled_boxed_3165_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object* v_inst_3167_, lean_object* v_toApplicative_3168_, lean_object* v_inst_3169_, lean_object* v_always_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_cls_3174_, uint8_t v_collapsed_3175_, lean_object* v_tag_3176_, lean_object* v_toBind_3177_, lean_object* v_k_3178_, lean_object* v_inst_3179_, lean_object* v_msg_3180_, lean_object* v___f_3181_, lean_object* v_inst_3182_, lean_object* v_opts_3183_){
_start:
{
uint8_t v_hasTrace_3184_; uint8_t v___x_3185_; 
v_hasTrace_3184_ = lean_ctor_get_uint8(v_opts_3183_, sizeof(void*)*1);
v___x_3185_ = lean_bool_not(v_hasTrace_3184_);
if (v___x_3185_ == 0)
{
lean_object* v_getInheritedTraceOptions_3186_; lean_object* v_toPure_3187_; lean_object* v___x_3188_; lean_object* v___f_3189_; lean_object* v___f_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_getInheritedTraceOptions_3186_ = lean_ctor_get(v_inst_3167_, 2);
lean_inc(v_getInheritedTraceOptions_3186_);
v_toPure_3187_ = lean_ctor_get(v_toApplicative_3168_, 1);
lean_inc_n(v_toPure_3187_, 2);
lean_dec_ref(v_toApplicative_3168_);
v___x_3188_ = lean_box(v_collapsed_3175_);
lean_inc_n(v_toBind_3177_, 3);
lean_inc(v_cls_3174_);
v___f_3189_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_3189_, 0, v_inst_3169_);
lean_closure_set(v___f_3189_, 1, v_always_3170_);
lean_closure_set(v___f_3189_, 2, v_inst_3171_);
lean_closure_set(v___f_3189_, 3, v_inst_3167_);
lean_closure_set(v___f_3189_, 4, v_inst_3172_);
lean_closure_set(v___f_3189_, 5, v_inst_3173_);
lean_closure_set(v___f_3189_, 6, v_cls_3174_);
lean_closure_set(v___f_3189_, 7, v___x_3188_);
lean_closure_set(v___f_3189_, 8, v_tag_3176_);
lean_closure_set(v___f_3189_, 9, v_opts_3183_);
lean_closure_set(v___f_3189_, 10, v_toPure_3187_);
lean_closure_set(v___f_3189_, 11, v_toBind_3177_);
lean_closure_set(v___f_3189_, 12, v_k_3178_);
lean_closure_set(v___f_3189_, 13, v_inst_3179_);
lean_closure_set(v___f_3189_, 14, v_msg_3180_);
lean_closure_set(v___f_3189_, 15, v___f_3181_);
v___f_3190_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3190_, 0, v_toPure_3187_);
lean_closure_set(v___f_3190_, 1, v_cls_3174_);
lean_closure_set(v___f_3190_, 2, v_toBind_3177_);
lean_closure_set(v___f_3190_, 3, v_inst_3182_);
v___x_3191_ = lean_apply_4(v_toBind_3177_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3186_, v___f_3190_);
v___x_3192_ = lean_apply_4(v_toBind_3177_, lean_box(0), lean_box(0), v___x_3191_, v___f_3189_);
return v___x_3192_;
}
else
{
lean_dec_ref(v_opts_3183_);
lean_dec(v_inst_3182_);
lean_dec(v___f_3181_);
lean_dec(v_msg_3180_);
lean_dec(v_inst_3179_);
lean_dec(v_toBind_3177_);
lean_dec_ref(v_tag_3176_);
lean_dec(v_cls_3174_);
lean_dec_ref(v_inst_3173_);
lean_dec(v_inst_3172_);
lean_dec_ref(v_inst_3171_);
lean_dec_ref(v_always_3170_);
lean_dec_ref(v_inst_3169_);
lean_dec_ref(v_toApplicative_3168_);
lean_dec_ref(v_inst_3167_);
return v_k_3178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_inst_3193_ = _args[0];
lean_object* v_toApplicative_3194_ = _args[1];
lean_object* v_inst_3195_ = _args[2];
lean_object* v_always_3196_ = _args[3];
lean_object* v_inst_3197_ = _args[4];
lean_object* v_inst_3198_ = _args[5];
lean_object* v_inst_3199_ = _args[6];
lean_object* v_cls_3200_ = _args[7];
lean_object* v_collapsed_3201_ = _args[8];
lean_object* v_tag_3202_ = _args[9];
lean_object* v_toBind_3203_ = _args[10];
lean_object* v_k_3204_ = _args[11];
lean_object* v_inst_3205_ = _args[12];
lean_object* v_msg_3206_ = _args[13];
lean_object* v___f_3207_ = _args[14];
lean_object* v_inst_3208_ = _args[15];
lean_object* v_opts_3209_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3210_; lean_object* v_res_3211_; 
v_collapsed_boxed_3210_ = lean_unbox(v_collapsed_3201_);
v_res_3211_ = l_Lean_withTraceNodeBefore___redArg___lam__7(v_inst_3193_, v_toApplicative_3194_, v_inst_3195_, v_always_3196_, v_inst_3197_, v_inst_3198_, v_inst_3199_, v_cls_3200_, v_collapsed_boxed_3210_, v_tag_3202_, v_toBind_3203_, v_k_3204_, v_inst_3205_, v_msg_3206_, v___f_3207_, v_inst_3208_, v_opts_3209_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_always_3217_, lean_object* v_inst_3218_, lean_object* v_inst_3219_, lean_object* v_cls_3220_, lean_object* v_msg_3221_, lean_object* v_k_3222_, uint8_t v_collapsed_3223_, lean_object* v_tag_3224_){
_start:
{
lean_object* v_toApplicative_3225_; lean_object* v_toBind_3226_; lean_object* v___f_3227_; lean_object* v___x_3228_; lean_object* v___f_3229_; lean_object* v___x_3230_; 
v_toApplicative_3225_ = lean_ctor_get(v_inst_3212_, 0);
lean_inc_ref(v_toApplicative_3225_);
v_toBind_3226_ = lean_ctor_get(v_inst_3212_, 1);
lean_inc_n(v_toBind_3226_, 2);
lean_inc(v_inst_3215_);
v___f_3227_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3227_, 0, v_inst_3215_);
v___x_3228_ = lean_box(v_collapsed_3223_);
lean_inc(v_inst_3216_);
v___f_3229_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3229_, 0, v_inst_3213_);
lean_closure_set(v___f_3229_, 1, v_toApplicative_3225_);
lean_closure_set(v___f_3229_, 2, v_inst_3214_);
lean_closure_set(v___f_3229_, 3, v_always_3217_);
lean_closure_set(v___f_3229_, 4, v_inst_3212_);
lean_closure_set(v___f_3229_, 5, v_inst_3215_);
lean_closure_set(v___f_3229_, 6, v_inst_3219_);
lean_closure_set(v___f_3229_, 7, v_cls_3220_);
lean_closure_set(v___f_3229_, 8, v___x_3228_);
lean_closure_set(v___f_3229_, 9, v_tag_3224_);
lean_closure_set(v___f_3229_, 10, v_toBind_3226_);
lean_closure_set(v___f_3229_, 11, v_k_3222_);
lean_closure_set(v___f_3229_, 12, v_inst_3218_);
lean_closure_set(v___f_3229_, 13, v_msg_3221_);
lean_closure_set(v___f_3229_, 14, v___f_3227_);
lean_closure_set(v___f_3229_, 15, v_inst_3216_);
v___x_3230_ = lean_apply_4(v_toBind_3226_, lean_box(0), lean_box(0), v_inst_3216_, v___f_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_always_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_cls_3239_, lean_object* v_msg_3240_, lean_object* v_k_3241_, lean_object* v_collapsed_3242_, lean_object* v_tag_3243_){
_start:
{
uint8_t v_collapsed_boxed_3244_; lean_object* v_res_3245_; 
v_collapsed_boxed_3244_ = lean_unbox(v_collapsed_3242_);
v_res_3245_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3231_, v_inst_3232_, v_inst_3233_, v_inst_3234_, v_inst_3235_, v_always_3236_, v_inst_3237_, v_inst_3238_, v_cls_3239_, v_msg_3240_, v_k_3241_, v_collapsed_boxed_3244_, v_tag_3243_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object* v_00_u03b1_3246_, lean_object* v_m_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_00_u03b5_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_always_3254_, lean_object* v_inst_3255_, lean_object* v_inst_3256_, lean_object* v_cls_3257_, lean_object* v_msg_3258_, lean_object* v_k_3259_, uint8_t v_collapsed_3260_, lean_object* v_tag_3261_){
_start:
{
lean_object* v_toApplicative_3262_; lean_object* v_toBind_3263_; lean_object* v___f_3264_; lean_object* v___x_3265_; lean_object* v___f_3266_; lean_object* v___x_3267_; 
v_toApplicative_3262_ = lean_ctor_get(v_inst_3248_, 0);
lean_inc_ref(v_toApplicative_3262_);
v_toBind_3263_ = lean_ctor_get(v_inst_3248_, 1);
lean_inc_n(v_toBind_3263_, 2);
lean_inc(v_inst_3252_);
v___f_3264_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3264_, 0, v_inst_3252_);
v___x_3265_ = lean_box(v_collapsed_3260_);
lean_inc(v_inst_3253_);
v___f_3266_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3266_, 0, v_inst_3249_);
lean_closure_set(v___f_3266_, 1, v_toApplicative_3262_);
lean_closure_set(v___f_3266_, 2, v_inst_3251_);
lean_closure_set(v___f_3266_, 3, v_always_3254_);
lean_closure_set(v___f_3266_, 4, v_inst_3248_);
lean_closure_set(v___f_3266_, 5, v_inst_3252_);
lean_closure_set(v___f_3266_, 6, v_inst_3256_);
lean_closure_set(v___f_3266_, 7, v_cls_3257_);
lean_closure_set(v___f_3266_, 8, v___x_3265_);
lean_closure_set(v___f_3266_, 9, v_tag_3261_);
lean_closure_set(v___f_3266_, 10, v_toBind_3263_);
lean_closure_set(v___f_3266_, 11, v_k_3259_);
lean_closure_set(v___f_3266_, 12, v_inst_3255_);
lean_closure_set(v___f_3266_, 13, v_msg_3258_);
lean_closure_set(v___f_3266_, 14, v___f_3264_);
lean_closure_set(v___f_3266_, 15, v_inst_3253_);
v___x_3267_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v_inst_3253_, v___f_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object* v_00_u03b1_3268_, lean_object* v_m_3269_, lean_object* v_inst_3270_, lean_object* v_inst_3271_, lean_object* v_00_u03b5_3272_, lean_object* v_inst_3273_, lean_object* v_inst_3274_, lean_object* v_inst_3275_, lean_object* v_always_3276_, lean_object* v_inst_3277_, lean_object* v_inst_3278_, lean_object* v_cls_3279_, lean_object* v_msg_3280_, lean_object* v_k_3281_, lean_object* v_collapsed_3282_, lean_object* v_tag_3283_){
_start:
{
uint8_t v_collapsed_boxed_3284_; lean_object* v_res_3285_; 
v_collapsed_boxed_3284_ = lean_unbox(v_collapsed_3282_);
v_res_3285_ = l_Lean_withTraceNodeBefore(v_00_u03b1_3268_, v_m_3269_, v_inst_3270_, v_inst_3271_, v_00_u03b5_3272_, v_inst_3273_, v_inst_3274_, v_inst_3275_, v_always_3276_, v_inst_3277_, v_inst_3278_, v_cls_3279_, v_msg_3280_, v_k_3281_, v_collapsed_boxed_3284_, v_tag_3283_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0(lean_object* v_toApplicative_3286_, lean_object* v_____s_3287_){
_start:
{
lean_object* v_toPure_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_toPure_3288_ = lean_ctor_get(v_toApplicative_3286_, 1);
lean_inc(v_toPure_3288_);
lean_dec_ref(v_toApplicative_3286_);
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_apply_2(v_toPure_3288_, lean_box(0), v___x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__1(lean_object* v_x_3291_, lean_object* v_x_3292_){
_start:
{
lean_object* v_fst_3293_; lean_object* v_fst_3294_; lean_object* v_fst_3295_; lean_object* v_fst_3296_; uint8_t v___x_3297_; 
v_fst_3293_ = lean_ctor_get(v_x_3291_, 0);
v_fst_3294_ = lean_ctor_get(v_x_3292_, 0);
v_fst_3295_ = lean_ctor_get(v_fst_3293_, 0);
v_fst_3296_ = lean_ctor_get(v_fst_3294_, 0);
v___x_3297_ = lean_nat_dec_lt(v_fst_3295_, v_fst_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1___boxed(lean_object* v_x_3298_, lean_object* v_x_3299_){
_start:
{
uint8_t v_res_3300_; lean_object* v_r_3301_; 
v_res_3300_ = l_Lean_addTraceAsMessages___redArg___lam__1(v_x_3298_, v_x_3299_);
lean_dec_ref(v_x_3299_);
lean_dec_ref(v_x_3298_);
v_r_3301_ = lean_box(v_res_3300_);
return v_r_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object* v_x1_3302_, lean_object* v_x2_3303_, lean_object* v_x3_3304_){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v_x2_3303_);
lean_ctor_set(v___x_3305_, 1, v_x3_3304_);
v___x_3306_ = lean_array_push(v_x1_3302_, v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object* v_toApplicative_3307_, lean_object* v___x_3308_, lean_object* v_r_3309_){
_start:
{
lean_object* v_toPure_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_toPure_3310_ = lean_ctor_get(v_toApplicative_3307_, 1);
lean_inc(v_toPure_3310_);
lean_dec_ref(v_toApplicative_3307_);
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3308_);
v___x_3312_ = lean_apply_2(v_toPure_3310_, lean_box(0), v___x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object* v_____do__lift_3313_, lean_object* v___x_3314_, lean_object* v_fst_3315_, lean_object* v_snd_3316_, lean_object* v_logMessage_3317_, lean_object* v_toBind_3318_, lean_object* v___f_3319_, lean_object* v_____do__lift_3320_){
_start:
{
uint8_t v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3321_ = 0;
v___x_3322_ = l_Lean_Elab_mkMessageCore(v_____do__lift_3313_, v_____do__lift_3320_, v___x_3314_, v___x_3321_, v_fst_3315_, v_snd_3316_);
v___x_3323_ = lean_apply_1(v_logMessage_3317_, v___x_3322_);
v___x_3324_ = lean_apply_4(v_toBind_3318_, lean_box(0), lean_box(0), v___x_3323_, v___f_3319_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object* v_____do__lift_3325_, lean_object* v___x_3326_, lean_object* v_fst_3327_, lean_object* v_snd_3328_, lean_object* v_logMessage_3329_, lean_object* v_toBind_3330_, lean_object* v___f_3331_, lean_object* v_____do__lift_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_addTraceAsMessages___redArg___lam__4(v_____do__lift_3325_, v___x_3326_, v_fst_3327_, v_snd_3328_, v_logMessage_3329_, v_toBind_3330_, v___f_3331_, v_____do__lift_3332_);
lean_dec(v_snd_3328_);
lean_dec(v_fst_3327_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object* v___x_3334_, lean_object* v_fst_3335_, lean_object* v_snd_3336_, lean_object* v_logMessage_3337_, lean_object* v_toBind_3338_, lean_object* v___f_3339_, lean_object* v_toMonadFileMap_3340_, lean_object* v_____do__lift_3341_){
_start:
{
lean_object* v___f_3342_; lean_object* v___x_3343_; 
lean_inc(v_toBind_3338_);
v___f_3342_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_3342_, 0, v_____do__lift_3341_);
lean_closure_set(v___f_3342_, 1, v___x_3334_);
lean_closure_set(v___f_3342_, 2, v_fst_3335_);
lean_closure_set(v___f_3342_, 3, v_snd_3336_);
lean_closure_set(v___f_3342_, 4, v_logMessage_3337_);
lean_closure_set(v___f_3342_, 5, v_toBind_3338_);
lean_closure_set(v___f_3342_, 6, v___f_3339_);
v___x_3343_ = lean_apply_4(v_toBind_3338_, lean_box(0), lean_box(0), v_toMonadFileMap_3340_, v___f_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object* v___x_3344_, uint8_t v___x_3345_, lean_object* v_inst_3346_, lean_object* v_toBind_3347_, lean_object* v___f_3348_, lean_object* v_a_3349_, lean_object* v_x_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_fst_3352_; lean_object* v_snd_3353_; lean_object* v_fst_3354_; lean_object* v_snd_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3375_; 
v_fst_3352_ = lean_ctor_get(v_a_3349_, 0);
lean_inc(v_fst_3352_);
v_snd_3353_ = lean_ctor_get(v_a_3349_, 1);
lean_inc(v_snd_3353_);
lean_dec_ref(v_a_3349_);
v_fst_3354_ = lean_ctor_get(v_fst_3352_, 0);
v_snd_3355_ = lean_ctor_get(v_fst_3352_, 1);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_fst_3352_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3357_ = v_fst_3352_;
v_isShared_3358_ = v_isSharedCheck_3375_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_snd_3355_);
lean_inc(v_fst_3354_);
lean_dec(v_fst_3352_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3375_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; double v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v_toMonadFileMap_3364_; lean_object* v_getFileName_3365_; lean_object* v_logMessage_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_box(0);
v___x_3361_ = lean_float_of_nat(v___x_3344_);
v___x_3362_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_3363_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3363_, 0, v___x_3359_);
lean_ctor_set(v___x_3363_, 1, v___x_3360_);
lean_ctor_set(v___x_3363_, 2, v___x_3362_);
lean_ctor_set_float(v___x_3363_, sizeof(void*)*3, v___x_3361_);
lean_ctor_set_float(v___x_3363_, sizeof(void*)*3 + 8, v___x_3361_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*3 + 16, v___x_3345_);
v_toMonadFileMap_3364_ = lean_ctor_get(v_inst_3346_, 0);
lean_inc(v_toMonadFileMap_3364_);
v_getFileName_3365_ = lean_ctor_get(v_inst_3346_, 2);
lean_inc(v_getFileName_3365_);
v_logMessage_3366_ = lean_ctor_get(v_inst_3346_, 4);
lean_inc(v_logMessage_3366_);
lean_dec_ref(v_inst_3346_);
v___x_3367_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_3368_ = l_Lean_MessageData_nil;
v___x_3369_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3363_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
lean_ctor_set(v___x_3369_, 2, v_snd_3353_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set_tag(v___x_3357_, 8);
lean_ctor_set(v___x_3357_, 1, v___x_3369_);
lean_ctor_set(v___x_3357_, 0, v___x_3367_);
v___x_3371_ = v___x_3357_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___f_3372_; lean_object* v___x_3373_; 
lean_inc(v_toBind_3347_);
v___f_3372_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__5), 8, 7);
lean_closure_set(v___f_3372_, 0, v___x_3371_);
lean_closure_set(v___f_3372_, 1, v_fst_3354_);
lean_closure_set(v___f_3372_, 2, v_snd_3355_);
lean_closure_set(v___f_3372_, 3, v_logMessage_3366_);
lean_closure_set(v___f_3372_, 4, v_toBind_3347_);
lean_closure_set(v___f_3372_, 5, v___f_3348_);
lean_closure_set(v___f_3372_, 6, v_toMonadFileMap_3364_);
v___x_3373_ = lean_apply_4(v_toBind_3347_, lean_box(0), lean_box(0), v_getFileName_3365_, v___f_3372_);
return v___x_3373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object* v___x_3376_, lean_object* v___x_3377_, lean_object* v_inst_3378_, lean_object* v_toBind_3379_, lean_object* v___f_3380_, lean_object* v_a_3381_, lean_object* v_x_3382_, lean_object* v___y_3383_){
_start:
{
uint8_t v___x_1730__boxed_3384_; lean_object* v_res_3385_; 
v___x_1730__boxed_3384_ = lean_unbox(v___x_3377_);
v_res_3385_ = l_Lean_addTraceAsMessages___redArg___lam__6(v___x_3376_, v___x_1730__boxed_3384_, v_inst_3378_, v_toBind_3379_, v___f_3380_, v_a_3381_, v_x_3382_, v___y_3383_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object* v___x_3386_, lean_object* v___f_3387_, lean_object* v_acc_3388_, lean_object* v_l_3389_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_3386_, v___f_3387_, v_acc_3388_, v_l_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object* v_toApplicative_3391_, uint8_t v___x_3392_, lean_object* v_inst_3393_, lean_object* v_toBind_3394_, lean_object* v_inst_3395_, lean_object* v___f_3396_, lean_object* v___f_3397_, lean_object* v___f_3398_, lean_object* v_____s_3399_){
_start:
{
lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3426_; lean_object* v_size_3433_; lean_object* v_buckets_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
v_size_3433_ = lean_ctor_get(v_____s_3399_, 0);
lean_inc(v_size_3433_);
v_buckets_3434_ = lean_ctor_get(v_____s_3399_, 1);
lean_inc_ref(v_buckets_3434_);
lean_dec_ref(v_____s_3399_);
v___x_3435_ = lean_mk_empty_array_with_capacity(v_size_3433_);
lean_dec(v_size_3433_);
v___x_3436_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v___x_3437_ = lean_unsigned_to_nat(0u);
v___x_3438_ = lean_array_get_size(v_buckets_3434_);
v___x_3439_ = lean_nat_dec_lt(v___x_3437_, v___x_3438_);
if (v___x_3439_ == 0)
{
lean_dec_ref(v_buckets_3434_);
lean_dec_ref(v___f_3398_);
v___y_3426_ = v___x_3435_;
goto v___jp_3425_;
}
else
{
lean_object* v___f_3440_; uint8_t v___x_3441_; 
v___f_3440_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__7), 4, 2);
lean_closure_set(v___f_3440_, 0, v___x_3436_);
lean_closure_set(v___f_3440_, 1, v___f_3398_);
v___x_3441_ = lean_nat_dec_le(v___x_3438_, v___x_3438_);
if (v___x_3441_ == 0)
{
if (v___x_3439_ == 0)
{
lean_dec_ref(v___f_3440_);
lean_dec_ref(v_buckets_3434_);
v___y_3426_ = v___x_3435_;
goto v___jp_3425_;
}
else
{
size_t v___x_3442_; size_t v___x_3443_; lean_object* v___x_3444_; 
v___x_3442_ = ((size_t)0ULL);
v___x_3443_ = lean_usize_of_nat(v___x_3438_);
v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3436_, v___f_3440_, v_buckets_3434_, v___x_3442_, v___x_3443_, v___x_3435_);
v___y_3426_ = v___x_3444_;
goto v___jp_3425_;
}
}
else
{
size_t v___x_3445_; size_t v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = ((size_t)0ULL);
v___x_3446_ = lean_usize_of_nat(v___x_3438_);
v___x_3447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3436_, v___f_3440_, v_buckets_3434_, v___x_3445_, v___x_3446_, v___x_3435_);
v___y_3426_ = v___x_3447_;
goto v___jp_3425_;
}
}
v___jp_3400_:
{
lean_object* v___x_3403_; lean_object* v___f_3404_; lean_object* v___x_3405_; lean_object* v___f_3406_; size_t v_sz_3407_; size_t v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3403_ = lean_box(0);
v___f_3404_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3404_, 0, v_toApplicative_3391_);
lean_closure_set(v___f_3404_, 1, v___x_3403_);
v___x_3405_ = lean_box(v___x_3392_);
lean_inc(v_toBind_3394_);
v___f_3406_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__6___boxed), 8, 5);
lean_closure_set(v___f_3406_, 0, v___y_3401_);
lean_closure_set(v___f_3406_, 1, v___x_3405_);
lean_closure_set(v___f_3406_, 2, v_inst_3393_);
lean_closure_set(v___f_3406_, 3, v_toBind_3394_);
lean_closure_set(v___f_3406_, 4, v___f_3404_);
v_sz_3407_ = lean_array_size(v___y_3402_);
v___x_3408_ = ((size_t)0ULL);
v___x_3409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3395_, v___y_3402_, v___f_3406_, v_sz_3407_, v___x_3408_, v___x_3403_);
v___x_3410_ = lean_apply_4(v_toBind_3394_, lean_box(0), lean_box(0), v___x_3409_, v___f_3396_);
return v___x_3410_;
}
v___jp_3411_:
{
lean_object* v___x_3417_; 
v___x_3417_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_3397_, v___y_3414_, v___y_3415_, v___y_3413_, v___y_3416_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_3416_);
lean_dec(v___y_3414_);
v___y_3401_ = v___y_3412_;
v___y_3402_ = v___x_3417_;
goto v___jp_3400_;
}
v___jp_3418_:
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_nat_dec_le(v___y_3423_, v___y_3420_);
if (v___x_3424_ == 0)
{
lean_dec(v___y_3420_);
lean_inc(v___y_3423_);
v___y_3412_ = v___y_3419_;
v___y_3413_ = v___y_3423_;
v___y_3414_ = v___y_3421_;
v___y_3415_ = v___y_3422_;
v___y_3416_ = v___y_3423_;
goto v___jp_3411_;
}
else
{
v___y_3412_ = v___y_3419_;
v___y_3413_ = v___y_3423_;
v___y_3414_ = v___y_3421_;
v___y_3415_ = v___y_3422_;
v___y_3416_ = v___y_3420_;
goto v___jp_3411_;
}
}
v___jp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3427_ = lean_unsigned_to_nat(0u);
v___x_3428_ = lean_array_get_size(v___y_3426_);
v___x_3429_ = lean_nat_dec_eq(v___x_3428_, v___x_3427_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3430_ = lean_unsigned_to_nat(1u);
v___x_3431_ = lean_nat_sub(v___x_3428_, v___x_3430_);
v___x_3432_ = lean_nat_dec_le(v___x_3427_, v___x_3431_);
if (v___x_3432_ == 0)
{
lean_inc(v___x_3431_);
v___y_3419_ = v___x_3427_;
v___y_3420_ = v___x_3431_;
v___y_3421_ = v___x_3428_;
v___y_3422_ = v___y_3426_;
v___y_3423_ = v___x_3431_;
goto v___jp_3418_;
}
else
{
v___y_3419_ = v___x_3427_;
v___y_3420_ = v___x_3431_;
v___y_3421_ = v___x_3428_;
v___y_3422_ = v___y_3426_;
v___y_3423_ = v___x_3427_;
goto v___jp_3418_;
}
}
else
{
lean_dec_ref(v___f_3397_);
v___y_3401_ = v___x_3427_;
v___y_3402_ = v___y_3426_;
goto v___jp_3400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object* v_toApplicative_3448_, lean_object* v___x_3449_, lean_object* v_inst_3450_, lean_object* v_toBind_3451_, lean_object* v_inst_3452_, lean_object* v___f_3453_, lean_object* v___f_3454_, lean_object* v___f_3455_, lean_object* v_____s_3456_){
_start:
{
uint8_t v___x_1818__boxed_3457_; lean_object* v_res_3458_; 
v___x_1818__boxed_3457_ = lean_unbox(v___x_3449_);
v_res_3458_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_toApplicative_3448_, v___x_1818__boxed_3457_, v_inst_3450_, v_toBind_3451_, v_inst_3452_, v___f_3453_, v___f_3454_, v___f_3455_, v_____s_3456_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object* v_traceElem_3459_, lean_object* v_toApplicative_3460_, lean_object* v___f_3461_, lean_object* v___f_3462_, lean_object* v_____s_3463_, uint8_t v___x_3464_, lean_object* v_____do__lift_3465_){
_start:
{
lean_object* v_ref_3466_; lean_object* v_msg_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3492_; 
v_ref_3466_ = lean_ctor_get(v_traceElem_3459_, 0);
v_msg_3467_ = lean_ctor_get(v_traceElem_3459_, 1);
v_isSharedCheck_3492_ = !lean_is_exclusive(v_traceElem_3459_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3469_ = v_traceElem_3459_;
v_isShared_3470_ = v_isSharedCheck_3492_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_msg_3467_);
lean_inc(v_ref_3466_);
lean_dec(v_traceElem_3459_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3492_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v_ref_3484_; lean_object* v___y_3486_; lean_object* v___x_3489_; 
v_ref_3484_ = l_Lean_replaceRef(v_ref_3466_, v_____do__lift_3465_);
lean_dec(v_ref_3466_);
v___x_3489_ = l_Lean_Syntax_getPos_x3f(v_ref_3484_, v___x_3464_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_unsigned_to_nat(0u);
v___y_3486_ = v___x_3490_;
goto v___jp_3485_;
}
else
{
lean_object* v_val_3491_; 
v_val_3491_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_val_3491_);
lean_dec_ref_known(v___x_3489_, 1);
v___y_3486_ = v_val_3491_;
goto v___jp_3485_;
}
v___jp_3471_:
{
lean_object* v_toPure_3474_; lean_object* v___x_3476_; 
v_toPure_3474_ = lean_ctor_get(v_toApplicative_3460_, 1);
lean_inc(v_toPure_3474_);
lean_dec_ref(v_toApplicative_3460_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 1, v___y_3473_);
lean_ctor_set(v___x_3469_, 0, v___y_3472_);
v___x_3476_ = v___x_3469_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___y_3472_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v___y_3473_);
v___x_3476_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v_pos2traces_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3477_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
lean_inc_ref(v___x_3476_);
lean_inc_ref(v___f_3462_);
lean_inc_ref(v___f_3461_);
v___x_3478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_3461_, v___f_3462_, v_____s_3463_, v___x_3476_, v___x_3477_);
v___x_3479_ = lean_array_push(v___x_3478_, v_msg_3467_);
v_pos2traces_3480_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3461_, v___f_3462_, v_____s_3463_, v___x_3476_, v___x_3479_);
v___x_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3481_, 0, v_pos2traces_3480_);
v___x_3482_ = lean_apply_2(v_toPure_3474_, lean_box(0), v___x_3481_);
return v___x_3482_;
}
}
v___jp_3485_:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_Syntax_getTailPos_x3f(v_ref_3484_, v___x_3464_);
lean_dec(v_ref_3484_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_inc(v___y_3486_);
v___y_3472_ = v___y_3486_;
v___y_3473_ = v___y_3486_;
goto v___jp_3471_;
}
else
{
lean_object* v_val_3488_; 
v_val_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_val_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v___y_3472_ = v___y_3486_;
v___y_3473_ = v_val_3488_;
goto v___jp_3471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object* v_traceElem_3493_, lean_object* v_toApplicative_3494_, lean_object* v___f_3495_, lean_object* v___f_3496_, lean_object* v_____s_3497_, lean_object* v___x_3498_, lean_object* v_____do__lift_3499_){
_start:
{
uint8_t v___x_1943__boxed_3500_; lean_object* v_res_3501_; 
v___x_1943__boxed_3500_ = lean_unbox(v___x_3498_);
v_res_3501_ = l_Lean_addTraceAsMessages___redArg___lam__9(v_traceElem_3493_, v_toApplicative_3494_, v___f_3495_, v___f_3496_, v_____s_3497_, v___x_1943__boxed_3500_, v_____do__lift_3499_);
lean_dec(v_____do__lift_3499_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object* v_inst_3502_, lean_object* v_toApplicative_3503_, lean_object* v___f_3504_, lean_object* v___f_3505_, uint8_t v___x_3506_, lean_object* v_toBind_3507_, lean_object* v_traceElem_3508_, lean_object* v_____s_3509_){
_start:
{
lean_object* v_getRef_3510_; lean_object* v___x_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; 
v_getRef_3510_ = lean_ctor_get(v_inst_3502_, 0);
lean_inc(v_getRef_3510_);
lean_dec_ref(v_inst_3502_);
v___x_3511_ = lean_box(v___x_3506_);
v___f_3512_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_3512_, 0, v_traceElem_3508_);
lean_closure_set(v___f_3512_, 1, v_toApplicative_3503_);
lean_closure_set(v___f_3512_, 2, v___f_3504_);
lean_closure_set(v___f_3512_, 3, v___f_3505_);
lean_closure_set(v___f_3512_, 4, v_____s_3509_);
lean_closure_set(v___f_3512_, 5, v___x_3511_);
v___x_3513_ = lean_apply_4(v_toBind_3507_, lean_box(0), lean_box(0), v_getRef_3510_, v___f_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object* v_inst_3514_, lean_object* v_toApplicative_3515_, lean_object* v___f_3516_, lean_object* v___f_3517_, lean_object* v___x_3518_, lean_object* v_toBind_3519_, lean_object* v_traceElem_3520_, lean_object* v_____s_3521_){
_start:
{
uint8_t v___x_2003__boxed_3522_; lean_object* v_res_3523_; 
v___x_2003__boxed_3522_ = lean_unbox(v___x_3518_);
v_res_3523_ = l_Lean_addTraceAsMessages___redArg___lam__10(v_inst_3514_, v_toApplicative_3515_, v___f_3516_, v___f_3517_, v___x_2003__boxed_3522_, v_toBind_3519_, v_traceElem_3520_, v_____s_3521_);
return v_res_3523_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___f_3525_; 
v___x_3524_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_3525_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3525_, 0, v___x_3524_);
return v___f_3525_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___f_3526_; lean_object* v___f_3527_; 
v___f_3526_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__0, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0);
v___f_3527_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3527_, 0, v___f_3526_);
lean_closure_set(v___f_3527_, 1, v___f_3526_);
return v___f_3527_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3531_ = lean_box(0);
v___x_3532_ = lean_unsigned_to_nat(16u);
v___x_3533_ = lean_mk_array(v___x_3532_, v___x_3531_);
return v___x_3533_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5(void){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v_pos2traces_3536_; 
v___x_3534_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__4, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4);
v___x_3535_ = lean_unsigned_to_nat(0u);
v_pos2traces_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_3536_, 0, v___x_3535_);
lean_ctor_set(v_pos2traces_3536_, 1, v___x_3534_);
return v_pos2traces_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11(lean_object* v_inst_3537_, lean_object* v_toApplicative_3538_, lean_object* v_toBind_3539_, lean_object* v_inst_3540_, lean_object* v___f_3541_, lean_object* v_traces_3542_){
_start:
{
uint8_t v___x_3543_; 
v___x_3543_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___f_3544_; lean_object* v___f_3545_; lean_object* v___x_3546_; lean_object* v___f_3547_; lean_object* v_pos2traces_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___f_3544_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__1, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1);
v___f_3545_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___lam__11___closed__3));
v___x_3546_ = lean_box(v___x_3543_);
lean_inc(v_toBind_3539_);
v___f_3547_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3547_, 0, v_inst_3537_);
lean_closure_set(v___f_3547_, 1, v_toApplicative_3538_);
lean_closure_set(v___f_3547_, 2, v___f_3544_);
lean_closure_set(v___f_3547_, 3, v___f_3545_);
lean_closure_set(v___f_3547_, 4, v___x_3546_);
lean_closure_set(v___f_3547_, 5, v_toBind_3539_);
v_pos2traces_3548_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__5, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5);
v___x_3549_ = l_Lean_PersistentArray_forIn___redArg(v_inst_3540_, v_traces_3542_, v_pos2traces_3548_, v___f_3547_);
v___x_3550_ = lean_apply_4(v_toBind_3539_, lean_box(0), lean_box(0), v___x_3549_, v___f_3541_);
return v___x_3550_;
}
else
{
lean_object* v_toPure_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
lean_dec(v___f_3541_);
lean_dec_ref(v_inst_3540_);
lean_dec(v_toBind_3539_);
lean_dec_ref(v_inst_3537_);
v_toPure_3551_ = lean_ctor_get(v_toApplicative_3538_, 1);
lean_inc(v_toPure_3551_);
lean_dec_ref(v_toApplicative_3538_);
v___x_3552_ = lean_box(0);
v___x_3553_ = lean_apply_2(v_toPure_3551_, lean_box(0), v___x_3552_);
return v___x_3553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___boxed(lean_object* v_inst_3554_, lean_object* v_toApplicative_3555_, lean_object* v_toBind_3556_, lean_object* v_inst_3557_, lean_object* v___f_3558_, lean_object* v_traces_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_addTraceAsMessages___redArg___lam__11(v_inst_3554_, v_toApplicative_3555_, v_toBind_3556_, v_inst_3557_, v___f_3558_, v_traces_3559_);
lean_dec_ref(v_traces_3559_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12(lean_object* v_toApplicative_3561_, lean_object* v_inst_3562_, lean_object* v_toBind_3563_, lean_object* v_inst_3564_, lean_object* v___f_3565_, lean_object* v___f_3566_, lean_object* v___f_3567_, lean_object* v_inst_3568_, lean_object* v_inst_3569_, lean_object* v_____do__lift_3570_){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3575_ = l_Lean_KVMap_instValueBool;
v___x_3576_ = l_Lean_KVMap_instValueString;
v___x_3577_ = l_Lean_trace_profiler_output;
v___x_3578_ = l_Lean_Option_get_x3f___redArg(v___x_3576_, v_____do__lift_3570_, v___x_3577_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3579_ = l_Lean_trace_profiler_serve;
v___x_3580_ = l_Lean_Option_get___redArg(v___x_3575_, v_____do__lift_3570_, v___x_3579_);
v___x_3581_ = lean_unbox(v___x_3580_);
lean_dec(v___x_3580_);
if (v___x_3581_ == 0)
{
uint8_t v___x_3582_; lean_object* v___x_3583_; lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3582_ = 1;
v___x_3583_ = lean_box(v___x_3582_);
lean_inc_ref_n(v_inst_3564_, 2);
lean_inc_n(v_toBind_3563_, 2);
lean_inc_ref(v_toApplicative_3561_);
v___f_3584_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__8___boxed), 9, 8);
lean_closure_set(v___f_3584_, 0, v_toApplicative_3561_);
lean_closure_set(v___f_3584_, 1, v___x_3583_);
lean_closure_set(v___f_3584_, 2, v_inst_3562_);
lean_closure_set(v___f_3584_, 3, v_toBind_3563_);
lean_closure_set(v___f_3584_, 4, v_inst_3564_);
lean_closure_set(v___f_3584_, 5, v___f_3565_);
lean_closure_set(v___f_3584_, 6, v___f_3566_);
lean_closure_set(v___f_3584_, 7, v___f_3567_);
v___f_3585_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__11___boxed), 6, 5);
lean_closure_set(v___f_3585_, 0, v_inst_3568_);
lean_closure_set(v___f_3585_, 1, v_toApplicative_3561_);
lean_closure_set(v___f_3585_, 2, v_toBind_3563_);
lean_closure_set(v___f_3585_, 3, v_inst_3564_);
lean_closure_set(v___f_3585_, 4, v___f_3584_);
v___x_3586_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3564_, v_inst_3569_);
v___x_3587_ = lean_apply_4(v_toBind_3563_, lean_box(0), lean_box(0), v___x_3586_, v___f_3585_);
return v___x_3587_;
}
else
{
lean_dec_ref(v_inst_3569_);
lean_dec_ref(v_inst_3568_);
lean_dec_ref(v___f_3567_);
lean_dec_ref(v___f_3566_);
lean_dec(v___f_3565_);
lean_dec_ref(v_inst_3564_);
lean_dec(v_toBind_3563_);
lean_dec_ref(v_inst_3562_);
goto v___jp_3571_;
}
}
else
{
lean_dec_ref_known(v___x_3578_, 1);
lean_dec_ref(v_inst_3569_);
lean_dec_ref(v_inst_3568_);
lean_dec_ref(v___f_3567_);
lean_dec_ref(v___f_3566_);
lean_dec(v___f_3565_);
lean_dec_ref(v_inst_3564_);
lean_dec(v_toBind_3563_);
lean_dec_ref(v_inst_3562_);
goto v___jp_3571_;
}
v___jp_3571_:
{
lean_object* v_toPure_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v_toPure_3572_ = lean_ctor_get(v_toApplicative_3561_, 1);
lean_inc(v_toPure_3572_);
lean_dec_ref(v_toApplicative_3561_);
v___x_3573_ = lean_box(0);
v___x_3574_ = lean_apply_2(v_toPure_3572_, lean_box(0), v___x_3573_);
return v___x_3574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12___boxed(lean_object* v_toApplicative_3588_, lean_object* v_inst_3589_, lean_object* v_toBind_3590_, lean_object* v_inst_3591_, lean_object* v___f_3592_, lean_object* v___f_3593_, lean_object* v___f_3594_, lean_object* v_inst_3595_, lean_object* v_inst_3596_, lean_object* v_____do__lift_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_addTraceAsMessages___redArg___lam__12(v_toApplicative_3588_, v_inst_3589_, v_toBind_3590_, v_inst_3591_, v___f_3592_, v___f_3593_, v___f_3594_, v_inst_3595_, v_inst_3596_, v_____do__lift_3597_);
lean_dec_ref(v_____do__lift_3597_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object* v_inst_3601_, lean_object* v_inst_3602_, lean_object* v_inst_3603_, lean_object* v_inst_3604_, lean_object* v_inst_3605_){
_start:
{
lean_object* v_toApplicative_3606_; lean_object* v_toBind_3607_; lean_object* v___f_3608_; lean_object* v___f_3609_; lean_object* v___f_3610_; lean_object* v___f_3611_; lean_object* v___x_3612_; 
v_toApplicative_3606_ = lean_ctor_get(v_inst_3602_, 0);
lean_inc_ref_n(v_toApplicative_3606_, 2);
v_toBind_3607_ = lean_ctor_get(v_inst_3602_, 1);
lean_inc_n(v_toBind_3607_, 2);
v___f_3608_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3608_, 0, v_toApplicative_3606_);
v___f_3609_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__0));
v___f_3610_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__1));
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__12___boxed), 10, 9);
lean_closure_set(v___f_3611_, 0, v_toApplicative_3606_);
lean_closure_set(v___f_3611_, 1, v_inst_3604_);
lean_closure_set(v___f_3611_, 2, v_toBind_3607_);
lean_closure_set(v___f_3611_, 3, v_inst_3602_);
lean_closure_set(v___f_3611_, 4, v___f_3608_);
lean_closure_set(v___f_3611_, 5, v___f_3609_);
lean_closure_set(v___f_3611_, 6, v___f_3610_);
lean_closure_set(v___f_3611_, 7, v_inst_3603_);
lean_closure_set(v___f_3611_, 8, v_inst_3605_);
v___x_3612_ = lean_apply_4(v_toBind_3607_, lean_box(0), lean_box(0), v_inst_3601_, v___f_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object* v_m_3613_, lean_object* v_inst_3614_, lean_object* v_inst_3615_, lean_object* v_inst_3616_, lean_object* v_inst_3617_, lean_object* v_inst_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Lean_addTraceAsMessages___redArg(v_inst_3614_, v_inst_3615_, v_inst_3616_, v_inst_3617_, v_inst_3618_);
return v___x_3619_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = lean_unsigned_to_nat(2826257906u);
v___x_3662_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3663_ = l_Lean_Name_num___override(v___x_3662_, v___x_3661_);
return v___x_3663_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3665_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3666_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3667_ = l_Lean_Name_str___override(v___x_3666_, v___x_3665_);
return v___x_3667_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3670_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3671_ = l_Lean_Name_str___override(v___x_3670_, v___x_3669_);
return v___x_3671_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = lean_unsigned_to_nat(2u);
v___x_3673_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3674_ = l_Lean_Name_num___override(v___x_3673_, v___x_3672_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3676_; uint8_t v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3676_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3677_ = 0;
v___x_3678_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3679_ = l_Lean_registerTraceClass(v___x_3676_, v___x_3677_, v___x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object* v_a_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
return v_res_3681_;
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
