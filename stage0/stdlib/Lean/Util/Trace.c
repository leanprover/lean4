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
uint8_t v_____do__lift_148__boxed_590_; lean_object* v_res_591_; 
v_____do__lift_148__boxed_590_ = lean_unbox(v_____do__lift_589_);
v_res_591_ = l_Lean_trace___redArg___lam__0(v_toPure_582_, v_msg_583_, v_inst_584_, v_inst_585_, v_inst_586_, v_inst_587_, v_cls_588_, v_____do__lift_148__boxed_590_);
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
uint8_t v_____do__lift_154__boxed_643_; lean_object* v_res_644_; 
v_____do__lift_154__boxed_643_ = lean_unbox(v_____do__lift_642_);
v_res_644_ = l_Lean_traceM___redArg___lam__1(v_toPure_638_, v_toBind_639_, v_mkMsg_640_, v___f_641_, v_____do__lift_154__boxed_643_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_992_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_993_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_994_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_995_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_992_, v___x_993_, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4____boxed(lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
return v_res_997_;
}
}
LEAN_EXPORT uint8_t l_Lean_trace_profiler_isExporting(lean_object* v_opts_998_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_999_ = l_Lean_KVMap_instValueBool;
v___x_1000_ = l_Lean_KVMap_instValueString;
v___x_1001_ = l_Lean_trace_profiler_output;
v___x_1002_ = l_Lean_Option_get_x3f___redArg(v___x_1000_, v_opts_998_, v___x_1001_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = l_Lean_trace_profiler_serve;
v___x_1004_ = l_Lean_Option_get___redArg(v___x_999_, v_opts_998_, v___x_1003_);
v___x_1005_ = lean_unbox(v___x_1004_);
lean_dec(v___x_1004_);
return v___x_1005_;
}
else
{
uint8_t v___x_1006_; 
lean_dec_ref_known(v___x_1002_, 1);
v___x_1006_ = 1;
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_isExporting___boxed(lean_object* v_opts_1007_){
_start:
{
uint8_t v_res_1008_; lean_object* v_r_1009_; 
v_res_1008_ = l_Lean_trace_profiler_isExporting(v_opts_1007_);
lean_dec_ref(v_opts_1007_);
v_r_1009_ = lean_box(v_res_1008_);
return v_r_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1029_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1030_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1031_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1032_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_1029_, v___x_1030_, v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
return v_res_1034_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1035_; double v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(1000000000u);
v___x_1036_ = lean_float_of_nat(v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object* v_toApplicative_1037_, lean_object* v_start_1038_, lean_object* v_a_1039_, lean_object* v_stop_1040_){
_start:
{
lean_object* v_toPure_1041_; double v___x_1042_; double v___x_1043_; double v___x_1044_; double v___x_1045_; double v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_toPure_1041_ = lean_ctor_get(v_toApplicative_1037_, 1);
lean_inc(v_toPure_1041_);
lean_dec_ref(v_toApplicative_1037_);
v___x_1042_ = lean_float_of_nat(v_start_1038_);
v___x_1043_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1044_ = lean_float_div(v___x_1042_, v___x_1043_);
v___x_1045_ = lean_float_of_nat(v_stop_1040_);
v___x_1046_ = lean_float_div(v___x_1045_, v___x_1043_);
v___x_1047_ = lean_box_float(v___x_1044_);
v___x_1048_ = lean_box_float(v___x_1046_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_a_1039_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_apply_2(v_toPure_1041_, lean_box(0), v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object* v_toApplicative_1052_, lean_object* v_start_1053_, lean_object* v_toBind_1054_, lean_object* v___x_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___f_1057_; lean_object* v___x_1058_; 
v___f_1057_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1057_, 0, v_toApplicative_1052_);
lean_closure_set(v___f_1057_, 1, v_start_1053_);
lean_closure_set(v___f_1057_, 2, v_a_1056_);
v___x_1058_ = lean_apply_4(v_toBind_1054_, lean_box(0), lean_box(0), v___x_1055_, v___f_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object* v_toApplicative_1059_, lean_object* v_toBind_1060_, lean_object* v___x_1061_, lean_object* v_act_1062_, lean_object* v_start_1063_){
_start:
{
lean_object* v___f_1064_; lean_object* v___x_1065_; 
lean_inc(v_toBind_1060_);
v___f_1064_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1064_, 0, v_toApplicative_1059_);
lean_closure_set(v___f_1064_, 1, v_start_1063_);
lean_closure_set(v___f_1064_, 2, v_toBind_1060_);
lean_closure_set(v___f_1064_, 3, v___x_1061_);
v___x_1065_ = lean_apply_4(v_toBind_1060_, lean_box(0), lean_box(0), v_act_1062_, v___f_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object* v_toApplicative_1066_, lean_object* v_start_1067_, lean_object* v_a_1068_, lean_object* v_stop_1069_){
_start:
{
lean_object* v_toPure_1070_; double v___x_1071_; double v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_toPure_1070_ = lean_ctor_get(v_toApplicative_1066_, 1);
lean_inc(v_toPure_1070_);
lean_dec_ref(v_toApplicative_1066_);
v___x_1071_ = lean_float_of_nat(v_start_1067_);
v___x_1072_ = lean_float_of_nat(v_stop_1069_);
v___x_1073_ = lean_box_float(v___x_1071_);
v___x_1074_ = lean_box_float(v___x_1072_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_a_1068_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_apply_2(v_toPure_1070_, lean_box(0), v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object* v_toApplicative_1078_, lean_object* v_start_1079_, lean_object* v_toBind_1080_, lean_object* v___x_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v___f_1083_; lean_object* v___x_1084_; 
v___f_1083_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1083_, 0, v_toApplicative_1078_);
lean_closure_set(v___f_1083_, 1, v_start_1079_);
lean_closure_set(v___f_1083_, 2, v_a_1082_);
v___x_1084_ = lean_apply_4(v_toBind_1080_, lean_box(0), lean_box(0), v___x_1081_, v___f_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object* v_toApplicative_1085_, lean_object* v_toBind_1086_, lean_object* v___x_1087_, lean_object* v_act_1088_, lean_object* v_start_1089_){
_start:
{
lean_object* v___f_1090_; lean_object* v___x_1091_; 
lean_inc(v_toBind_1086_);
v___f_1090_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1090_, 0, v_toApplicative_1085_);
lean_closure_set(v___f_1090_, 1, v_start_1089_);
lean_closure_set(v___f_1090_, 2, v_toBind_1086_);
lean_closure_set(v___f_1090_, 3, v___x_1087_);
v___x_1091_ = lean_apply_4(v_toBind_1086_, lean_box(0), lean_box(0), v_act_1088_, v___f_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_opts_1096_, lean_object* v_act_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1098_ = l_Lean_KVMap_instValueBool;
v___x_1099_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1100_ = l_Lean_Option_get___redArg(v___x_1098_, v_opts_1096_, v___x_1099_);
v___x_1101_ = lean_unbox(v___x_1100_);
lean_dec(v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v_toApplicative_1102_; lean_object* v_toBind_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; 
v_toApplicative_1102_ = lean_ctor_get(v_inst_1094_, 0);
lean_inc_ref(v_toApplicative_1102_);
v_toBind_1103_ = lean_ctor_get(v_inst_1094_, 1);
lean_inc_n(v_toBind_1103_, 2);
lean_dec_ref(v_inst_1094_);
v___x_1104_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1105_ = lean_apply_2(v_inst_1095_, lean_box(0), v___x_1104_);
lean_inc(v___x_1105_);
v___f_1106_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1106_, 0, v_toApplicative_1102_);
lean_closure_set(v___f_1106_, 1, v_toBind_1103_);
lean_closure_set(v___f_1106_, 2, v___x_1105_);
lean_closure_set(v___f_1106_, 3, v_act_1097_);
v___x_1107_ = lean_apply_4(v_toBind_1103_, lean_box(0), lean_box(0), v___x_1105_, v___f_1106_);
return v___x_1107_;
}
else
{
lean_object* v_toApplicative_1108_; lean_object* v_toBind_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___f_1112_; lean_object* v___x_1113_; 
v_toApplicative_1108_ = lean_ctor_get(v_inst_1094_, 0);
lean_inc_ref(v_toApplicative_1108_);
v_toBind_1109_ = lean_ctor_get(v_inst_1094_, 1);
lean_inc_n(v_toBind_1109_, 2);
lean_dec_ref(v_inst_1094_);
v___x_1110_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1111_ = lean_apply_2(v_inst_1095_, lean_box(0), v___x_1110_);
lean_inc(v___x_1111_);
v___f_1112_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1112_, 0, v_toApplicative_1108_);
lean_closure_set(v___f_1112_, 1, v_toBind_1109_);
lean_closure_set(v___f_1112_, 2, v___x_1111_);
lean_closure_set(v___f_1112_, 3, v_act_1097_);
v___x_1113_ = lean_apply_4(v_toBind_1109_, lean_box(0), lean_box(0), v___x_1111_, v___f_1112_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_opts_1116_, lean_object* v_act_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(v_inst_1114_, v_inst_1115_, v_opts_1116_, v_act_1117_);
lean_dec_ref(v_opts_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object* v_00_u03b1_1119_, lean_object* v_m_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_opts_1123_, lean_object* v_act_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1125_ = l_Lean_KVMap_instValueBool;
v___x_1126_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1127_ = l_Lean_Option_get___redArg(v___x_1125_, v_opts_1123_, v___x_1126_);
v___x_1128_ = lean_unbox(v___x_1127_);
lean_dec(v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v_toApplicative_1129_; lean_object* v_toBind_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; 
v_toApplicative_1129_ = lean_ctor_get(v_inst_1121_, 0);
lean_inc_ref(v_toApplicative_1129_);
v_toBind_1130_ = lean_ctor_get(v_inst_1121_, 1);
lean_inc_n(v_toBind_1130_, 2);
lean_dec_ref(v_inst_1121_);
v___x_1131_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1132_ = lean_apply_2(v_inst_1122_, lean_box(0), v___x_1131_);
lean_inc(v___x_1132_);
v___f_1133_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1133_, 0, v_toApplicative_1129_);
lean_closure_set(v___f_1133_, 1, v_toBind_1130_);
lean_closure_set(v___f_1133_, 2, v___x_1132_);
lean_closure_set(v___f_1133_, 3, v_act_1124_);
v___x_1134_ = lean_apply_4(v_toBind_1130_, lean_box(0), lean_box(0), v___x_1132_, v___f_1133_);
return v___x_1134_;
}
else
{
lean_object* v_toApplicative_1135_; lean_object* v_toBind_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; 
v_toApplicative_1135_ = lean_ctor_get(v_inst_1121_, 0);
lean_inc_ref(v_toApplicative_1135_);
v_toBind_1136_ = lean_ctor_get(v_inst_1121_, 1);
lean_inc_n(v_toBind_1136_, 2);
lean_dec_ref(v_inst_1121_);
v___x_1137_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1138_ = lean_apply_2(v_inst_1122_, lean_box(0), v___x_1137_);
lean_inc(v___x_1138_);
v___f_1139_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1139_, 0, v_toApplicative_1135_);
lean_closure_set(v___f_1139_, 1, v_toBind_1136_);
lean_closure_set(v___f_1139_, 2, v___x_1138_);
lean_closure_set(v___f_1139_, 3, v_act_1124_);
v___x_1140_ = lean_apply_4(v_toBind_1136_, lean_box(0), lean_box(0), v___x_1138_, v___f_1139_);
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_m_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_opts_1145_, lean_object* v_act_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(v_00_u03b1_1141_, v_m_1142_, v_inst_1143_, v_inst_1144_, v_opts_1145_, v_act_1146_);
lean_dec_ref(v_opts_1145_);
return v_res_1147_;
}
}
static double _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0(void){
_start:
{
lean_object* v___x_1148_; double v___x_1149_; 
v___x_1148_ = lean_unsigned_to_nat(1000u);
v___x_1149_ = lean_float_of_nat(v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object* v_o_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1151_ = l_Lean_KVMap_instValueBool;
v___x_1152_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1153_ = l_Lean_Option_get___redArg(v___x_1151_, v_o_1150_, v___x_1152_);
v___x_1154_ = lean_unbox(v___x_1153_);
lean_dec(v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; double v___x_1158_; double v___x_1159_; double v___x_1160_; 
v___x_1155_ = l_Lean_KVMap_instValueNat;
v___x_1156_ = l_Lean_trace_profiler_threshold;
v___x_1157_ = l_Lean_Option_get___redArg(v___x_1155_, v_o_1150_, v___x_1156_);
v___x_1158_ = lean_float_of_nat(v___x_1157_);
v___x_1159_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1160_ = lean_float_div(v___x_1158_, v___x_1159_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; double v___x_1164_; 
v___x_1161_ = l_Lean_KVMap_instValueNat;
v___x_1162_ = l_Lean_trace_profiler_threshold;
v___x_1163_ = l_Lean_Option_get___redArg(v___x_1161_, v_o_1150_, v___x_1162_);
v___x_1164_ = lean_float_of_nat(v___x_1163_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object* v_o_1165_){
_start:
{
double v_res_1166_; lean_object* v_r_1167_; 
v_res_1166_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1165_);
lean_dec_ref(v_o_1165_);
v_r_1167_ = lean_box_float(v_res_1166_);
return v_r_1167_;
}
}
static lean_object* _init_l_Lean_instMonadAlwaysExceptEIO___closed__0(void){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object* v_00_u03b5_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___closed__0, &l_Lean_instMonadAlwaysExceptEIO___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___closed__0);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object* v_inst_1171_, lean_object* v_always_1172_){
_start:
{
lean_object* v___f_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; 
lean_inc_ref(v_always_1172_);
v___f_1173_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1173_, 0, v_always_1172_);
lean_closure_set(v___f_1173_, 1, v_inst_1171_);
v___f_1174_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_1174_, 0, v_always_1172_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___f_1173_);
lean_ctor_set(v___x_1175_, 1, v___f_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object* v_m_1176_, lean_object* v_inst_1177_, lean_object* v_00_u03b5_1178_, lean_object* v_00_u03c3_1179_, lean_object* v_always_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_1177_, v_always_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object* v_always_1182_){
_start:
{
lean_object* v___f_1183_; lean_object* v___f_1184_; lean_object* v___x_1185_; 
lean_inc_ref(v_always_1182_);
v___f_1183_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1183_, 0, v_always_1182_);
v___f_1184_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1184_, 0, v_always_1182_);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___f_1183_);
lean_ctor_set(v___x_1185_, 1, v___f_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object* v_m_1186_, lean_object* v_00_u03b5_1187_, lean_object* v_00_u03c9_1188_, lean_object* v_00_u03c3_1189_, lean_object* v_always_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object* v_always_1192_){
_start:
{
lean_object* v___f_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; 
lean_inc_ref(v_always_1192_);
v___f_1193_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1193_, 0, v_always_1192_);
v___f_1194_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1194_, 0, v_always_1192_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___f_1193_);
lean_ctor_set(v___x_1195_, 1, v___f_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object* v_m_1196_, lean_object* v_00_u03b5_1197_, lean_object* v_00_u03c1_1198_, lean_object* v_always_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object* v_always_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1202_, v_inst_1203_, v_inst_1204_, v_always_1201_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object* v_00_u03b1_1206_, lean_object* v_m_1207_, lean_object* v_00_u03b5_1208_, lean_object* v_00_u03c9_1209_, lean_object* v_00_u03b2_1210_, lean_object* v_always_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1212_, v_inst_1213_, v_inst_1214_, v_always_1211_);
return v___x_1215_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___lam__0(lean_object* v_x_1222_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 0)
{
uint8_t v___x_1223_; 
v___x_1223_ = 2;
return v___x_1223_;
}
else
{
lean_object* v_a_1224_; uint8_t v___x_1225_; 
v_a_1224_ = lean_ctor_get(v_x_1222_, 0);
v___x_1225_ = lean_unbox(v_a_1224_);
if (v___x_1225_ == 0)
{
uint8_t v___x_1226_; 
v___x_1226_ = 1;
return v___x_1226_;
}
else
{
uint8_t v___x_1227_; 
v___x_1227_ = 0;
return v___x_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object* v_x_1228_){
_start:
{
uint8_t v_res_1229_; lean_object* v_r_1230_; 
v_res_1229_ = l_Lean_instExceptToTraceResultBool___lam__0(v_x_1228_);
lean_dec_ref(v_x_1228_);
v_r_1230_ = lean_box(v_res_1229_);
return v_r_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object* v_00_u03b5_1232_){
_start:
{
lean_object* v___f_1233_; 
v___f_1233_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___closed__0));
return v___f_1233_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___lam__0(lean_object* v_x_1234_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
uint8_t v___x_1235_; 
v___x_1235_ = 2;
return v___x_1235_;
}
else
{
lean_object* v_a_1236_; 
v_a_1236_ = lean_ctor_get(v_x_1234_, 0);
if (lean_obj_tag(v_a_1236_) == 0)
{
uint8_t v___x_1237_; 
v___x_1237_ = 1;
return v___x_1237_;
}
else
{
uint8_t v___x_1238_; 
v___x_1238_ = 0;
return v___x_1238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object* v_x_1239_){
_start:
{
uint8_t v_res_1240_; lean_object* v_r_1241_; 
v_res_1240_ = l_Lean_instExceptToTraceResultOption___lam__0(v_x_1239_);
lean_dec_ref(v_x_1239_);
v_r_1241_ = lean_box(v_res_1240_);
return v_r_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object* v_00_u03b1_1243_, lean_object* v_00_u03b5_1244_){
_start:
{
lean_object* v___f_1245_; 
v___f_1245_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___closed__0));
return v___f_1245_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultExpr___lam__0(lean_object* v_x_1246_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
uint8_t v___x_1247_; 
v___x_1247_ = 2;
return v___x_1247_;
}
else
{
lean_object* v_a_1248_; uint8_t v___x_1249_; 
v_a_1248_ = lean_ctor_get(v_x_1246_, 0);
v___x_1249_ = l_Lean_Expr_hasSyntheticSorry(v_a_1248_);
if (v___x_1249_ == 0)
{
uint8_t v___x_1250_; 
v___x_1250_ = 0;
return v___x_1250_;
}
else
{
uint8_t v___x_1251_; 
v___x_1251_ = 1;
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___lam__0___boxed(lean_object* v_x_1252_){
_start:
{
uint8_t v_res_1253_; lean_object* v_r_1254_; 
v_res_1253_ = l_Lean_instExceptToTraceResultExpr___lam__0(v_x_1252_);
lean_dec_ref(v_x_1252_);
v_r_1254_ = lean_box(v_res_1253_);
return v_r_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr(lean_object* v_00_u03b5_1256_){
_start:
{
lean_object* v___f_1257_; 
v___f_1257_ = ((lean_object*)(l_Lean_instExceptToTraceResultExpr___closed__0));
return v___f_1257_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
uint8_t v___x_1259_; 
v___x_1259_ = 2;
return v___x_1259_;
}
else
{
uint8_t v___x_1260_; 
v___x_1260_ = 0;
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object* v_x_1261_){
_start:
{
uint8_t v_res_1262_; lean_object* v_r_1263_; 
v_res_1262_ = l_Lean_instExceptToTraceResult___lam__0(v_x_1261_);
lean_dec_ref(v_x_1261_);
v_r_1263_ = lean_box(v_res_1262_);
return v_r_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object* v_00_u03b1_1265_, lean_object* v_00_u03b5_1266_){
_start:
{
lean_object* v___f_1267_; 
v___f_1267_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
return v___f_1267_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___redArg(lean_object* v_inst_1268_, lean_object* v_e_1269_){
_start:
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = lean_apply_1(v_inst_1268_, v_e_1269_);
v___x_1271_ = lean_unbox(v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___redArg___boxed(lean_object* v_inst_1272_, lean_object* v_e_1273_){
_start:
{
uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = l_Except_toTraceResult___redArg(v_inst_1272_, v_e_1273_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult(lean_object* v_00_u03b1_1276_, lean_object* v_00_u03b5_1277_, lean_object* v_inst_1278_, lean_object* v_e_1279_){
_start:
{
lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = lean_apply_1(v_inst_1278_, v_e_1279_);
v___x_1281_ = lean_unbox(v___x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_00_u03b5_1283_, lean_object* v_inst_1284_, lean_object* v_e_1285_){
_start:
{
uint8_t v_res_1286_; lean_object* v_r_1287_; 
v_res_1286_ = l_Except_toTraceResult(v_00_u03b1_1282_, v_00_u03b5_1283_, v_inst_1284_, v_e_1285_);
v_r_1287_ = lean_box(v_res_1286_);
return v_r_1287_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__0));
v___x_1290_ = l_Lean_stringToMessageData(v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object* v_inst_1291_, lean_object* v_x_1292_){
_start:
{
lean_object* v_toApplicative_1293_; lean_object* v_toPure_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_toApplicative_1293_ = lean_ctor_get(v_inst_1291_, 0);
lean_inc_ref(v_toApplicative_1293_);
lean_dec_ref(v_inst_1291_);
v_toPure_1294_ = lean_ctor_get(v_toApplicative_1293_, 1);
lean_inc(v_toPure_1294_);
lean_dec_ref(v_toApplicative_1293_);
v___x_1295_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___closed__1);
v___x_1296_ = lean_apply_2(v_toPure_1294_, lean_box(0), v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed(lean_object* v_inst_1297_, lean_object* v_x_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(v_inst_1297_, v_x_1298_);
lean_dec(v_x_1298_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object* v_oldTraces_1300_, lean_object* v_s_1301_){
_start:
{
uint64_t v_tid_1302_; lean_object* v_traces_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1311_; 
v_tid_1302_ = lean_ctor_get_uint64(v_s_1301_, sizeof(void*)*1);
v_traces_1303_ = lean_ctor_get(v_s_1301_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_s_1301_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1305_ = v_s_1301_;
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_traces_1303_);
lean_dec(v_s_1301_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1300_, v_traces_1303_);
lean_dec_ref(v_traces_1303_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1307_);
v___x_1309_ = v___x_1305_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
lean_ctor_set_uint64(v_reuseFailAlloc_1310_, sizeof(void*)*1, v_tid_1302_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object* v_always_1312_, lean_object* v_inst_1313_, lean_object* v_fst_1314_, lean_object* v_____r_1315_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1312_);
v___x_1317_ = l_MonadExcept_ofExcept___redArg(v_inst_1313_, v___x_1316_, v_fst_1314_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object* v_inst_1318_, lean_object* v___x_1319_, lean_object* v_fst_1320_, lean_object* v_____r_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_MonadExcept_ofExcept___redArg(v_inst_1318_, v___x_1319_, v_fst_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_oldTraces_1327_, lean_object* v_ref_1328_, lean_object* v_toBind_1329_, lean_object* v___f_1330_, lean_object* v_inst_1331_, lean_object* v_fst_1332_, lean_object* v_cls_1333_, uint8_t v_collapsed_1334_, lean_object* v_tag_1335_, uint8_t v___x_1336_, double v_fst_1337_, double v_snd_1338_, lean_object* v_m_1339_){
_start:
{
lean_object* v_data_1341_; lean_object* v_result_1344_; lean_object* v___x_1345_; double v___x_1346_; lean_object* v_data_1347_; 
v_result_1344_ = lean_apply_1(v_inst_1331_, v_fst_1332_);
v___x_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1345_, 0, v_result_1344_);
v___x_1346_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_1335_);
lean_inc_ref(v___x_1345_);
lean_inc(v_cls_1333_);
v_data_1347_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1347_, 0, v_cls_1333_);
lean_ctor_set(v_data_1347_, 1, v___x_1345_);
lean_ctor_set(v_data_1347_, 2, v_tag_1335_);
lean_ctor_set_float(v_data_1347_, sizeof(void*)*3, v___x_1346_);
lean_ctor_set_float(v_data_1347_, sizeof(void*)*3 + 8, v___x_1346_);
lean_ctor_set_uint8(v_data_1347_, sizeof(void*)*3 + 16, v_collapsed_1334_);
if (v___x_1336_ == 0)
{
lean_dec_ref_known(v___x_1345_, 1);
lean_dec_ref(v_tag_1335_);
lean_dec(v_cls_1333_);
v_data_1341_ = v_data_1347_;
goto v___jp_1340_;
}
else
{
lean_object* v_data_1348_; 
lean_dec_ref_known(v_data_1347_, 3);
v_data_1348_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1348_, 0, v_cls_1333_);
lean_ctor_set(v_data_1348_, 1, v___x_1345_);
lean_ctor_set(v_data_1348_, 2, v_tag_1335_);
lean_ctor_set_float(v_data_1348_, sizeof(void*)*3, v_fst_1337_);
lean_ctor_set_float(v_data_1348_, sizeof(void*)*3 + 8, v_snd_1338_);
lean_ctor_set_uint8(v_data_1348_, sizeof(void*)*3 + 16, v_collapsed_1334_);
v_data_1341_ = v_data_1348_;
goto v___jp_1340_;
}
v___jp_1340_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_1323_, v_inst_1324_, v_inst_1325_, v_inst_1326_, v_oldTraces_1327_, v_data_1341_, v_ref_1328_, v_m_1339_);
v___x_1343_ = lean_apply_4(v_toBind_1329_, lean_box(0), lean_box(0), v___x_1342_, v___f_1330_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_1349_ = _args[0];
lean_object* v_inst_1350_ = _args[1];
lean_object* v_inst_1351_ = _args[2];
lean_object* v_inst_1352_ = _args[3];
lean_object* v_oldTraces_1353_ = _args[4];
lean_object* v_ref_1354_ = _args[5];
lean_object* v_toBind_1355_ = _args[6];
lean_object* v___f_1356_ = _args[7];
lean_object* v_inst_1357_ = _args[8];
lean_object* v_fst_1358_ = _args[9];
lean_object* v_cls_1359_ = _args[10];
lean_object* v_collapsed_1360_ = _args[11];
lean_object* v_tag_1361_ = _args[12];
lean_object* v___x_1362_ = _args[13];
lean_object* v_fst_1363_ = _args[14];
lean_object* v_snd_1364_ = _args[15];
lean_object* v_m_1365_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1366_; uint8_t v___x_608__boxed_1367_; double v_fst_609__boxed_1368_; double v_snd_610__boxed_1369_; lean_object* v_res_1370_; 
v_collapsed_boxed_1366_ = lean_unbox(v_collapsed_1360_);
v___x_608__boxed_1367_ = lean_unbox(v___x_1362_);
v_fst_609__boxed_1368_ = lean_unbox_float(v_fst_1363_);
lean_dec_ref(v_fst_1363_);
v_snd_610__boxed_1369_ = lean_unbox_float(v_snd_1364_);
lean_dec_ref(v_snd_1364_);
v_res_1370_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1349_, v_inst_1350_, v_inst_1351_, v_inst_1352_, v_oldTraces_1353_, v_ref_1354_, v_toBind_1355_, v___f_1356_, v_inst_1357_, v_fst_1358_, v_cls_1359_, v_collapsed_boxed_1366_, v_tag_1361_, v___x_608__boxed_1367_, v_fst_609__boxed_1368_, v_snd_610__boxed_1369_, v_m_1365_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(lean_object* v_always_1371_, lean_object* v_inst_1372_, lean_object* v_fst_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_oldTraces_1377_, lean_object* v_toBind_1378_, lean_object* v_inst_1379_, lean_object* v_cls_1380_, uint8_t v_collapsed_1381_, lean_object* v_tag_1382_, uint8_t v___x_1383_, double v_fst_1384_, double v_snd_1385_, lean_object* v_msg_1386_, lean_object* v___f_1387_, lean_object* v_ref_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v_tryCatch_1390_; lean_object* v___f_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___f_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_inc_ref(v_always_1371_);
v___x_1389_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1371_);
v_tryCatch_1390_ = lean_ctor_get(v_always_1371_, 1);
lean_inc(v_tryCatch_1390_);
lean_dec_ref(v_always_1371_);
lean_inc_ref_n(v_fst_1373_, 2);
lean_inc_ref(v_inst_1372_);
v___f_1391_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1391_, 0, v_inst_1372_);
lean_closure_set(v___f_1391_, 1, v___x_1389_);
lean_closure_set(v___f_1391_, 2, v_fst_1373_);
v___x_1392_ = lean_box(v_collapsed_1381_);
v___x_1393_ = lean_box(v___x_1383_);
v___x_1394_ = lean_box_float(v_fst_1384_);
v___x_1395_ = lean_box_float(v_snd_1385_);
lean_inc(v_toBind_1378_);
v___f_1396_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1396_, 0, v_inst_1372_);
lean_closure_set(v___f_1396_, 1, v_inst_1374_);
lean_closure_set(v___f_1396_, 2, v_inst_1375_);
lean_closure_set(v___f_1396_, 3, v_inst_1376_);
lean_closure_set(v___f_1396_, 4, v_oldTraces_1377_);
lean_closure_set(v___f_1396_, 5, v_ref_1388_);
lean_closure_set(v___f_1396_, 6, v_toBind_1378_);
lean_closure_set(v___f_1396_, 7, v___f_1391_);
lean_closure_set(v___f_1396_, 8, v_inst_1379_);
lean_closure_set(v___f_1396_, 9, v_fst_1373_);
lean_closure_set(v___f_1396_, 10, v_cls_1380_);
lean_closure_set(v___f_1396_, 11, v___x_1392_);
lean_closure_set(v___f_1396_, 12, v_tag_1382_);
lean_closure_set(v___f_1396_, 13, v___x_1393_);
lean_closure_set(v___f_1396_, 14, v___x_1394_);
lean_closure_set(v___f_1396_, 15, v___x_1395_);
v___x_1397_ = lean_apply_1(v_msg_1386_, v_fst_1373_);
v___x_1398_ = lean_apply_3(v_tryCatch_1390_, lean_box(0), v___x_1397_, v___f_1387_);
v___x_1399_ = lean_apply_4(v_toBind_1378_, lean_box(0), lean_box(0), v___x_1398_, v___f_1396_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_always_1400_ = _args[0];
lean_object* v_inst_1401_ = _args[1];
lean_object* v_fst_1402_ = _args[2];
lean_object* v_inst_1403_ = _args[3];
lean_object* v_inst_1404_ = _args[4];
lean_object* v_inst_1405_ = _args[5];
lean_object* v_oldTraces_1406_ = _args[6];
lean_object* v_toBind_1407_ = _args[7];
lean_object* v_inst_1408_ = _args[8];
lean_object* v_cls_1409_ = _args[9];
lean_object* v_collapsed_1410_ = _args[10];
lean_object* v_tag_1411_ = _args[11];
lean_object* v___x_1412_ = _args[12];
lean_object* v_fst_1413_ = _args[13];
lean_object* v_snd_1414_ = _args[14];
lean_object* v_msg_1415_ = _args[15];
lean_object* v___f_1416_ = _args[16];
lean_object* v_ref_1417_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_1418_; uint8_t v___x_648__boxed_1419_; double v_fst_649__boxed_1420_; double v_snd_650__boxed_1421_; lean_object* v_res_1422_; 
v_collapsed_boxed_1418_ = lean_unbox(v_collapsed_1410_);
v___x_648__boxed_1419_ = lean_unbox(v___x_1412_);
v_fst_649__boxed_1420_ = lean_unbox_float(v_fst_1413_);
lean_dec_ref(v_fst_1413_);
v_snd_650__boxed_1421_ = lean_unbox_float(v_snd_1414_);
lean_dec_ref(v_snd_1414_);
v_res_1422_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5(v_always_1400_, v_inst_1401_, v_fst_1402_, v_inst_1403_, v_inst_1404_, v_inst_1405_, v_oldTraces_1406_, v_toBind_1407_, v_inst_1408_, v_cls_1409_, v_collapsed_boxed_1418_, v_tag_1411_, v___x_648__boxed_1419_, v_fst_649__boxed_1420_, v_snd_650__boxed_1421_, v_msg_1415_, v___f_1416_, v_ref_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_always_1427_, lean_object* v_inst_1428_, lean_object* v_cls_1429_, uint8_t v_collapsed_1430_, lean_object* v_tag_1431_, lean_object* v_opts_1432_, uint8_t v_clsEnabled_1433_, lean_object* v_oldTraces_1434_, lean_object* v_msg_1435_, lean_object* v_resStartStop_1436_){
_start:
{
lean_object* v___x_1437_; lean_object* v_snd_1438_; lean_object* v_fst_1439_; lean_object* v_fst_1440_; lean_object* v_snd_1441_; lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___y_1454_; double v___y_1460_; uint8_t v___x_1465_; 
v___x_1437_ = l_Lean_KVMap_instValueBool;
v_snd_1438_ = lean_ctor_get(v_resStartStop_1436_, 1);
lean_inc(v_snd_1438_);
v_fst_1439_ = lean_ctor_get(v_resStartStop_1436_, 0);
lean_inc_n(v_fst_1439_, 2);
lean_dec_ref(v_resStartStop_1436_);
v_fst_1440_ = lean_ctor_get(v_snd_1438_, 0);
lean_inc(v_fst_1440_);
v_snd_1441_ = lean_ctor_get(v_snd_1438_, 1);
lean_inc(v_snd_1441_);
lean_dec(v_snd_1438_);
lean_inc_ref_n(v_inst_1423_, 2);
v___f_1442_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1442_, 0, v_inst_1423_);
lean_inc_ref(v_oldTraces_1434_);
v___f_1443_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1443_, 0, v_oldTraces_1434_);
lean_inc_ref(v_always_1427_);
v___f_1444_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1444_, 0, v_always_1427_);
lean_closure_set(v___f_1444_, 1, v_inst_1423_);
lean_closure_set(v___f_1444_, 2, v_fst_1439_);
v___x_1445_ = l_Lean_trace_profiler;
v___x_1446_ = l_Lean_Option_get___redArg(v___x_1437_, v_opts_1432_, v___x_1445_);
v___x_1465_ = lean_unbox(v___x_1446_);
if (v___x_1465_ == 0)
{
uint8_t v___x_1466_; 
v___x_1466_ = lean_unbox(v___x_1446_);
v___y_1454_ = v___x_1466_;
goto v___jp_1453_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1468_ = l_Lean_Option_get___redArg(v___x_1437_, v_opts_1432_, v___x_1467_);
v___x_1469_ = lean_unbox(v___x_1468_);
lean_dec(v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; double v___x_1473_; double v___x_1474_; double v___x_1475_; 
v___x_1470_ = l_Lean_KVMap_instValueNat;
v___x_1471_ = l_Lean_trace_profiler_threshold;
v___x_1472_ = l_Lean_Option_get___redArg(v___x_1470_, v_opts_1432_, v___x_1471_);
v___x_1473_ = lean_float_of_nat(v___x_1472_);
v___x_1474_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1475_ = lean_float_div(v___x_1473_, v___x_1474_);
v___y_1460_ = v___x_1475_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; double v___x_1479_; 
v___x_1476_ = l_Lean_KVMap_instValueNat;
v___x_1477_ = l_Lean_trace_profiler_threshold;
v___x_1478_ = l_Lean_Option_get___redArg(v___x_1476_, v_opts_1432_, v___x_1477_);
v___x_1479_ = lean_float_of_nat(v___x_1478_);
v___y_1460_ = v___x_1479_;
goto v___jp_1459_;
}
}
v___jp_1447_:
{
lean_object* v_toBind_1448_; lean_object* v_getRef_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; 
v_toBind_1448_ = lean_ctor_get(v_inst_1423_, 1);
lean_inc_n(v_toBind_1448_, 2);
v_getRef_1449_ = lean_ctor_get(v_inst_1425_, 0);
lean_inc(v_getRef_1449_);
v___x_1450_ = lean_box(v_collapsed_1430_);
v___f_1451_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__5___boxed), 18, 17);
lean_closure_set(v___f_1451_, 0, v_always_1427_);
lean_closure_set(v___f_1451_, 1, v_inst_1423_);
lean_closure_set(v___f_1451_, 2, v_fst_1439_);
lean_closure_set(v___f_1451_, 3, v_inst_1424_);
lean_closure_set(v___f_1451_, 4, v_inst_1425_);
lean_closure_set(v___f_1451_, 5, v_inst_1426_);
lean_closure_set(v___f_1451_, 6, v_oldTraces_1434_);
lean_closure_set(v___f_1451_, 7, v_toBind_1448_);
lean_closure_set(v___f_1451_, 8, v_inst_1428_);
lean_closure_set(v___f_1451_, 9, v_cls_1429_);
lean_closure_set(v___f_1451_, 10, v___x_1450_);
lean_closure_set(v___f_1451_, 11, v_tag_1431_);
lean_closure_set(v___f_1451_, 12, v___x_1446_);
lean_closure_set(v___f_1451_, 13, v_fst_1440_);
lean_closure_set(v___f_1451_, 14, v_snd_1441_);
lean_closure_set(v___f_1451_, 15, v_msg_1435_);
lean_closure_set(v___f_1451_, 16, v___f_1442_);
v___x_1452_ = lean_apply_4(v_toBind_1448_, lean_box(0), lean_box(0), v_getRef_1449_, v___f_1451_);
return v___x_1452_;
}
v___jp_1453_:
{
if (v_clsEnabled_1433_ == 0)
{
if (v___y_1454_ == 0)
{
lean_object* v_toBind_1455_; lean_object* v_modifyTraceState_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec(v___x_1446_);
lean_dec_ref(v___f_1442_);
lean_dec(v_snd_1441_);
lean_dec(v_fst_1440_);
lean_dec(v_fst_1439_);
lean_dec(v_msg_1435_);
lean_dec_ref(v_oldTraces_1434_);
lean_dec_ref(v_tag_1431_);
lean_dec(v_cls_1429_);
lean_dec_ref(v_inst_1428_);
lean_dec_ref(v_always_1427_);
lean_dec(v_inst_1426_);
lean_dec_ref(v_inst_1425_);
v_toBind_1455_ = lean_ctor_get(v_inst_1423_, 1);
lean_inc(v_toBind_1455_);
lean_dec_ref(v_inst_1423_);
v_modifyTraceState_1456_ = lean_ctor_get(v_inst_1424_, 0);
lean_inc(v_modifyTraceState_1456_);
lean_dec_ref(v_inst_1424_);
v___x_1457_ = lean_apply_1(v_modifyTraceState_1456_, v___f_1443_);
v___x_1458_ = lean_apply_4(v_toBind_1455_, lean_box(0), lean_box(0), v___x_1457_, v___f_1444_);
return v___x_1458_;
}
else
{
lean_dec_ref(v___f_1444_);
lean_dec_ref(v___f_1443_);
goto v___jp_1447_;
}
}
else
{
lean_dec_ref(v___f_1444_);
lean_dec_ref(v___f_1443_);
goto v___jp_1447_;
}
}
v___jp_1459_:
{
double v___x_1461_; double v___x_1462_; double v___x_1463_; uint8_t v___x_1464_; 
v___x_1461_ = lean_unbox_float(v_snd_1441_);
v___x_1462_ = lean_unbox_float(v_fst_1440_);
v___x_1463_ = lean_float_sub(v___x_1461_, v___x_1462_);
v___x_1464_ = lean_float_decLt(v___y_1460_, v___x_1463_);
v___y_1454_ = v___x_1464_;
goto v___jp_1453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_inst_1483_, lean_object* v_always_1484_, lean_object* v_inst_1485_, lean_object* v_cls_1486_, lean_object* v_collapsed_1487_, lean_object* v_tag_1488_, lean_object* v_opts_1489_, lean_object* v_clsEnabled_1490_, lean_object* v_oldTraces_1491_, lean_object* v_msg_1492_, lean_object* v_resStartStop_1493_){
_start:
{
uint8_t v_collapsed_boxed_1494_; uint8_t v_clsEnabled_boxed_1495_; lean_object* v_res_1496_; 
v_collapsed_boxed_1494_ = lean_unbox(v_collapsed_1487_);
v_clsEnabled_boxed_1495_ = lean_unbox(v_clsEnabled_1490_);
v_res_1496_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1480_, v_inst_1481_, v_inst_1482_, v_inst_1483_, v_always_1484_, v_inst_1485_, v_cls_1486_, v_collapsed_boxed_1494_, v_tag_1488_, v_opts_1489_, v_clsEnabled_boxed_1495_, v_oldTraces_1491_, v_msg_1492_, v_resStartStop_1493_);
lean_dec_ref(v_opts_1489_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object* v_00_u03b1_1497_, lean_object* v_m_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_00_u03b5_1503_, lean_object* v_always_1504_, lean_object* v_inst_1505_, lean_object* v_cls_1506_, uint8_t v_collapsed_1507_, lean_object* v_tag_1508_, lean_object* v_opts_1509_, uint8_t v_clsEnabled_1510_, lean_object* v_oldTraces_1511_, lean_object* v_msg_1512_, lean_object* v_resStartStop_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1499_, v_inst_1500_, v_inst_1501_, v_inst_1502_, v_always_1504_, v_inst_1505_, v_cls_1506_, v_collapsed_1507_, v_tag_1508_, v_opts_1509_, v_clsEnabled_1510_, v_oldTraces_1511_, v_msg_1512_, v_resStartStop_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_1515_ = _args[0];
lean_object* v_m_1516_ = _args[1];
lean_object* v_inst_1517_ = _args[2];
lean_object* v_inst_1518_ = _args[3];
lean_object* v_inst_1519_ = _args[4];
lean_object* v_inst_1520_ = _args[5];
lean_object* v_00_u03b5_1521_ = _args[6];
lean_object* v_always_1522_ = _args[7];
lean_object* v_inst_1523_ = _args[8];
lean_object* v_cls_1524_ = _args[9];
lean_object* v_collapsed_1525_ = _args[10];
lean_object* v_tag_1526_ = _args[11];
lean_object* v_opts_1527_ = _args[12];
lean_object* v_clsEnabled_1528_ = _args[13];
lean_object* v_oldTraces_1529_ = _args[14];
lean_object* v_msg_1530_ = _args[15];
lean_object* v_resStartStop_1531_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1532_; uint8_t v_clsEnabled_boxed_1533_; lean_object* v_res_1534_; 
v_collapsed_boxed_1532_ = lean_unbox(v_collapsed_1525_);
v_clsEnabled_boxed_1533_ = lean_unbox(v_clsEnabled_1528_);
v_res_1534_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(v_00_u03b1_1515_, v_m_1516_, v_inst_1517_, v_inst_1518_, v_inst_1519_, v_inst_1520_, v_00_u03b5_1521_, v_always_1522_, v_inst_1523_, v_cls_1524_, v_collapsed_boxed_1532_, v_tag_1526_, v_opts_1527_, v_clsEnabled_boxed_1533_, v_oldTraces_1529_, v_msg_1530_, v_resStartStop_1531_);
lean_dec_ref(v_opts_1527_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object* v_inst_1535_, lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_always_1539_, lean_object* v_inst_1540_, lean_object* v_cls_1541_, uint8_t v_collapsed_1542_, lean_object* v_tag_1543_, lean_object* v_opts_1544_, uint8_t v_clsEnabled_1545_, lean_object* v_oldTraces_1546_, lean_object* v_msg_1547_, lean_object* v_resStartStop_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1535_, v_inst_1536_, v_inst_1537_, v_inst_1538_, v_always_1539_, v_inst_1540_, v_cls_1541_, v_collapsed_1542_, v_tag_1543_, v_opts_1544_, v_clsEnabled_1545_, v_oldTraces_1546_, v_msg_1547_, v_resStartStop_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_always_1554_, lean_object* v_inst_1555_, lean_object* v_cls_1556_, lean_object* v_collapsed_1557_, lean_object* v_tag_1558_, lean_object* v_opts_1559_, lean_object* v_clsEnabled_1560_, lean_object* v_oldTraces_1561_, lean_object* v_msg_1562_, lean_object* v_resStartStop_1563_){
_start:
{
uint8_t v_collapsed_boxed_1564_; uint8_t v_clsEnabled_boxed_1565_; lean_object* v_res_1566_; 
v_collapsed_boxed_1564_ = lean_unbox(v_collapsed_1557_);
v_clsEnabled_boxed_1565_ = lean_unbox(v_clsEnabled_1560_);
v_res_1566_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1550_, v_inst_1551_, v_inst_1552_, v_inst_1553_, v_always_1554_, v_inst_1555_, v_cls_1556_, v_collapsed_boxed_1564_, v_tag_1558_, v_opts_1559_, v_clsEnabled_boxed_1565_, v_oldTraces_1561_, v_msg_1562_, v_resStartStop_1563_);
lean_dec_ref(v_opts_1559_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object* v_toPure_1567_, lean_object* v_ex_1568_){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_ex_1568_);
v___x_1570_ = lean_apply_2(v_toPure_1567_, lean_box(0), v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object* v_toPure_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_a_1572_);
v___x_1574_ = lean_apply_2(v_toPure_1571_, lean_box(0), v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object* v_start_1575_, lean_object* v_a_1576_, lean_object* v_toPure_1577_, lean_object* v_stop_1578_){
_start:
{
double v___x_1579_; double v___x_1580_; double v___x_1581_; double v___x_1582_; double v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1579_ = lean_float_of_nat(v_start_1575_);
v___x_1580_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1581_ = lean_float_div(v___x_1579_, v___x_1580_);
v___x_1582_ = lean_float_of_nat(v_stop_1578_);
v___x_1583_ = lean_float_div(v___x_1582_, v___x_1580_);
v___x_1584_ = lean_box_float(v___x_1581_);
v___x_1585_ = lean_box_float(v___x_1583_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v_a_1576_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_apply_2(v_toPure_1577_, lean_box(0), v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object* v_start_1589_, lean_object* v_toPure_1590_, lean_object* v_toBind_1591_, lean_object* v___x_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v___f_1594_; lean_object* v___x_1595_; 
v___f_1594_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1594_, 0, v_start_1589_);
lean_closure_set(v___f_1594_, 1, v_a_1593_);
lean_closure_set(v___f_1594_, 2, v_toPure_1590_);
v___x_1595_ = lean_apply_4(v_toBind_1591_, lean_box(0), lean_box(0), v___x_1592_, v___f_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object* v_toPure_1596_, lean_object* v_toBind_1597_, lean_object* v___x_1598_, lean_object* v___x_1599_, lean_object* v_start_1600_){
_start:
{
lean_object* v___f_1601_; lean_object* v___x_1602_; 
lean_inc(v_toBind_1597_);
v___f_1601_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1601_, 0, v_start_1600_);
lean_closure_set(v___f_1601_, 1, v_toPure_1596_);
lean_closure_set(v___f_1601_, 2, v_toBind_1597_);
lean_closure_set(v___f_1601_, 3, v___x_1598_);
v___x_1602_ = lean_apply_4(v_toBind_1597_, lean_box(0), lean_box(0), v___x_1599_, v___f_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object* v_start_1603_, lean_object* v_a_1604_, lean_object* v_toPure_1605_, lean_object* v_stop_1606_){
_start:
{
double v___x_1607_; double v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1607_ = lean_float_of_nat(v_start_1603_);
v___x_1608_ = lean_float_of_nat(v_stop_1606_);
v___x_1609_ = lean_box_float(v___x_1607_);
v___x_1610_ = lean_box_float(v___x_1608_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v_a_1604_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_apply_2(v_toPure_1605_, lean_box(0), v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object* v_start_1614_, lean_object* v_toPure_1615_, lean_object* v_toBind_1616_, lean_object* v___x_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v___f_1619_; lean_object* v___x_1620_; 
v___f_1619_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__6), 4, 3);
lean_closure_set(v___f_1619_, 0, v_start_1614_);
lean_closure_set(v___f_1619_, 1, v_a_1618_);
lean_closure_set(v___f_1619_, 2, v_toPure_1615_);
v___x_1620_ = lean_apply_4(v_toBind_1616_, lean_box(0), lean_box(0), v___x_1617_, v___f_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object* v_toPure_1621_, lean_object* v_toBind_1622_, lean_object* v___x_1623_, lean_object* v___x_1624_, lean_object* v_start_1625_){
_start:
{
lean_object* v___f_1626_; lean_object* v___x_1627_; 
lean_inc(v_toBind_1622_);
v___f_1626_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1626_, 0, v_start_1625_);
lean_closure_set(v___f_1626_, 1, v_toPure_1621_);
lean_closure_set(v___f_1626_, 2, v_toBind_1622_);
lean_closure_set(v___f_1626_, 3, v___x_1623_);
v___x_1627_ = lean_apply_4(v_toBind_1622_, lean_box(0), lean_box(0), v___x_1624_, v___f_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object* v_always_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_cls_1634_, uint8_t v_collapsed_1635_, lean_object* v_tag_1636_, lean_object* v_opts_1637_, uint8_t v_clsEnabled_1638_, lean_object* v_msg_1639_, lean_object* v_toPure_1640_, lean_object* v_toBind_1641_, lean_object* v_k_1642_, lean_object* v_inst_1643_, lean_object* v_oldTraces_1644_){
_start:
{
lean_object* v_tryCatch_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___f_1648_; lean_object* v___f_1649_; lean_object* v___f_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v_tryCatch_1645_ = lean_ctor_get(v_always_1628_, 1);
lean_inc(v_tryCatch_1645_);
v___x_1646_ = lean_box(v_collapsed_1635_);
v___x_1647_ = lean_box(v_clsEnabled_1638_);
lean_inc_ref(v_opts_1637_);
v___f_1648_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1648_, 0, v_inst_1629_);
lean_closure_set(v___f_1648_, 1, v_inst_1630_);
lean_closure_set(v___f_1648_, 2, v_inst_1631_);
lean_closure_set(v___f_1648_, 3, v_inst_1632_);
lean_closure_set(v___f_1648_, 4, v_always_1628_);
lean_closure_set(v___f_1648_, 5, v_inst_1633_);
lean_closure_set(v___f_1648_, 6, v_cls_1634_);
lean_closure_set(v___f_1648_, 7, v___x_1646_);
lean_closure_set(v___f_1648_, 8, v_tag_1636_);
lean_closure_set(v___f_1648_, 9, v_opts_1637_);
lean_closure_set(v___f_1648_, 10, v___x_1647_);
lean_closure_set(v___f_1648_, 11, v_oldTraces_1644_);
lean_closure_set(v___f_1648_, 12, v_msg_1639_);
lean_inc_n(v_toPure_1640_, 2);
v___f_1649_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1649_, 0, v_toPure_1640_);
v___f_1650_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1650_, 0, v_toPure_1640_);
lean_inc(v_toBind_1641_);
v___x_1651_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v_k_1642_, v___f_1650_);
v___x_1652_ = lean_apply_3(v_tryCatch_1645_, lean_box(0), v___x_1651_, v___f_1649_);
v___x_1653_ = l_Lean_KVMap_instValueBool;
v___x_1654_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1655_ = l_Lean_Option_get___redArg(v___x_1653_, v_opts_1637_, v___x_1654_);
lean_dec_ref(v_opts_1637_);
v___x_1656_ = lean_unbox(v___x_1655_);
lean_dec(v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___f_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1657_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1658_ = lean_apply_2(v_inst_1643_, lean_box(0), v___x_1657_);
lean_inc(v___x_1658_);
lean_inc_n(v_toBind_1641_, 2);
v___f_1659_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1659_, 0, v_toPure_1640_);
lean_closure_set(v___f_1659_, 1, v_toBind_1641_);
lean_closure_set(v___f_1659_, 2, v___x_1658_);
lean_closure_set(v___f_1659_, 3, v___x_1652_);
v___x_1660_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v___x_1658_, v___f_1659_);
v___x_1661_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v___x_1660_, v___f_1648_);
return v___x_1661_;
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1662_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1663_ = lean_apply_2(v_inst_1643_, lean_box(0), v___x_1662_);
lean_inc(v___x_1663_);
lean_inc_n(v_toBind_1641_, 2);
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_1664_, 0, v_toPure_1640_);
lean_closure_set(v___f_1664_, 1, v_toBind_1641_);
lean_closure_set(v___f_1664_, 2, v___x_1663_);
lean_closure_set(v___f_1664_, 3, v___x_1652_);
v___x_1665_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v___x_1663_, v___f_1664_);
v___x_1666_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v___x_1665_, v___f_1648_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_always_1667_ = _args[0];
lean_object* v_inst_1668_ = _args[1];
lean_object* v_inst_1669_ = _args[2];
lean_object* v_inst_1670_ = _args[3];
lean_object* v_inst_1671_ = _args[4];
lean_object* v_inst_1672_ = _args[5];
lean_object* v_cls_1673_ = _args[6];
lean_object* v_collapsed_1674_ = _args[7];
lean_object* v_tag_1675_ = _args[8];
lean_object* v_opts_1676_ = _args[9];
lean_object* v_clsEnabled_1677_ = _args[10];
lean_object* v_msg_1678_ = _args[11];
lean_object* v_toPure_1679_ = _args[12];
lean_object* v_toBind_1680_ = _args[13];
lean_object* v_k_1681_ = _args[14];
lean_object* v_inst_1682_ = _args[15];
lean_object* v_oldTraces_1683_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1684_; uint8_t v_clsEnabled_boxed_1685_; lean_object* v_res_1686_; 
v_collapsed_boxed_1684_ = lean_unbox(v_collapsed_1674_);
v_clsEnabled_boxed_1685_ = lean_unbox(v_clsEnabled_1677_);
v_res_1686_ = l_Lean_withTraceNode___redArg___lam__9(v_always_1667_, v_inst_1668_, v_inst_1669_, v_inst_1670_, v_inst_1671_, v_inst_1672_, v_cls_1673_, v_collapsed_boxed_1684_, v_tag_1675_, v_opts_1676_, v_clsEnabled_boxed_1685_, v_msg_1678_, v_toPure_1679_, v_toBind_1680_, v_k_1681_, v_inst_1682_, v_oldTraces_1683_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object* v_always_1687_, lean_object* v_inst_1688_, lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_cls_1693_, uint8_t v_collapsed_1694_, lean_object* v_tag_1695_, lean_object* v_opts_1696_, lean_object* v_msg_1697_, lean_object* v_toPure_1698_, lean_object* v_toBind_1699_, lean_object* v_k_1700_, lean_object* v_inst_1701_, uint8_t v_clsEnabled_1702_){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___f_1705_; 
v___x_1703_ = lean_box(v_collapsed_1694_);
v___x_1704_ = lean_box(v_clsEnabled_1702_);
lean_inc(v_k_1700_);
lean_inc(v_toBind_1699_);
lean_inc_ref(v_opts_1696_);
lean_inc_ref(v_inst_1689_);
lean_inc_ref(v_inst_1688_);
v___f_1705_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__9___boxed), 17, 16);
lean_closure_set(v___f_1705_, 0, v_always_1687_);
lean_closure_set(v___f_1705_, 1, v_inst_1688_);
lean_closure_set(v___f_1705_, 2, v_inst_1689_);
lean_closure_set(v___f_1705_, 3, v_inst_1690_);
lean_closure_set(v___f_1705_, 4, v_inst_1691_);
lean_closure_set(v___f_1705_, 5, v_inst_1692_);
lean_closure_set(v___f_1705_, 6, v_cls_1693_);
lean_closure_set(v___f_1705_, 7, v___x_1703_);
lean_closure_set(v___f_1705_, 8, v_tag_1695_);
lean_closure_set(v___f_1705_, 9, v_opts_1696_);
lean_closure_set(v___f_1705_, 10, v___x_1704_);
lean_closure_set(v___f_1705_, 11, v_msg_1697_);
lean_closure_set(v___f_1705_, 12, v_toPure_1698_);
lean_closure_set(v___f_1705_, 13, v_toBind_1699_);
lean_closure_set(v___f_1705_, 14, v_k_1700_);
lean_closure_set(v___f_1705_, 15, v_inst_1701_);
if (v_clsEnabled_1702_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1709_ = l_Lean_KVMap_instValueBool;
v___x_1710_ = l_Lean_trace_profiler;
v___x_1711_ = l_Lean_Option_get___redArg(v___x_1709_, v_opts_1696_, v___x_1710_);
lean_dec_ref(v_opts_1696_);
v___x_1712_ = lean_unbox(v___x_1711_);
lean_dec(v___x_1711_);
if (v___x_1712_ == 0)
{
lean_dec_ref(v___f_1705_);
lean_dec(v_toBind_1699_);
lean_dec_ref(v_inst_1689_);
lean_dec_ref(v_inst_1688_);
return v_k_1700_;
}
else
{
lean_dec(v_k_1700_);
goto v___jp_1706_;
}
}
else
{
lean_dec(v_k_1700_);
lean_dec_ref(v_opts_1696_);
goto v___jp_1706_;
}
v___jp_1706_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1688_, v_inst_1689_);
v___x_1708_ = lean_apply_4(v_toBind_1699_, lean_box(0), lean_box(0), v___x_1707_, v___f_1705_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object* v_always_1713_, lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_cls_1719_, lean_object* v_collapsed_1720_, lean_object* v_tag_1721_, lean_object* v_opts_1722_, lean_object* v_msg_1723_, lean_object* v_toPure_1724_, lean_object* v_toBind_1725_, lean_object* v_k_1726_, lean_object* v_inst_1727_, lean_object* v_clsEnabled_1728_){
_start:
{
uint8_t v_collapsed_boxed_1729_; uint8_t v_clsEnabled_boxed_1730_; lean_object* v_res_1731_; 
v_collapsed_boxed_1729_ = lean_unbox(v_collapsed_1720_);
v_clsEnabled_boxed_1730_ = lean_unbox(v_clsEnabled_1728_);
v_res_1731_ = l_Lean_withTraceNode___redArg___lam__10(v_always_1713_, v_inst_1714_, v_inst_1715_, v_inst_1716_, v_inst_1717_, v_inst_1718_, v_cls_1719_, v_collapsed_boxed_1729_, v_tag_1721_, v_opts_1722_, v_msg_1723_, v_toPure_1724_, v_toBind_1725_, v_k_1726_, v_inst_1727_, v_clsEnabled_boxed_1730_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object* v_k_1732_, lean_object* v_inst_1733_, lean_object* v_toApplicative_1734_, lean_object* v_always_1735_, lean_object* v_inst_1736_, lean_object* v_inst_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_cls_1740_, uint8_t v_collapsed_1741_, lean_object* v_tag_1742_, lean_object* v_msg_1743_, lean_object* v_toBind_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_opts_1747_){
_start:
{
uint8_t v_hasTrace_1748_; 
v_hasTrace_1748_ = lean_ctor_get_uint8(v_opts_1747_, sizeof(void*)*1);
if (v_hasTrace_1748_ == 0)
{
lean_dec_ref(v_opts_1747_);
lean_dec(v_inst_1746_);
lean_dec(v_inst_1745_);
lean_dec(v_toBind_1744_);
lean_dec(v_msg_1743_);
lean_dec_ref(v_tag_1742_);
lean_dec(v_cls_1740_);
lean_dec_ref(v_inst_1739_);
lean_dec(v_inst_1738_);
lean_dec_ref(v_inst_1737_);
lean_dec_ref(v_inst_1736_);
lean_dec_ref(v_always_1735_);
lean_dec_ref(v_toApplicative_1734_);
lean_dec_ref(v_inst_1733_);
return v_k_1732_;
}
else
{
lean_object* v_getInheritedTraceOptions_1749_; lean_object* v_toPure_1750_; lean_object* v___x_1751_; lean_object* v___f_1752_; lean_object* v___f_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_getInheritedTraceOptions_1749_ = lean_ctor_get(v_inst_1733_, 2);
lean_inc(v_getInheritedTraceOptions_1749_);
v_toPure_1750_ = lean_ctor_get(v_toApplicative_1734_, 1);
lean_inc_n(v_toPure_1750_, 2);
lean_dec_ref(v_toApplicative_1734_);
v___x_1751_ = lean_box(v_collapsed_1741_);
lean_inc_n(v_toBind_1744_, 3);
lean_inc(v_cls_1740_);
v___f_1752_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__10___boxed), 16, 15);
lean_closure_set(v___f_1752_, 0, v_always_1735_);
lean_closure_set(v___f_1752_, 1, v_inst_1736_);
lean_closure_set(v___f_1752_, 2, v_inst_1733_);
lean_closure_set(v___f_1752_, 3, v_inst_1737_);
lean_closure_set(v___f_1752_, 4, v_inst_1738_);
lean_closure_set(v___f_1752_, 5, v_inst_1739_);
lean_closure_set(v___f_1752_, 6, v_cls_1740_);
lean_closure_set(v___f_1752_, 7, v___x_1751_);
lean_closure_set(v___f_1752_, 8, v_tag_1742_);
lean_closure_set(v___f_1752_, 9, v_opts_1747_);
lean_closure_set(v___f_1752_, 10, v_msg_1743_);
lean_closure_set(v___f_1752_, 11, v_toPure_1750_);
lean_closure_set(v___f_1752_, 12, v_toBind_1744_);
lean_closure_set(v___f_1752_, 13, v_k_1732_);
lean_closure_set(v___f_1752_, 14, v_inst_1745_);
v___f_1753_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1753_, 0, v_toPure_1750_);
lean_closure_set(v___f_1753_, 1, v_cls_1740_);
lean_closure_set(v___f_1753_, 2, v_toBind_1744_);
lean_closure_set(v___f_1753_, 3, v_inst_1746_);
v___x_1754_ = lean_apply_4(v_toBind_1744_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1749_, v___f_1753_);
v___x_1755_ = lean_apply_4(v_toBind_1744_, lean_box(0), lean_box(0), v___x_1754_, v___f_1752_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13___boxed(lean_object* v_k_1756_, lean_object* v_inst_1757_, lean_object* v_toApplicative_1758_, lean_object* v_always_1759_, lean_object* v_inst_1760_, lean_object* v_inst_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_cls_1764_, lean_object* v_collapsed_1765_, lean_object* v_tag_1766_, lean_object* v_msg_1767_, lean_object* v_toBind_1768_, lean_object* v_inst_1769_, lean_object* v_inst_1770_, lean_object* v_opts_1771_){
_start:
{
uint8_t v_collapsed_boxed_1772_; lean_object* v_res_1773_; 
v_collapsed_boxed_1772_ = lean_unbox(v_collapsed_1765_);
v_res_1773_ = l_Lean_withTraceNode___redArg___lam__13(v_k_1756_, v_inst_1757_, v_toApplicative_1758_, v_always_1759_, v_inst_1760_, v_inst_1761_, v_inst_1762_, v_inst_1763_, v_cls_1764_, v_collapsed_boxed_1772_, v_tag_1766_, v_msg_1767_, v_toBind_1768_, v_inst_1769_, v_inst_1770_, v_opts_1771_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_always_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_cls_1782_, lean_object* v_msg_1783_, lean_object* v_k_1784_, uint8_t v_collapsed_1785_, lean_object* v_tag_1786_){
_start:
{
lean_object* v_toApplicative_1787_; lean_object* v_toBind_1788_; lean_object* v___x_1789_; lean_object* v___f_1790_; lean_object* v___x_1791_; 
v_toApplicative_1787_ = lean_ctor_get(v_inst_1774_, 0);
lean_inc_ref(v_toApplicative_1787_);
v_toBind_1788_ = lean_ctor_get(v_inst_1774_, 1);
lean_inc_n(v_toBind_1788_, 2);
v___x_1789_ = lean_box(v_collapsed_1785_);
lean_inc(v_inst_1778_);
v___f_1790_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1790_, 0, v_k_1784_);
lean_closure_set(v___f_1790_, 1, v_inst_1775_);
lean_closure_set(v___f_1790_, 2, v_toApplicative_1787_);
lean_closure_set(v___f_1790_, 3, v_always_1779_);
lean_closure_set(v___f_1790_, 4, v_inst_1774_);
lean_closure_set(v___f_1790_, 5, v_inst_1776_);
lean_closure_set(v___f_1790_, 6, v_inst_1777_);
lean_closure_set(v___f_1790_, 7, v_inst_1781_);
lean_closure_set(v___f_1790_, 8, v_cls_1782_);
lean_closure_set(v___f_1790_, 9, v___x_1789_);
lean_closure_set(v___f_1790_, 10, v_tag_1786_);
lean_closure_set(v___f_1790_, 11, v_msg_1783_);
lean_closure_set(v___f_1790_, 12, v_toBind_1788_);
lean_closure_set(v___f_1790_, 13, v_inst_1780_);
lean_closure_set(v___f_1790_, 14, v_inst_1778_);
v___x_1791_ = lean_apply_4(v_toBind_1788_, lean_box(0), lean_box(0), v_inst_1778_, v___f_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_always_1797_, lean_object* v_inst_1798_, lean_object* v_inst_1799_, lean_object* v_cls_1800_, lean_object* v_msg_1801_, lean_object* v_k_1802_, lean_object* v_collapsed_1803_, lean_object* v_tag_1804_){
_start:
{
uint8_t v_collapsed_boxed_1805_; lean_object* v_res_1806_; 
v_collapsed_boxed_1805_ = lean_unbox(v_collapsed_1803_);
v_res_1806_ = l_Lean_withTraceNode___redArg(v_inst_1792_, v_inst_1793_, v_inst_1794_, v_inst_1795_, v_inst_1796_, v_always_1797_, v_inst_1798_, v_inst_1799_, v_cls_1800_, v_msg_1801_, v_k_1802_, v_collapsed_boxed_1805_, v_tag_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object* v_00_u03b1_1807_, lean_object* v_m_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_00_u03b5_1814_, lean_object* v_always_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_cls_1818_, lean_object* v_msg_1819_, lean_object* v_k_1820_, uint8_t v_collapsed_1821_, lean_object* v_tag_1822_){
_start:
{
lean_object* v_toApplicative_1823_; lean_object* v_toBind_1824_; lean_object* v___x_1825_; lean_object* v___f_1826_; lean_object* v___x_1827_; 
v_toApplicative_1823_ = lean_ctor_get(v_inst_1809_, 0);
lean_inc_ref(v_toApplicative_1823_);
v_toBind_1824_ = lean_ctor_get(v_inst_1809_, 1);
lean_inc_n(v_toBind_1824_, 2);
v___x_1825_ = lean_box(v_collapsed_1821_);
lean_inc(v_inst_1813_);
v___f_1826_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 16, 15);
lean_closure_set(v___f_1826_, 0, v_k_1820_);
lean_closure_set(v___f_1826_, 1, v_inst_1810_);
lean_closure_set(v___f_1826_, 2, v_toApplicative_1823_);
lean_closure_set(v___f_1826_, 3, v_always_1815_);
lean_closure_set(v___f_1826_, 4, v_inst_1809_);
lean_closure_set(v___f_1826_, 5, v_inst_1811_);
lean_closure_set(v___f_1826_, 6, v_inst_1812_);
lean_closure_set(v___f_1826_, 7, v_inst_1817_);
lean_closure_set(v___f_1826_, 8, v_cls_1818_);
lean_closure_set(v___f_1826_, 9, v___x_1825_);
lean_closure_set(v___f_1826_, 10, v_tag_1822_);
lean_closure_set(v___f_1826_, 11, v_msg_1819_);
lean_closure_set(v___f_1826_, 12, v_toBind_1824_);
lean_closure_set(v___f_1826_, 13, v_inst_1816_);
lean_closure_set(v___f_1826_, 14, v_inst_1813_);
v___x_1827_ = lean_apply_4(v_toBind_1824_, lean_box(0), lean_box(0), v_inst_1813_, v___f_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object* v_00_u03b1_1828_, lean_object* v_m_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_00_u03b5_1835_, lean_object* v_always_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_, lean_object* v_cls_1839_, lean_object* v_msg_1840_, lean_object* v_k_1841_, lean_object* v_collapsed_1842_, lean_object* v_tag_1843_){
_start:
{
uint8_t v_collapsed_boxed_1844_; lean_object* v_res_1845_; 
v_collapsed_boxed_1844_ = lean_unbox(v_collapsed_1842_);
v_res_1845_ = l_Lean_withTraceNode(v_00_u03b1_1828_, v_m_1829_, v_inst_1830_, v_inst_1831_, v_inst_1832_, v_inst_1833_, v_inst_1834_, v_00_u03b5_1835_, v_always_1836_, v_inst_1837_, v_inst_1838_, v_cls_1839_, v_msg_1840_, v_k_1841_, v_collapsed_boxed_1844_, v_tag_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object* v_self_1846_){
_start:
{
lean_object* v_fst_1847_; 
v_fst_1847_ = lean_ctor_get(v_self_1846_, 0);
lean_inc(v_fst_1847_);
return v_fst_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object* v_self_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_1848_);
lean_dec_ref(v_self_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object* v_toPure_1850_, lean_object* v_x_1851_){
_start:
{
if (lean_obj_tag(v_x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v_a_1852_ = lean_ctor_get(v_x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref_known(v_x_1851_, 1);
v___x_1853_ = l_Lean_Exception_toMessageData(v_a_1852_);
v___x_1854_ = lean_apply_2(v_toPure_1850_, lean_box(0), v___x_1853_);
return v___x_1854_;
}
else
{
lean_object* v_a_1855_; lean_object* v_snd_1856_; lean_object* v___x_1857_; 
v_a_1855_ = lean_ctor_get(v_x_1851_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v_x_1851_, 1);
v_snd_1856_ = lean_ctor_get(v_a_1855_, 1);
lean_inc(v_snd_1856_);
lean_dec(v_a_1855_);
v___x_1857_ = lean_apply_2(v_toPure_1850_, lean_box(0), v_snd_1856_);
return v___x_1857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object* v_toPure_1858_, lean_object* v_ex_1859_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_ex_1859_);
v___x_1861_ = lean_apply_2(v_toPure_1858_, lean_box(0), v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object* v_toPure_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_a_1863_);
v___x_1865_ = lean_apply_2(v_toPure_1862_, lean_box(0), v___x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v___f_1871_, lean_object* v_cls_1872_, uint8_t v_collapsed_1873_, lean_object* v_tag_1874_, lean_object* v_opts_1875_, uint8_t v_clsEnabled_1876_, lean_object* v_oldTraces_1877_, lean_object* v_msg_1878_, lean_object* v_resStartStop_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1866_, v_inst_1867_, v_inst_1868_, v_inst_1869_, v_inst_1870_, v___f_1871_, v_cls_1872_, v_collapsed_1873_, v_tag_1874_, v_opts_1875_, v_clsEnabled_1876_, v_oldTraces_1877_, v_msg_1878_, v_resStartStop_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3___boxed(lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_inst_1883_, lean_object* v_inst_1884_, lean_object* v_inst_1885_, lean_object* v___f_1886_, lean_object* v_cls_1887_, lean_object* v_collapsed_1888_, lean_object* v_tag_1889_, lean_object* v_opts_1890_, lean_object* v_clsEnabled_1891_, lean_object* v_oldTraces_1892_, lean_object* v_msg_1893_, lean_object* v_resStartStop_1894_){
_start:
{
uint8_t v_collapsed_boxed_1895_; uint8_t v_clsEnabled_boxed_1896_; lean_object* v_res_1897_; 
v_collapsed_boxed_1895_ = lean_unbox(v_collapsed_1888_);
v_clsEnabled_boxed_1896_ = lean_unbox(v_clsEnabled_1891_);
v_res_1897_ = l_Lean_withTraceNode_x27___redArg___lam__3(v_inst_1881_, v_inst_1882_, v_inst_1883_, v_inst_1884_, v_inst_1885_, v___f_1886_, v_cls_1887_, v_collapsed_boxed_1895_, v_tag_1889_, v_opts_1890_, v_clsEnabled_boxed_1896_, v_oldTraces_1892_, v_msg_1893_, v_resStartStop_1894_);
lean_dec_ref(v_opts_1890_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object* v_start_1898_, lean_object* v_a_1899_, lean_object* v_toPure_1900_, lean_object* v_stop_1901_){
_start:
{
double v___x_1902_; double v___x_1903_; double v___x_1904_; double v___x_1905_; double v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1902_ = lean_float_of_nat(v_start_1898_);
v___x_1903_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1904_ = lean_float_div(v___x_1902_, v___x_1903_);
v___x_1905_ = lean_float_of_nat(v_stop_1901_);
v___x_1906_ = lean_float_div(v___x_1905_, v___x_1903_);
v___x_1907_ = lean_box_float(v___x_1904_);
v___x_1908_ = lean_box_float(v___x_1906_);
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_a_1899_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_apply_2(v_toPure_1900_, lean_box(0), v___x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object* v_start_1912_, lean_object* v_toPure_1913_, lean_object* v_toBind_1914_, lean_object* v___x_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v___f_1917_; lean_object* v___x_1918_; 
v___f_1917_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__5), 4, 3);
lean_closure_set(v___f_1917_, 0, v_start_1912_);
lean_closure_set(v___f_1917_, 1, v_a_1916_);
lean_closure_set(v___f_1917_, 2, v_toPure_1913_);
v___x_1918_ = lean_apply_4(v_toBind_1914_, lean_box(0), lean_box(0), v___x_1915_, v___f_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object* v_toPure_1919_, lean_object* v_toBind_1920_, lean_object* v___x_1921_, lean_object* v___x_1922_, lean_object* v_start_1923_){
_start:
{
lean_object* v___f_1924_; lean_object* v___x_1925_; 
lean_inc(v_toBind_1920_);
v___f_1924_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__6), 5, 4);
lean_closure_set(v___f_1924_, 0, v_start_1923_);
lean_closure_set(v___f_1924_, 1, v_toPure_1919_);
lean_closure_set(v___f_1924_, 2, v_toBind_1920_);
lean_closure_set(v___f_1924_, 3, v___x_1921_);
v___x_1925_ = lean_apply_4(v_toBind_1920_, lean_box(0), lean_box(0), v___x_1922_, v___f_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object* v_start_1926_, lean_object* v_a_1927_, lean_object* v_toPure_1928_, lean_object* v_stop_1929_){
_start:
{
double v___x_1930_; double v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1930_ = lean_float_of_nat(v_start_1926_);
v___x_1931_ = lean_float_of_nat(v_stop_1929_);
v___x_1932_ = lean_box_float(v___x_1930_);
v___x_1933_ = lean_box_float(v___x_1931_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v_a_1927_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_apply_2(v_toPure_1928_, lean_box(0), v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object* v_start_1937_, lean_object* v_toPure_1938_, lean_object* v_toBind_1939_, lean_object* v___x_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v___f_1942_; lean_object* v___x_1943_; 
v___f_1942_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__8), 4, 3);
lean_closure_set(v___f_1942_, 0, v_start_1937_);
lean_closure_set(v___f_1942_, 1, v_a_1941_);
lean_closure_set(v___f_1942_, 2, v_toPure_1938_);
v___x_1943_ = lean_apply_4(v_toBind_1939_, lean_box(0), lean_box(0), v___x_1940_, v___f_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object* v_toPure_1944_, lean_object* v_toBind_1945_, lean_object* v___x_1946_, lean_object* v___x_1947_, lean_object* v_start_1948_){
_start:
{
lean_object* v___f_1949_; lean_object* v___x_1950_; 
lean_inc(v_toBind_1945_);
v___f_1949_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__9), 5, 4);
lean_closure_set(v___f_1949_, 0, v_start_1948_);
lean_closure_set(v___f_1949_, 1, v_toPure_1944_);
lean_closure_set(v___f_1949_, 2, v_toBind_1945_);
lean_closure_set(v___f_1949_, 3, v___x_1946_);
v___x_1950_ = lean_apply_4(v_toBind_1945_, lean_box(0), lean_box(0), v___x_1947_, v___f_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v___f_1956_, lean_object* v_cls_1957_, uint8_t v_collapsed_1958_, lean_object* v_tag_1959_, lean_object* v_opts_1960_, uint8_t v_clsEnabled_1961_, lean_object* v_msg_1962_, lean_object* v_toBind_1963_, lean_object* v_k_1964_, lean_object* v___f_1965_, lean_object* v___f_1966_, lean_object* v_inst_1967_, lean_object* v_toPure_1968_, lean_object* v_oldTraces_1969_){
_start:
{
lean_object* v_tryCatch_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___f_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v_tryCatch_1970_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc(v_tryCatch_1970_);
v___x_1971_ = lean_box(v_collapsed_1958_);
v___x_1972_ = lean_box(v_clsEnabled_1961_);
lean_inc_ref(v_opts_1960_);
v___f_1973_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_1973_, 0, v_inst_1952_);
lean_closure_set(v___f_1973_, 1, v_inst_1953_);
lean_closure_set(v___f_1973_, 2, v_inst_1954_);
lean_closure_set(v___f_1973_, 3, v_inst_1955_);
lean_closure_set(v___f_1973_, 4, v_inst_1951_);
lean_closure_set(v___f_1973_, 5, v___f_1956_);
lean_closure_set(v___f_1973_, 6, v_cls_1957_);
lean_closure_set(v___f_1973_, 7, v___x_1971_);
lean_closure_set(v___f_1973_, 8, v_tag_1959_);
lean_closure_set(v___f_1973_, 9, v_opts_1960_);
lean_closure_set(v___f_1973_, 10, v___x_1972_);
lean_closure_set(v___f_1973_, 11, v_oldTraces_1969_);
lean_closure_set(v___f_1973_, 12, v_msg_1962_);
lean_inc(v_toBind_1963_);
v___x_1974_ = lean_apply_4(v_toBind_1963_, lean_box(0), lean_box(0), v_k_1964_, v___f_1965_);
v___x_1975_ = lean_apply_3(v_tryCatch_1970_, lean_box(0), v___x_1974_, v___f_1966_);
v___x_1976_ = l_Lean_KVMap_instValueBool;
v___x_1977_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1978_ = l_Lean_Option_get___redArg(v___x_1976_, v_opts_1960_, v___x_1977_);
lean_dec_ref(v_opts_1960_);
v___x_1979_ = lean_unbox(v___x_1978_);
lean_dec(v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___f_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1980_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1981_ = lean_apply_2(v_inst_1967_, lean_box(0), v___x_1980_);
lean_inc(v___x_1981_);
lean_inc_n(v_toBind_1963_, 2);
v___f_1982_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1982_, 0, v_toPure_1968_);
lean_closure_set(v___f_1982_, 1, v_toBind_1963_);
lean_closure_set(v___f_1982_, 2, v___x_1981_);
lean_closure_set(v___f_1982_, 3, v___x_1975_);
v___x_1983_ = lean_apply_4(v_toBind_1963_, lean_box(0), lean_box(0), v___x_1981_, v___f_1982_);
v___x_1984_ = lean_apply_4(v_toBind_1963_, lean_box(0), lean_box(0), v___x_1983_, v___f_1973_);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___f_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1985_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1986_ = lean_apply_2(v_inst_1967_, lean_box(0), v___x_1985_);
lean_inc(v___x_1986_);
lean_inc_n(v_toBind_1963_, 2);
v___f_1987_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__10), 5, 4);
lean_closure_set(v___f_1987_, 0, v_toPure_1968_);
lean_closure_set(v___f_1987_, 1, v_toBind_1963_);
lean_closure_set(v___f_1987_, 2, v___x_1986_);
lean_closure_set(v___f_1987_, 3, v___x_1975_);
v___x_1988_ = lean_apply_4(v_toBind_1963_, lean_box(0), lean_box(0), v___x_1986_, v___f_1987_);
v___x_1989_ = lean_apply_4(v_toBind_1963_, lean_box(0), lean_box(0), v___x_1988_, v___f_1973_);
return v___x_1989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_1990_ = _args[0];
lean_object* v_inst_1991_ = _args[1];
lean_object* v_inst_1992_ = _args[2];
lean_object* v_inst_1993_ = _args[3];
lean_object* v_inst_1994_ = _args[4];
lean_object* v___f_1995_ = _args[5];
lean_object* v_cls_1996_ = _args[6];
lean_object* v_collapsed_1997_ = _args[7];
lean_object* v_tag_1998_ = _args[8];
lean_object* v_opts_1999_ = _args[9];
lean_object* v_clsEnabled_2000_ = _args[10];
lean_object* v_msg_2001_ = _args[11];
lean_object* v_toBind_2002_ = _args[12];
lean_object* v_k_2003_ = _args[13];
lean_object* v___f_2004_ = _args[14];
lean_object* v___f_2005_ = _args[15];
lean_object* v_inst_2006_ = _args[16];
lean_object* v_toPure_2007_ = _args[17];
lean_object* v_oldTraces_2008_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_2009_; uint8_t v_clsEnabled_boxed_2010_; lean_object* v_res_2011_; 
v_collapsed_boxed_2009_ = lean_unbox(v_collapsed_1997_);
v_clsEnabled_boxed_2010_ = lean_unbox(v_clsEnabled_2000_);
v_res_2011_ = l_Lean_withTraceNode_x27___redArg___lam__11(v_inst_1990_, v_inst_1991_, v_inst_1992_, v_inst_1993_, v_inst_1994_, v___f_1995_, v_cls_1996_, v_collapsed_boxed_2009_, v_tag_1998_, v_opts_1999_, v_clsEnabled_boxed_2010_, v_msg_2001_, v_toBind_2002_, v_k_2003_, v___f_2004_, v___f_2005_, v_inst_2006_, v_toPure_2007_, v_oldTraces_2008_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v___f_2017_, lean_object* v_cls_2018_, uint8_t v_collapsed_2019_, lean_object* v_tag_2020_, lean_object* v_opts_2021_, lean_object* v_msg_2022_, lean_object* v_toBind_2023_, lean_object* v_k_2024_, lean_object* v___f_2025_, lean_object* v___f_2026_, lean_object* v_inst_2027_, lean_object* v_toPure_2028_, uint8_t v_clsEnabled_2029_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___f_2032_; 
v___x_2030_ = lean_box(v_collapsed_2019_);
v___x_2031_ = lean_box(v_clsEnabled_2029_);
lean_inc(v_k_2024_);
lean_inc(v_toBind_2023_);
lean_inc_ref(v_opts_2021_);
lean_inc_ref(v_inst_2014_);
lean_inc_ref(v_inst_2013_);
v___f_2032_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__11___boxed), 19, 18);
lean_closure_set(v___f_2032_, 0, v_inst_2012_);
lean_closure_set(v___f_2032_, 1, v_inst_2013_);
lean_closure_set(v___f_2032_, 2, v_inst_2014_);
lean_closure_set(v___f_2032_, 3, v_inst_2015_);
lean_closure_set(v___f_2032_, 4, v_inst_2016_);
lean_closure_set(v___f_2032_, 5, v___f_2017_);
lean_closure_set(v___f_2032_, 6, v_cls_2018_);
lean_closure_set(v___f_2032_, 7, v___x_2030_);
lean_closure_set(v___f_2032_, 8, v_tag_2020_);
lean_closure_set(v___f_2032_, 9, v_opts_2021_);
lean_closure_set(v___f_2032_, 10, v___x_2031_);
lean_closure_set(v___f_2032_, 11, v_msg_2022_);
lean_closure_set(v___f_2032_, 12, v_toBind_2023_);
lean_closure_set(v___f_2032_, 13, v_k_2024_);
lean_closure_set(v___f_2032_, 14, v___f_2025_);
lean_closure_set(v___f_2032_, 15, v___f_2026_);
lean_closure_set(v___f_2032_, 16, v_inst_2027_);
lean_closure_set(v___f_2032_, 17, v_toPure_2028_);
if (v_clsEnabled_2029_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2036_ = l_Lean_KVMap_instValueBool;
v___x_2037_ = l_Lean_trace_profiler;
v___x_2038_ = l_Lean_Option_get___redArg(v___x_2036_, v_opts_2021_, v___x_2037_);
lean_dec_ref(v_opts_2021_);
v___x_2039_ = lean_unbox(v___x_2038_);
lean_dec(v___x_2038_);
if (v___x_2039_ == 0)
{
lean_dec_ref(v___f_2032_);
lean_dec(v_toBind_2023_);
lean_dec_ref(v_inst_2014_);
lean_dec_ref(v_inst_2013_);
return v_k_2024_;
}
else
{
lean_dec(v_k_2024_);
goto v___jp_2033_;
}
}
else
{
lean_dec(v_k_2024_);
lean_dec_ref(v_opts_2021_);
goto v___jp_2033_;
}
v___jp_2033_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_2013_, v_inst_2014_);
v___x_2035_ = lean_apply_4(v_toBind_2023_, lean_box(0), lean_box(0), v___x_2034_, v___f_2032_);
return v___x_2035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_inst_2040_ = _args[0];
lean_object* v_inst_2041_ = _args[1];
lean_object* v_inst_2042_ = _args[2];
lean_object* v_inst_2043_ = _args[3];
lean_object* v_inst_2044_ = _args[4];
lean_object* v___f_2045_ = _args[5];
lean_object* v_cls_2046_ = _args[6];
lean_object* v_collapsed_2047_ = _args[7];
lean_object* v_tag_2048_ = _args[8];
lean_object* v_opts_2049_ = _args[9];
lean_object* v_msg_2050_ = _args[10];
lean_object* v_toBind_2051_ = _args[11];
lean_object* v_k_2052_ = _args[12];
lean_object* v___f_2053_ = _args[13];
lean_object* v___f_2054_ = _args[14];
lean_object* v_inst_2055_ = _args[15];
lean_object* v_toPure_2056_ = _args[16];
lean_object* v_clsEnabled_2057_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2058_; uint8_t v_clsEnabled_boxed_2059_; lean_object* v_res_2060_; 
v_collapsed_boxed_2058_ = lean_unbox(v_collapsed_2047_);
v_clsEnabled_boxed_2059_ = lean_unbox(v_clsEnabled_2057_);
v_res_2060_ = l_Lean_withTraceNode_x27___redArg___lam__12(v_inst_2040_, v_inst_2041_, v_inst_2042_, v_inst_2043_, v_inst_2044_, v___f_2045_, v_cls_2046_, v_collapsed_boxed_2058_, v_tag_2048_, v_opts_2049_, v_msg_2050_, v_toBind_2051_, v_k_2052_, v___f_2053_, v___f_2054_, v_inst_2055_, v_toPure_2056_, v_clsEnabled_boxed_2059_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object* v_k_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_inst_2066_, lean_object* v___f_2067_, lean_object* v_cls_2068_, uint8_t v_collapsed_2069_, lean_object* v_tag_2070_, lean_object* v_msg_2071_, lean_object* v_toBind_2072_, lean_object* v___f_2073_, lean_object* v___f_2074_, lean_object* v_inst_2075_, lean_object* v_toPure_2076_, lean_object* v___f_2077_, lean_object* v_opts_2078_){
_start:
{
uint8_t v_hasTrace_2079_; 
v_hasTrace_2079_ = lean_ctor_get_uint8(v_opts_2078_, sizeof(void*)*1);
if (v_hasTrace_2079_ == 0)
{
lean_dec_ref(v_opts_2078_);
lean_dec(v___f_2077_);
lean_dec(v_toPure_2076_);
lean_dec(v_inst_2075_);
lean_dec(v___f_2074_);
lean_dec(v___f_2073_);
lean_dec(v_toBind_2072_);
lean_dec(v_msg_2071_);
lean_dec_ref(v_tag_2070_);
lean_dec(v_cls_2068_);
lean_dec_ref(v___f_2067_);
lean_dec(v_inst_2066_);
lean_dec_ref(v_inst_2065_);
lean_dec_ref(v_inst_2064_);
lean_dec_ref(v_inst_2063_);
lean_dec_ref(v_inst_2062_);
return v_k_2061_;
}
else
{
lean_object* v_getInheritedTraceOptions_2080_; lean_object* v___x_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_getInheritedTraceOptions_2080_ = lean_ctor_get(v_inst_2062_, 2);
lean_inc(v_getInheritedTraceOptions_2080_);
v___x_2081_ = lean_box(v_collapsed_2069_);
lean_inc_n(v_toBind_2072_, 2);
v___f_2082_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__12___boxed), 18, 17);
lean_closure_set(v___f_2082_, 0, v_inst_2063_);
lean_closure_set(v___f_2082_, 1, v_inst_2064_);
lean_closure_set(v___f_2082_, 2, v_inst_2062_);
lean_closure_set(v___f_2082_, 3, v_inst_2065_);
lean_closure_set(v___f_2082_, 4, v_inst_2066_);
lean_closure_set(v___f_2082_, 5, v___f_2067_);
lean_closure_set(v___f_2082_, 6, v_cls_2068_);
lean_closure_set(v___f_2082_, 7, v___x_2081_);
lean_closure_set(v___f_2082_, 8, v_tag_2070_);
lean_closure_set(v___f_2082_, 9, v_opts_2078_);
lean_closure_set(v___f_2082_, 10, v_msg_2071_);
lean_closure_set(v___f_2082_, 11, v_toBind_2072_);
lean_closure_set(v___f_2082_, 12, v_k_2061_);
lean_closure_set(v___f_2082_, 13, v___f_2073_);
lean_closure_set(v___f_2082_, 14, v___f_2074_);
lean_closure_set(v___f_2082_, 15, v_inst_2075_);
lean_closure_set(v___f_2082_, 16, v_toPure_2076_);
v___x_2083_ = lean_apply_4(v_toBind_2072_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2080_, v___f_2077_);
v___x_2084_ = lean_apply_4(v_toBind_2072_, lean_box(0), lean_box(0), v___x_2083_, v___f_2082_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_k_2085_ = _args[0];
lean_object* v_inst_2086_ = _args[1];
lean_object* v_inst_2087_ = _args[2];
lean_object* v_inst_2088_ = _args[3];
lean_object* v_inst_2089_ = _args[4];
lean_object* v_inst_2090_ = _args[5];
lean_object* v___f_2091_ = _args[6];
lean_object* v_cls_2092_ = _args[7];
lean_object* v_collapsed_2093_ = _args[8];
lean_object* v_tag_2094_ = _args[9];
lean_object* v_msg_2095_ = _args[10];
lean_object* v_toBind_2096_ = _args[11];
lean_object* v___f_2097_ = _args[12];
lean_object* v___f_2098_ = _args[13];
lean_object* v_inst_2099_ = _args[14];
lean_object* v_toPure_2100_ = _args[15];
lean_object* v___f_2101_ = _args[16];
lean_object* v_opts_2102_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2103_; lean_object* v_res_2104_; 
v_collapsed_boxed_2103_ = lean_unbox(v_collapsed_2093_);
v_res_2104_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_k_2085_, v_inst_2086_, v_inst_2087_, v_inst_2088_, v_inst_2089_, v_inst_2090_, v___f_2091_, v_cls_2092_, v_collapsed_boxed_2103_, v_tag_2094_, v_msg_2095_, v_toBind_2096_, v___f_2097_, v___f_2098_, v_inst_2099_, v_toPure_2100_, v___f_2101_, v_opts_2102_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_cls_2113_, lean_object* v_k_2114_, uint8_t v_collapsed_2115_, lean_object* v_tag_2116_){
_start:
{
lean_object* v_toApplicative_2117_; lean_object* v_toFunctor_2118_; lean_object* v_toBind_2119_; lean_object* v_toPure_2120_; lean_object* v_map_2121_; lean_object* v___f_2122_; lean_object* v_msg_2123_; lean_object* v___f_2124_; lean_object* v___f_2125_; lean_object* v___f_2126_; lean_object* v___f_2127_; lean_object* v___x_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_toApplicative_2117_ = lean_ctor_get(v_inst_2106_, 0);
v_toFunctor_2118_ = lean_ctor_get(v_toApplicative_2117_, 0);
v_toBind_2119_ = lean_ctor_get(v_inst_2106_, 1);
lean_inc_n(v_toBind_2119_, 3);
v_toPure_2120_ = lean_ctor_get(v_toApplicative_2117_, 1);
lean_inc_n(v_toPure_2120_, 5);
v_map_2121_ = lean_ctor_get(v_toFunctor_2118_, 0);
lean_inc(v_map_2121_);
v___f_2122_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2123_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2123_, 0, v_toPure_2120_);
lean_inc(v_inst_2110_);
lean_inc(v_cls_2113_);
v___f_2124_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2124_, 0, v_toPure_2120_);
lean_closure_set(v___f_2124_, 1, v_cls_2113_);
lean_closure_set(v___f_2124_, 2, v_toBind_2119_);
lean_closure_set(v___f_2124_, 3, v_inst_2110_);
v___f_2125_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2125_, 0, v_toPure_2120_);
v___f_2126_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2126_, 0, v_toPure_2120_);
v___f_2127_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2128_ = lean_box(v_collapsed_2115_);
v___f_2129_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2129_, 0, v_k_2114_);
lean_closure_set(v___f_2129_, 1, v_inst_2107_);
lean_closure_set(v___f_2129_, 2, v_inst_2111_);
lean_closure_set(v___f_2129_, 3, v_inst_2106_);
lean_closure_set(v___f_2129_, 4, v_inst_2108_);
lean_closure_set(v___f_2129_, 5, v_inst_2109_);
lean_closure_set(v___f_2129_, 6, v___f_2127_);
lean_closure_set(v___f_2129_, 7, v_cls_2113_);
lean_closure_set(v___f_2129_, 8, v___x_2128_);
lean_closure_set(v___f_2129_, 9, v_tag_2116_);
lean_closure_set(v___f_2129_, 10, v_msg_2123_);
lean_closure_set(v___f_2129_, 11, v_toBind_2119_);
lean_closure_set(v___f_2129_, 12, v___f_2126_);
lean_closure_set(v___f_2129_, 13, v___f_2125_);
lean_closure_set(v___f_2129_, 14, v_inst_2112_);
lean_closure_set(v___f_2129_, 15, v_toPure_2120_);
lean_closure_set(v___f_2129_, 16, v___f_2124_);
v___x_2130_ = lean_apply_4(v_toBind_2119_, lean_box(0), lean_box(0), v_inst_2110_, v___f_2129_);
v___x_2131_ = lean_apply_4(v_map_2121_, lean_box(0), lean_box(0), v___f_2122_, v___x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_cls_2139_, lean_object* v_k_2140_, lean_object* v_collapsed_2141_, lean_object* v_tag_2142_){
_start:
{
uint8_t v_collapsed_boxed_2143_; lean_object* v_res_2144_; 
v_collapsed_boxed_2143_ = lean_unbox(v_collapsed_2141_);
v_res_2144_ = l_Lean_withTraceNode_x27___redArg(v_inst_2132_, v_inst_2133_, v_inst_2134_, v_inst_2135_, v_inst_2136_, v_inst_2137_, v_inst_2138_, v_cls_2139_, v_k_2140_, v_collapsed_boxed_2143_, v_tag_2142_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object* v_00_u03b1_2145_, lean_object* v_m_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_inst_2150_, lean_object* v_inst_2151_, lean_object* v_inst_2152_, lean_object* v_inst_2153_, lean_object* v_cls_2154_, lean_object* v_k_2155_, uint8_t v_collapsed_2156_, lean_object* v_tag_2157_){
_start:
{
lean_object* v_toApplicative_2158_; lean_object* v_toFunctor_2159_; lean_object* v_toBind_2160_; lean_object* v_toPure_2161_; lean_object* v_map_2162_; lean_object* v___f_2163_; lean_object* v_msg_2164_; lean_object* v___f_2165_; lean_object* v___f_2166_; lean_object* v___f_2167_; lean_object* v___f_2168_; lean_object* v___x_2169_; lean_object* v___f_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_toApplicative_2158_ = lean_ctor_get(v_inst_2147_, 0);
v_toFunctor_2159_ = lean_ctor_get(v_toApplicative_2158_, 0);
v_toBind_2160_ = lean_ctor_get(v_inst_2147_, 1);
lean_inc_n(v_toBind_2160_, 3);
v_toPure_2161_ = lean_ctor_get(v_toApplicative_2158_, 1);
lean_inc_n(v_toPure_2161_, 5);
v_map_2162_ = lean_ctor_get(v_toFunctor_2159_, 0);
lean_inc(v_map_2162_);
v___f_2163_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2164_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2164_, 0, v_toPure_2161_);
lean_inc(v_inst_2151_);
lean_inc(v_cls_2154_);
v___f_2165_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2165_, 0, v_toPure_2161_);
lean_closure_set(v___f_2165_, 1, v_cls_2154_);
lean_closure_set(v___f_2165_, 2, v_toBind_2160_);
lean_closure_set(v___f_2165_, 3, v_inst_2151_);
v___f_2166_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2166_, 0, v_toPure_2161_);
v___f_2167_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2167_, 0, v_toPure_2161_);
v___f_2168_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2169_ = lean_box(v_collapsed_2156_);
v___f_2170_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 18, 17);
lean_closure_set(v___f_2170_, 0, v_k_2155_);
lean_closure_set(v___f_2170_, 1, v_inst_2148_);
lean_closure_set(v___f_2170_, 2, v_inst_2152_);
lean_closure_set(v___f_2170_, 3, v_inst_2147_);
lean_closure_set(v___f_2170_, 4, v_inst_2149_);
lean_closure_set(v___f_2170_, 5, v_inst_2150_);
lean_closure_set(v___f_2170_, 6, v___f_2168_);
lean_closure_set(v___f_2170_, 7, v_cls_2154_);
lean_closure_set(v___f_2170_, 8, v___x_2169_);
lean_closure_set(v___f_2170_, 9, v_tag_2157_);
lean_closure_set(v___f_2170_, 10, v_msg_2164_);
lean_closure_set(v___f_2170_, 11, v_toBind_2160_);
lean_closure_set(v___f_2170_, 12, v___f_2167_);
lean_closure_set(v___f_2170_, 13, v___f_2166_);
lean_closure_set(v___f_2170_, 14, v_inst_2153_);
lean_closure_set(v___f_2170_, 15, v_toPure_2161_);
lean_closure_set(v___f_2170_, 16, v___f_2165_);
v___x_2171_ = lean_apply_4(v_toBind_2160_, lean_box(0), lean_box(0), v_inst_2151_, v___f_2170_);
v___x_2172_ = lean_apply_4(v_map_2162_, lean_box(0), lean_box(0), v___f_2163_, v___x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object* v_00_u03b1_2173_, lean_object* v_m_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_inst_2179_, lean_object* v_inst_2180_, lean_object* v_inst_2181_, lean_object* v_cls_2182_, lean_object* v_k_2183_, lean_object* v_collapsed_2184_, lean_object* v_tag_2185_){
_start:
{
uint8_t v_collapsed_boxed_2186_; lean_object* v_res_2187_; 
v_collapsed_boxed_2186_ = lean_unbox(v_collapsed_2184_);
v_res_2187_ = l_Lean_withTraceNode_x27(v_00_u03b1_2173_, v_m_2174_, v_inst_2175_, v_inst_2176_, v_inst_2177_, v_inst_2178_, v_inst_2179_, v_inst_2180_, v_inst_2181_, v_cls_2182_, v_k_2183_, v_collapsed_boxed_2186_, v_tag_2185_);
return v_res_2187_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__4(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__3));
v___x_2197_ = l_Lean_mkAtom(v___x_2196_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__5(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__4, &l_Lean_registerTraceClass___auto__1___closed__4_once, _init_l_Lean_registerTraceClass___auto__1___closed__4);
v___x_2199_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2200_ = lean_array_push(v___x_2199_, v___x_2198_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__6(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2201_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__5, &l_Lean_registerTraceClass___auto__1___closed__5_once, _init_l_Lean_registerTraceClass___auto__1___closed__5);
v___x_2202_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__2));
v___x_2203_ = lean_box(2);
v___x_2204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v___x_2202_);
lean_ctor_set(v___x_2204_, 2, v___x_2201_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__7(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__6, &l_Lean_registerTraceClass___auto__1___closed__6_once, _init_l_Lean_registerTraceClass___auto__1___closed__6);
v___x_2206_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_2207_ = lean_array_push(v___x_2206_, v___x_2205_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2208_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__7, &l_Lean_registerTraceClass___auto__1___closed__7_once, _init_l_Lean_registerTraceClass___auto__1___closed__7);
v___x_2209_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_2210_ = lean_box(2);
v___x_2211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v___x_2209_);
lean_ctor_set(v___x_2211_, 2, v___x_2208_);
return v___x_2211_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__8, &l_Lean_registerTraceClass___auto__1___closed__8_once, _init_l_Lean_registerTraceClass___auto__1___closed__8);
v___x_2213_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2214_ = lean_array_push(v___x_2213_, v___x_2212_);
return v___x_2214_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2215_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__9, &l_Lean_registerTraceClass___auto__1___closed__9_once, _init_l_Lean_registerTraceClass___auto__1___closed__9);
v___x_2216_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2217_ = lean_box(2);
v___x_2218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v___x_2216_);
lean_ctor_set(v___x_2218_, 2, v___x_2215_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__11(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__10, &l_Lean_registerTraceClass___auto__1___closed__10_once, _init_l_Lean_registerTraceClass___auto__1___closed__10);
v___x_2220_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2221_ = lean_array_push(v___x_2220_, v___x_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2222_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__11, &l_Lean_registerTraceClass___auto__1___closed__11_once, _init_l_Lean_registerTraceClass___auto__1___closed__11);
v___x_2223_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_2224_ = lean_box(2);
v___x_2225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set(v___x_2225_, 1, v___x_2223_);
lean_ctor_set(v___x_2225_, 2, v___x_2222_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__12, &l_Lean_registerTraceClass___auto__1___closed__12_once, _init_l_Lean_registerTraceClass___auto__1___closed__12);
v___x_2227_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2228_ = lean_array_push(v___x_2227_, v___x_2226_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2229_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__13, &l_Lean_registerTraceClass___auto__1___closed__13_once, _init_l_Lean_registerTraceClass___auto__1___closed__13);
v___x_2230_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_2231_ = lean_box(2);
v___x_2232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2230_);
lean_ctor_set(v___x_2232_, 2, v___x_2229_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1(void){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__14, &l_Lean_registerTraceClass___auto__1___closed__14_once, _init_l_Lean_registerTraceClass___auto__1___closed__14);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2234_, lean_object* v_x_2235_){
_start:
{
if (lean_obj_tag(v_x_2235_) == 0)
{
return v_x_2234_;
}
else
{
lean_object* v_key_2236_; lean_object* v_value_2237_; lean_object* v_tail_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2264_; 
v_key_2236_ = lean_ctor_get(v_x_2235_, 0);
v_value_2237_ = lean_ctor_get(v_x_2235_, 1);
v_tail_2238_ = lean_ctor_get(v_x_2235_, 2);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_x_2235_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2240_ = v_x_2235_;
v_isShared_2241_ = v_isSharedCheck_2264_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_tail_2238_);
lean_inc(v_value_2237_);
lean_inc(v_key_2236_);
lean_dec(v_x_2235_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2264_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; uint64_t v___y_2244_; 
v___x_2242_ = lean_array_get_size(v_x_2234_);
if (lean_obj_tag(v_key_2236_) == 0)
{
uint64_t v___x_2262_; 
v___x_2262_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2244_ = v___x_2262_;
goto v___jp_2243_;
}
else
{
uint64_t v_hash_2263_; 
v_hash_2263_ = lean_ctor_get_uint64(v_key_2236_, sizeof(void*)*2);
v___y_2244_ = v_hash_2263_;
goto v___jp_2243_;
}
v___jp_2243_:
{
uint64_t v___x_2245_; uint64_t v___x_2246_; uint64_t v_fold_2247_; uint64_t v___x_2248_; uint64_t v___x_2249_; uint64_t v___x_2250_; size_t v___x_2251_; size_t v___x_2252_; size_t v___x_2253_; size_t v___x_2254_; size_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2245_ = 32ULL;
v___x_2246_ = lean_uint64_shift_right(v___y_2244_, v___x_2245_);
v_fold_2247_ = lean_uint64_xor(v___y_2244_, v___x_2246_);
v___x_2248_ = 16ULL;
v___x_2249_ = lean_uint64_shift_right(v_fold_2247_, v___x_2248_);
v___x_2250_ = lean_uint64_xor(v_fold_2247_, v___x_2249_);
v___x_2251_ = lean_uint64_to_usize(v___x_2250_);
v___x_2252_ = lean_usize_of_nat(v___x_2242_);
v___x_2253_ = ((size_t)1ULL);
v___x_2254_ = lean_usize_sub(v___x_2252_, v___x_2253_);
v___x_2255_ = lean_usize_land(v___x_2251_, v___x_2254_);
v___x_2256_ = lean_array_uget_borrowed(v_x_2234_, v___x_2255_);
lean_inc(v___x_2256_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 2, v___x_2256_);
v___x_2258_ = v___x_2240_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_key_2236_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_value_2237_);
lean_ctor_set(v_reuseFailAlloc_2261_, 2, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_array_uset(v_x_2234_, v___x_2255_, v___x_2258_);
v_x_2234_ = v___x_2259_;
v_x_2235_ = v_tail_2238_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object* v_i_2265_, lean_object* v_source_2266_, lean_object* v_target_2267_){
_start:
{
lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = lean_array_get_size(v_source_2266_);
v___x_2269_ = lean_nat_dec_lt(v_i_2265_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_dec_ref(v_source_2266_);
lean_dec(v_i_2265_);
return v_target_2267_;
}
else
{
lean_object* v_es_2270_; lean_object* v___x_2271_; lean_object* v_source_2272_; lean_object* v_target_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v_es_2270_ = lean_array_fget(v_source_2266_, v_i_2265_);
v___x_2271_ = lean_box(0);
v_source_2272_ = lean_array_fset(v_source_2266_, v_i_2265_, v___x_2271_);
v_target_2273_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_2267_, v_es_2270_);
v___x_2274_ = lean_unsigned_to_nat(1u);
v___x_2275_ = lean_nat_add(v_i_2265_, v___x_2274_);
lean_dec(v_i_2265_);
v_i_2265_ = v___x_2275_;
v_source_2266_ = v_source_2272_;
v_target_2267_ = v_target_2273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object* v_data_2277_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v_nbuckets_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2278_ = lean_array_get_size(v_data_2277_);
v___x_2279_ = lean_unsigned_to_nat(2u);
v_nbuckets_2280_ = lean_nat_mul(v___x_2278_, v___x_2279_);
v___x_2281_ = lean_unsigned_to_nat(0u);
v___x_2282_ = lean_box(0);
v___x_2283_ = lean_mk_array(v_nbuckets_2280_, v___x_2282_);
v___x_2284_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_2281_, v_data_2277_, v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object* v_m_2285_, lean_object* v_a_2286_, lean_object* v_b_2287_){
_start:
{
lean_object* v_size_2288_; lean_object* v_buckets_2289_; lean_object* v___x_2290_; uint64_t v___y_2292_; 
v_size_2288_ = lean_ctor_get(v_m_2285_, 0);
v_buckets_2289_ = lean_ctor_get(v_m_2285_, 1);
v___x_2290_ = lean_array_get_size(v_buckets_2289_);
if (lean_obj_tag(v_a_2286_) == 0)
{
uint64_t v___x_2329_; 
v___x_2329_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___closed__0);
v___y_2292_ = v___x_2329_;
goto v___jp_2291_;
}
else
{
uint64_t v_hash_2330_; 
v_hash_2330_ = lean_ctor_get_uint64(v_a_2286_, sizeof(void*)*2);
v___y_2292_ = v_hash_2330_;
goto v___jp_2291_;
}
v___jp_2291_:
{
uint64_t v___x_2293_; uint64_t v___x_2294_; uint64_t v_fold_2295_; uint64_t v___x_2296_; uint64_t v___x_2297_; uint64_t v___x_2298_; size_t v___x_2299_; size_t v___x_2300_; size_t v___x_2301_; size_t v___x_2302_; size_t v___x_2303_; lean_object* v_bkt_2304_; uint8_t v___x_2305_; 
v___x_2293_ = 32ULL;
v___x_2294_ = lean_uint64_shift_right(v___y_2292_, v___x_2293_);
v_fold_2295_ = lean_uint64_xor(v___y_2292_, v___x_2294_);
v___x_2296_ = 16ULL;
v___x_2297_ = lean_uint64_shift_right(v_fold_2295_, v___x_2296_);
v___x_2298_ = lean_uint64_xor(v_fold_2295_, v___x_2297_);
v___x_2299_ = lean_uint64_to_usize(v___x_2298_);
v___x_2300_ = lean_usize_of_nat(v___x_2290_);
v___x_2301_ = ((size_t)1ULL);
v___x_2302_ = lean_usize_sub(v___x_2300_, v___x_2301_);
v___x_2303_ = lean_usize_land(v___x_2299_, v___x_2302_);
v_bkt_2304_ = lean_array_uget_borrowed(v_buckets_2289_, v___x_2303_);
v___x_2305_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_2286_, v_bkt_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2326_; 
lean_inc_ref(v_buckets_2289_);
lean_inc(v_size_2288_);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_m_2285_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; lean_object* v_unused_2328_; 
v_unused_2327_ = lean_ctor_get(v_m_2285_, 1);
lean_dec(v_unused_2327_);
v_unused_2328_ = lean_ctor_get(v_m_2285_, 0);
lean_dec(v_unused_2328_);
v___x_2307_ = v_m_2285_;
v_isShared_2308_ = v_isSharedCheck_2326_;
goto v_resetjp_2306_;
}
else
{
lean_dec(v_m_2285_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2326_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v_size_x27_2310_; lean_object* v___x_2311_; lean_object* v_buckets_x27_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2309_ = lean_unsigned_to_nat(1u);
v_size_x27_2310_ = lean_nat_add(v_size_2288_, v___x_2309_);
lean_dec(v_size_2288_);
lean_inc(v_bkt_2304_);
v___x_2311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2311_, 0, v_a_2286_);
lean_ctor_set(v___x_2311_, 1, v_b_2287_);
lean_ctor_set(v___x_2311_, 2, v_bkt_2304_);
v_buckets_x27_2312_ = lean_array_uset(v_buckets_2289_, v___x_2303_, v___x_2311_);
v___x_2313_ = lean_unsigned_to_nat(4u);
v___x_2314_ = lean_nat_mul(v_size_x27_2310_, v___x_2313_);
v___x_2315_ = lean_unsigned_to_nat(3u);
v___x_2316_ = lean_nat_div(v___x_2314_, v___x_2315_);
lean_dec(v___x_2314_);
v___x_2317_ = lean_array_get_size(v_buckets_x27_2312_);
v___x_2318_ = lean_nat_dec_le(v___x_2316_, v___x_2317_);
lean_dec(v___x_2316_);
if (v___x_2318_ == 0)
{
lean_object* v_val_2319_; lean_object* v___x_2321_; 
v_val_2319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_2312_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 1, v_val_2319_);
lean_ctor_set(v___x_2307_, 0, v_size_x27_2310_);
v___x_2321_ = v___x_2307_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_size_x27_2310_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_val_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
else
{
lean_object* v___x_2324_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 1, v_buckets_x27_2312_);
lean_ctor_set(v___x_2307_, 0, v_size_x27_2310_);
v___x_2324_ = v___x_2307_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_size_x27_2310_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_buckets_x27_2312_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
else
{
lean_dec(v_b_2287_);
lean_dec(v_a_2286_);
return v_m_2285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object* v_traceClassName_2334_, uint8_t v_inherited_2335_, lean_object* v_ref_2336_){
_start:
{
lean_object* v___x_2338_; lean_object* v_optionName_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2338_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v_optionName_2339_ = l_Lean_Name_append(v___x_2338_, v_traceClassName_2334_);
v___x_2340_ = ((lean_object*)(l_Lean_registerTraceClass___closed__0));
v___x_2341_ = ((lean_object*)(l_Lean_registerTraceClass___closed__1));
v___x_2342_ = lean_box(0);
lean_inc_n(v_optionName_2339_, 2);
v___x_2343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2343_, 0, v_optionName_2339_);
lean_ctor_set(v___x_2343_, 1, v_ref_2336_);
lean_ctor_set(v___x_2343_, 2, v___x_2340_);
lean_ctor_set(v___x_2343_, 3, v___x_2341_);
lean_ctor_set(v___x_2343_, 4, v___x_2342_);
v___x_2344_ = lean_register_option(v_optionName_2339_, v___x_2343_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2360_; 
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; 
v_unused_2361_ = lean_ctor_get(v___x_2344_, 0);
lean_dec(v_unused_2361_);
v___x_2346_ = v___x_2344_;
v_isShared_2347_ = v_isSharedCheck_2360_;
goto v_resetjp_2345_;
}
else
{
lean_dec(v___x_2344_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2360_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
if (v_inherited_2335_ == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
lean_dec(v_optionName_2339_);
v___x_2348_ = lean_box(0);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2348_);
v___x_2350_ = v___x_2346_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
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
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2352_ = l_Lean_inheritedTraceOptions;
v___x_2353_ = lean_st_ref_take(v___x_2352_);
v___x_2354_ = lean_box(0);
v___x_2355_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2353_, v_optionName_2339_, v___x_2354_);
v___x_2356_ = lean_st_ref_set(v___x_2352_, v___x_2355_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2356_);
v___x_2358_ = v___x_2346_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_dec(v_optionName_2339_);
return v___x_2344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object* v_traceClassName_2362_, lean_object* v_inherited_2363_, lean_object* v_ref_2364_, lean_object* v_a_2365_){
_start:
{
uint8_t v_inherited_boxed_2366_; lean_object* v_res_2367_; 
v_inherited_boxed_2366_ = lean_unbox(v_inherited_2363_);
v_res_2367_ = l_Lean_registerTraceClass(v_traceClassName_2362_, v_inherited_boxed_2366_, v_ref_2364_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(lean_object* v_00_u03b2_2368_, lean_object* v_m_2369_, lean_object* v_a_2370_, lean_object* v_b_2371_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v_m_2369_, v_a_2370_, v_b_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object* v_00_u03b2_2373_, lean_object* v_data_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_data_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2376_, lean_object* v_i_2377_, lean_object* v_source_2378_, lean_object* v_target_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_i_2377_, v_source_2378_, v_target_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2382_, v_x_2383_);
return v___x_2384_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_2395_ = l_String_toRawSubstring_x27(v___x_2394_);
return v___x_2395_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13));
v___x_2402_ = l_String_toRawSubstring_x27(v___x_2401_);
return v___x_2402_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18));
v___x_2408_ = l_String_toRawSubstring_x27(v___x_2407_);
return v___x_2408_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31(void){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Array_mkArray0(lean_box(0));
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40));
v___x_2463_ = l_String_toRawSubstring_x27(v___x_2462_);
return v___x_2463_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57));
v___x_2499_ = l_String_toRawSubstring_x27(v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object* v_id_2521_, lean_object* v_s_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v_msg_2622_; lean_object* v_quotContext_2623_; lean_object* v_currMacroScope_2624_; lean_object* v_ref_2625_; lean_object* v___y_2626_; lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
lean_inc(v_s_2522_);
v___x_2672_ = l_Lean_Syntax_getKind(v_s_2522_);
v___x_2673_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49));
v___x_2674_ = lean_name_eq(v___x_2672_, v___x_2673_);
lean_dec(v___x_2672_);
if (v___x_2674_ == 0)
{
lean_object* v_quotContext_2675_; lean_object* v_currMacroScope_2676_; lean_object* v_ref_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v_quotContext_2675_ = lean_ctor_get(v_a_2523_, 1);
v_currMacroScope_2676_ = lean_ctor_get(v_a_2523_, 2);
v_ref_2677_ = lean_ctor_get(v_a_2523_, 5);
v___x_2678_ = l_Lean_SourceInfo_fromRef(v_ref_2677_, v___x_2674_);
v___x_2679_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51));
v___x_2680_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52));
v___x_2681_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
lean_inc_n(v___x_2678_, 8);
v___x_2682_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2678_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2684_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2685_ = lean_box(0);
lean_inc_n(v_currMacroScope_2676_, 3);
lean_inc_n(v_quotContext_2675_, 3);
v___x_2686_ = l_Lean_addMacroScope(v_quotContext_2675_, v___x_2685_, v_currMacroScope_2676_);
v___x_2687_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55));
v___x_2688_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2678_);
lean_ctor_set(v___x_2688_, 1, v___x_2684_);
lean_ctor_set(v___x_2688_, 2, v___x_2686_);
lean_ctor_set(v___x_2688_, 3, v___x_2687_);
v___x_2689_ = l_Lean_Syntax_node1(v___x_2678_, v___x_2683_, v___x_2688_);
v___x_2690_ = l_Lean_Syntax_node2(v___x_2678_, v___x_2680_, v___x_2682_, v___x_2689_);
v___x_2691_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56));
v___x_2692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2678_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2694_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58);
v___x_2695_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59));
v___x_2696_ = l_Lean_addMacroScope(v_quotContext_2675_, v___x_2695_, v_currMacroScope_2676_);
v___x_2697_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64));
v___x_2698_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2678_);
lean_ctor_set(v___x_2698_, 1, v___x_2694_);
lean_ctor_set(v___x_2698_, 2, v___x_2696_);
lean_ctor_set(v___x_2698_, 3, v___x_2697_);
v___x_2699_ = l_Lean_Syntax_node1(v___x_2678_, v___x_2693_, v___x_2698_);
v___x_2700_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2678_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_Syntax_node5(v___x_2678_, v___x_2679_, v___x_2690_, v_s_2522_, v___x_2692_, v___x_2699_, v___x_2701_);
v_msg_2622_ = v___x_2702_;
v_quotContext_2623_ = v_quotContext_2675_;
v_currMacroScope_2624_ = v_currMacroScope_2676_;
v_ref_2625_ = v_ref_2677_;
v___y_2626_ = v_a_2524_;
goto v___jp_2621_;
}
else
{
lean_object* v_quotContext_2703_; lean_object* v_currMacroScope_2704_; lean_object* v_ref_2705_; uint8_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v_quotContext_2703_ = lean_ctor_get(v_a_2523_, 1);
v_currMacroScope_2704_ = lean_ctor_get(v_a_2523_, 2);
v_ref_2705_ = lean_ctor_get(v_a_2523_, 5);
v___x_2706_ = 0;
v___x_2707_ = l_Lean_SourceInfo_fromRef(v_ref_2705_, v___x_2706_);
v___x_2708_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66));
v___x_2709_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67));
lean_inc(v___x_2707_);
v___x_2710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2707_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = l_Lean_Syntax_node2(v___x_2707_, v___x_2708_, v___x_2710_, v_s_2522_);
lean_inc(v_currMacroScope_2704_);
lean_inc(v_quotContext_2703_);
v_msg_2622_ = v___x_2711_;
v_quotContext_2623_ = v_quotContext_2703_;
v_currMacroScope_2624_ = v_currMacroScope_2704_;
v_ref_2625_ = v_ref_2705_;
v___y_2626_ = v_a_2524_;
goto v___jp_2621_;
}
v___jp_2525_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_inc_n(v___y_2539_, 8);
lean_inc(v___y_2541_);
lean_inc_n(v___y_2542_, 30);
v___x_2550_ = l_Lean_Syntax_node5(v___y_2542_, v___y_2541_, v___y_2531_, v___y_2539_, v___y_2539_, v___y_2538_, v___y_2549_);
lean_inc(v___y_2536_);
v___x_2551_ = l_Lean_Syntax_node1(v___y_2542_, v___y_2536_, v___x_2550_);
lean_inc(v___y_2537_);
v___x_2552_ = l_Lean_Syntax_node4(v___y_2542_, v___y_2537_, v___y_2527_, v___y_2539_, v___y_2548_, v___x_2551_);
lean_inc_n(v___y_2533_, 3);
v___x_2553_ = l_Lean_Syntax_node2(v___y_2542_, v___y_2533_, v___x_2552_, v___y_2539_);
v___x_2554_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0));
lean_inc_ref_n(v___y_2529_, 7);
lean_inc_ref_n(v___y_2528_, 7);
lean_inc_ref_n(v___y_2546_, 10);
v___x_2555_ = l_Lean_Name_mkStr4(v___y_2546_, v___y_2528_, v___y_2529_, v___x_2554_);
v___x_2556_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1));
v___x_2557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___y_2542_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2));
v___x_2559_ = l_Lean_Name_mkStr4(v___y_2546_, v___y_2528_, v___y_2529_, v___x_2558_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3));
v___x_2561_ = l_Lean_Name_mkStr4(v___y_2546_, v___y_2528_, v___y_2529_, v___x_2560_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4));
v___x_2563_ = l_Lean_Name_mkStr4(v___y_2546_, v___y_2528_, v___y_2529_, v___x_2562_);
v___x_2564_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
v___x_2565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___y_2542_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2567_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2568_ = lean_box(0);
lean_inc_n(v___y_2540_, 2);
lean_inc_n(v___y_2544_, 2);
v___x_2569_ = l_Lean_addMacroScope(v___y_2544_, v___x_2568_, v___y_2540_);
v___x_2570_ = l_Lean_Name_mkStr1(v___y_2546_);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_inc_n(v___y_2530_, 2);
v___x_2572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___y_2530_);
v___x_2573_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2573_, 0, v___y_2542_);
lean_ctor_set(v___x_2573_, 1, v___x_2567_);
lean_ctor_set(v___x_2573_, 2, v___x_2569_);
lean_ctor_set(v___x_2573_, 3, v___x_2572_);
v___x_2574_ = l_Lean_Syntax_node1(v___y_2542_, v___x_2566_, v___x_2573_);
v___x_2575_ = l_Lean_Syntax_node2(v___y_2542_, v___x_2563_, v___x_2565_, v___x_2574_);
v___x_2576_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9));
v___x_2577_ = l_Lean_Name_mkStr4(v___y_2546_, v___y_2528_, v___y_2529_, v___x_2576_);
v___x_2578_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10));
v___x_2579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___y_2542_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11));
v___x_2581_ = l_Lean_Name_mkStr4(v___y_2546_, v___y_2528_, v___y_2529_, v___x_2580_);
v___x_2582_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12));
v___x_2583_ = l_Lean_Name_mkStr4(v___y_2546_, v___y_2528_, v___y_2529_, v___x_2582_);
v___x_2584_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14);
v___x_2585_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2586_ = l_Lean_Name_mkStr2(v___y_2546_, v___x_2585_);
lean_inc(v___x_2586_);
v___x_2587_ = l_Lean_addMacroScope(v___y_2544_, v___x_2586_, v___y_2540_);
v___x_2588_ = lean_box(0);
v___x_2589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2586_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v___y_2530_);
v___x_2591_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2591_, 0, v___y_2542_);
lean_ctor_set(v___x_2591_, 1, v___x_2584_);
lean_ctor_set(v___x_2591_, 2, v___x_2587_);
lean_ctor_set(v___x_2591_, 3, v___x_2590_);
lean_inc(v___y_2526_);
lean_inc_n(v___y_2545_, 4);
v___x_2592_ = l_Lean_Syntax_node1(v___y_2542_, v___y_2545_, v___y_2526_);
lean_inc(v___x_2583_);
v___x_2593_ = l_Lean_Syntax_node2(v___y_2542_, v___x_2583_, v___x_2591_, v___x_2592_);
lean_inc(v___x_2581_);
v___x_2594_ = l_Lean_Syntax_node1(v___y_2542_, v___x_2581_, v___x_2593_);
v___x_2595_ = l_Lean_Syntax_node2(v___y_2542_, v___x_2577_, v___x_2579_, v___x_2594_);
v___x_2596_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___y_2542_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = l_Lean_Syntax_node3(v___y_2542_, v___x_2561_, v___x_2575_, v___x_2595_, v___x_2597_);
v___x_2599_ = l_Lean_Syntax_node2(v___y_2542_, v___x_2559_, v___y_2539_, v___x_2598_);
v___x_2600_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17));
v___x_2601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___y_2542_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19);
v___x_2603_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20));
v___x_2604_ = l_Lean_Name_mkStr2(v___y_2546_, v___x_2603_);
lean_inc(v___x_2604_);
v___x_2605_ = l_Lean_addMacroScope(v___y_2544_, v___x_2604_, v___y_2540_);
v___x_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2588_);
v___x_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
lean_ctor_set(v___x_2607_, 1, v___y_2530_);
v___x_2608_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2608_, 0, v___y_2542_);
lean_ctor_set(v___x_2608_, 1, v___x_2602_);
lean_ctor_set(v___x_2608_, 2, v___x_2605_);
lean_ctor_set(v___x_2608_, 3, v___x_2607_);
v___x_2609_ = l_Lean_Syntax_node2(v___y_2542_, v___y_2545_, v___y_2526_, v___y_2532_);
v___x_2610_ = l_Lean_Syntax_node2(v___y_2542_, v___x_2583_, v___x_2608_, v___x_2609_);
v___x_2611_ = l_Lean_Syntax_node1(v___y_2542_, v___x_2581_, v___x_2610_);
v___x_2612_ = l_Lean_Syntax_node2(v___y_2542_, v___y_2533_, v___x_2611_, v___y_2539_);
v___x_2613_ = l_Lean_Syntax_node1(v___y_2542_, v___y_2545_, v___x_2612_);
lean_inc_n(v___y_2547_, 2);
v___x_2614_ = l_Lean_Syntax_node1(v___y_2542_, v___y_2547_, v___x_2613_);
v___x_2615_ = l_Lean_Syntax_node6(v___y_2542_, v___x_2555_, v___x_2557_, v___x_2599_, v___x_2601_, v___x_2614_, v___y_2539_, v___y_2539_);
v___x_2616_ = l_Lean_Syntax_node2(v___y_2542_, v___y_2533_, v___x_2615_, v___y_2539_);
v___x_2617_ = l_Lean_Syntax_node2(v___y_2542_, v___y_2545_, v___x_2553_, v___x_2616_);
v___x_2618_ = l_Lean_Syntax_node1(v___y_2542_, v___y_2547_, v___x_2617_);
lean_inc(v___y_2534_);
v___x_2619_ = l_Lean_Syntax_node2(v___y_2542_, v___y_2534_, v___y_2543_, v___x_2618_);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___y_2535_);
return v___x_2620_;
}
v___jp_2621_:
{
uint8_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2627_ = 0;
v___x_2628_ = l_Lean_SourceInfo_fromRef(v_ref_2625_, v___x_2627_);
v___x_2629_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0));
v___x_2630_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1));
v___x_2631_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__0));
v___x_2632_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22));
v___x_2633_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23));
lean_inc_n(v___x_2628_, 7);
v___x_2634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2628_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25));
v___x_2636_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2637_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27));
v___x_2638_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2639_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
v___x_2640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2628_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31);
v___x_2642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2628_);
lean_ctor_set(v___x_2642_, 1, v___x_2636_);
lean_ctor_set(v___x_2642_, 2, v___x_2641_);
v___x_2643_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33));
lean_inc_ref(v___x_2642_);
v___x_2644_ = l_Lean_Syntax_node1(v___x_2628_, v___x_2643_, v___x_2642_);
v___x_2645_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35));
v___x_2646_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37));
v___x_2647_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39));
v___x_2648_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41);
v___x_2649_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42));
lean_inc(v_currMacroScope_2624_);
lean_inc(v_quotContext_2623_);
v___x_2650_ = l_Lean_addMacroScope(v_quotContext_2623_, v___x_2649_, v_currMacroScope_2624_);
v___x_2651_ = lean_box(0);
v___x_2652_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2628_);
lean_ctor_set(v___x_2652_, 1, v___x_2648_);
lean_ctor_set(v___x_2652_, 2, v___x_2650_);
lean_ctor_set(v___x_2652_, 3, v___x_2651_);
lean_inc_ref(v___x_2652_);
v___x_2653_ = l_Lean_Syntax_node1(v___x_2628_, v___x_2647_, v___x_2652_);
v___x_2654_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43));
v___x_2655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2628_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = l_Lean_Syntax_getId(v_id_2521_);
v___x_2657_ = lean_erase_macro_scopes(v___x_2656_);
lean_inc(v___x_2657_);
v___x_2658_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2651_, v___x_2657_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_quoteNameMk(v___x_2657_);
v___y_2526_ = v___x_2652_;
v___y_2527_ = v___x_2640_;
v___y_2528_ = v___x_2630_;
v___y_2529_ = v___x_2631_;
v___y_2530_ = v___x_2651_;
v___y_2531_ = v___x_2653_;
v___y_2532_ = v_msg_2622_;
v___y_2533_ = v___x_2637_;
v___y_2534_ = v___x_2632_;
v___y_2535_ = v___y_2626_;
v___y_2536_ = v___x_2645_;
v___y_2537_ = v___x_2638_;
v___y_2538_ = v___x_2655_;
v___y_2539_ = v___x_2642_;
v___y_2540_ = v_currMacroScope_2624_;
v___y_2541_ = v___x_2646_;
v___y_2542_ = v___x_2628_;
v___y_2543_ = v___x_2634_;
v___y_2544_ = v_quotContext_2623_;
v___y_2545_ = v___x_2636_;
v___y_2546_ = v___x_2629_;
v___y_2547_ = v___x_2635_;
v___y_2548_ = v___x_2644_;
v___y_2549_ = v___x_2659_;
goto v___jp_2525_;
}
else
{
lean_object* v_val_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec(v___x_2657_);
v_val_2660_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_val_2660_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2661_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45));
v___x_2662_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46));
v___x_2663_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47));
v___x_2664_ = lean_string_intercalate(v___x_2663_, v_val_2660_);
v___x_2665_ = lean_string_append(v___x_2662_, v___x_2664_);
lean_dec_ref(v___x_2664_);
v___x_2666_ = lean_box(2);
v___x_2667_ = l_Lean_Syntax_mkNameLit(v___x_2665_, v___x_2666_);
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = lean_mk_empty_array_with_capacity(v___x_2668_);
v___x_2670_ = lean_array_push(v___x_2669_, v___x_2667_);
v___x_2671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2666_);
lean_ctor_set(v___x_2671_, 1, v___x_2661_);
lean_ctor_set(v___x_2671_, 2, v___x_2670_);
v___y_2526_ = v___x_2652_;
v___y_2527_ = v___x_2640_;
v___y_2528_ = v___x_2630_;
v___y_2529_ = v___x_2631_;
v___y_2530_ = v___x_2651_;
v___y_2531_ = v___x_2653_;
v___y_2532_ = v_msg_2622_;
v___y_2533_ = v___x_2637_;
v___y_2534_ = v___x_2632_;
v___y_2535_ = v___y_2626_;
v___y_2536_ = v___x_2645_;
v___y_2537_ = v___x_2638_;
v___y_2538_ = v___x_2655_;
v___y_2539_ = v___x_2642_;
v___y_2540_ = v_currMacroScope_2624_;
v___y_2541_ = v___x_2646_;
v___y_2542_ = v___x_2628_;
v___y_2543_ = v___x_2634_;
v___y_2544_ = v_quotContext_2623_;
v___y_2545_ = v___x_2636_;
v___y_2546_ = v___x_2629_;
v___y_2547_ = v___x_2635_;
v___y_2548_ = v___x_2644_;
v___y_2549_ = v___x_2671_;
goto v___jp_2525_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object* v_id_2712_, lean_object* v_s_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v_id_2712_, v_s_2713_, v_a_2714_, v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_id_2712_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object* v_x_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v___x_2774_; uint8_t v___x_2775_; 
v___x_2774_ = ((lean_object*)(l_Lean_doElemTrace_x5b___x5d_____00__closed__1));
lean_inc(v_x_2771_);
v___x_2775_ = l_Lean_Syntax_isOfKind(v_x_2771_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
lean_dec(v_x_2771_);
v___x_2776_ = lean_box(1);
v___x_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
lean_ctor_set(v___x_2777_, 1, v_a_2773_);
return v___x_2777_;
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v_a_2783_; lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
v___x_2778_ = lean_unsigned_to_nat(1u);
v___x_2779_ = l_Lean_Syntax_getArg(v_x_2771_, v___x_2778_);
v___x_2780_ = lean_unsigned_to_nat(3u);
v___x_2781_ = l_Lean_Syntax_getArg(v_x_2771_, v___x_2780_);
lean_dec(v_x_2771_);
v___x_2782_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v___x_2779_, v___x_2781_, v_a_2772_, v_a_2773_);
lean_dec(v___x_2779_);
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_a_2784_ = lean_ctor_get(v___x_2782_, 1);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2782_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2783_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object* v_x_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(v_x_2792_, v_a_2793_, v_a_2794_);
lean_dec_ref(v_a_2793_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object* v_inst_2796_, lean_object* v_inst_2797_, lean_object* v_inst_2798_, lean_object* v_inst_2799_, lean_object* v_always_2800_, lean_object* v_inst_2801_, lean_object* v_cls_2802_, uint8_t v_collapsed_2803_, lean_object* v_tag_2804_, lean_object* v_opts_2805_, uint8_t v_clsEnabled_2806_, lean_object* v_oldTraces_2807_, lean_object* v_ref_2808_, lean_object* v_msg_2809_, lean_object* v_resStartStop_2810_){
_start:
{
lean_object* v___x_2811_; lean_object* v_snd_2812_; lean_object* v_fst_2813_; lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v___f_2816_; lean_object* v___f_2817_; lean_object* v_data_2819_; lean_object* v___x_2823_; lean_object* v___x_2824_; uint8_t v___y_2835_; double v___y_2841_; uint8_t v___x_2846_; 
v___x_2811_ = l_Lean_KVMap_instValueBool;
v_snd_2812_ = lean_ctor_get(v_resStartStop_2810_, 1);
lean_inc(v_snd_2812_);
v_fst_2813_ = lean_ctor_get(v_resStartStop_2810_, 0);
lean_inc_n(v_fst_2813_, 2);
lean_dec_ref(v_resStartStop_2810_);
v_fst_2814_ = lean_ctor_get(v_snd_2812_, 0);
lean_inc(v_fst_2814_);
v_snd_2815_ = lean_ctor_get(v_snd_2812_, 1);
lean_inc(v_snd_2815_);
lean_dec(v_snd_2812_);
lean_inc_ref(v_oldTraces_2807_);
v___f_2816_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2816_, 0, v_oldTraces_2807_);
lean_inc_ref(v_inst_2796_);
v___f_2817_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2817_, 0, v_always_2800_);
lean_closure_set(v___f_2817_, 1, v_inst_2796_);
lean_closure_set(v___f_2817_, 2, v_fst_2813_);
v___x_2823_ = l_Lean_trace_profiler;
v___x_2824_ = l_Lean_Option_get___redArg(v___x_2811_, v_opts_2805_, v___x_2823_);
v___x_2846_ = lean_unbox(v___x_2824_);
if (v___x_2846_ == 0)
{
uint8_t v___x_2847_; 
v___x_2847_ = lean_unbox(v___x_2824_);
v___y_2835_ = v___x_2847_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2848_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2849_ = l_Lean_Option_get___redArg(v___x_2811_, v_opts_2805_, v___x_2848_);
v___x_2850_ = lean_unbox(v___x_2849_);
lean_dec(v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; double v___x_2854_; double v___x_2855_; double v___x_2856_; 
v___x_2851_ = l_Lean_KVMap_instValueNat;
v___x_2852_ = l_Lean_trace_profiler_threshold;
v___x_2853_ = l_Lean_Option_get___redArg(v___x_2851_, v_opts_2805_, v___x_2852_);
v___x_2854_ = lean_float_of_nat(v___x_2853_);
v___x_2855_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_2856_ = lean_float_div(v___x_2854_, v___x_2855_);
v___y_2841_ = v___x_2856_;
goto v___jp_2840_;
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; double v___x_2860_; 
v___x_2857_ = l_Lean_KVMap_instValueNat;
v___x_2858_ = l_Lean_trace_profiler_threshold;
v___x_2859_ = l_Lean_Option_get___redArg(v___x_2857_, v_opts_2805_, v___x_2858_);
v___x_2860_ = lean_float_of_nat(v___x_2859_);
v___y_2841_ = v___x_2860_;
goto v___jp_2840_;
}
}
v___jp_2818_:
{
lean_object* v_toBind_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_toBind_2820_ = lean_ctor_get(v_inst_2796_, 1);
lean_inc(v_toBind_2820_);
v___x_2821_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_2796_, v_inst_2797_, v_inst_2798_, v_inst_2799_, v_oldTraces_2807_, v_data_2819_, v_ref_2808_, v_msg_2809_);
v___x_2822_ = lean_apply_4(v_toBind_2820_, lean_box(0), lean_box(0), v___x_2821_, v___f_2817_);
return v___x_2822_;
}
v___jp_2825_:
{
lean_object* v_result_2826_; lean_object* v___x_2827_; double v___x_2828_; lean_object* v_data_2829_; uint8_t v___x_2830_; 
v_result_2826_ = lean_apply_1(v_inst_2801_, v_fst_2813_);
v___x_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2827_, 0, v_result_2826_);
v___x_2828_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_2804_);
lean_inc_ref(v___x_2827_);
lean_inc(v_cls_2802_);
v_data_2829_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2829_, 0, v_cls_2802_);
lean_ctor_set(v_data_2829_, 1, v___x_2827_);
lean_ctor_set(v_data_2829_, 2, v_tag_2804_);
lean_ctor_set_float(v_data_2829_, sizeof(void*)*3, v___x_2828_);
lean_ctor_set_float(v_data_2829_, sizeof(void*)*3 + 8, v___x_2828_);
lean_ctor_set_uint8(v_data_2829_, sizeof(void*)*3 + 16, v_collapsed_2803_);
v___x_2830_ = lean_unbox(v___x_2824_);
lean_dec(v___x_2824_);
if (v___x_2830_ == 0)
{
lean_dec_ref_known(v___x_2827_, 1);
lean_dec(v_snd_2815_);
lean_dec(v_fst_2814_);
lean_dec_ref(v_tag_2804_);
lean_dec(v_cls_2802_);
v_data_2819_ = v_data_2829_;
goto v___jp_2818_;
}
else
{
lean_object* v_data_2831_; double v___x_2832_; double v___x_2833_; 
lean_dec_ref_known(v_data_2829_, 3);
v_data_2831_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2831_, 0, v_cls_2802_);
lean_ctor_set(v_data_2831_, 1, v___x_2827_);
lean_ctor_set(v_data_2831_, 2, v_tag_2804_);
v___x_2832_ = lean_unbox_float(v_fst_2814_);
lean_dec(v_fst_2814_);
lean_ctor_set_float(v_data_2831_, sizeof(void*)*3, v___x_2832_);
v___x_2833_ = lean_unbox_float(v_snd_2815_);
lean_dec(v_snd_2815_);
lean_ctor_set_float(v_data_2831_, sizeof(void*)*3 + 8, v___x_2833_);
lean_ctor_set_uint8(v_data_2831_, sizeof(void*)*3 + 16, v_collapsed_2803_);
v_data_2819_ = v_data_2831_;
goto v___jp_2818_;
}
}
v___jp_2834_:
{
if (v_clsEnabled_2806_ == 0)
{
if (v___y_2835_ == 0)
{
lean_object* v_toBind_2836_; lean_object* v_modifyTraceState_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_dec(v___x_2824_);
lean_dec(v_snd_2815_);
lean_dec(v_fst_2814_);
lean_dec(v_fst_2813_);
lean_dec_ref(v_msg_2809_);
lean_dec(v_ref_2808_);
lean_dec_ref(v_oldTraces_2807_);
lean_dec_ref(v_tag_2804_);
lean_dec(v_cls_2802_);
lean_dec_ref(v_inst_2801_);
lean_dec(v_inst_2799_);
lean_dec_ref(v_inst_2798_);
v_toBind_2836_ = lean_ctor_get(v_inst_2796_, 1);
lean_inc(v_toBind_2836_);
lean_dec_ref(v_inst_2796_);
v_modifyTraceState_2837_ = lean_ctor_get(v_inst_2797_, 0);
lean_inc(v_modifyTraceState_2837_);
lean_dec_ref(v_inst_2797_);
v___x_2838_ = lean_apply_1(v_modifyTraceState_2837_, v___f_2816_);
v___x_2839_ = lean_apply_4(v_toBind_2836_, lean_box(0), lean_box(0), v___x_2838_, v___f_2817_);
return v___x_2839_;
}
else
{
lean_dec_ref(v___f_2816_);
goto v___jp_2825_;
}
}
else
{
lean_dec_ref(v___f_2816_);
goto v___jp_2825_;
}
}
v___jp_2840_:
{
double v___x_2842_; double v___x_2843_; double v___x_2844_; uint8_t v___x_2845_; 
v___x_2842_ = lean_unbox_float(v_snd_2815_);
v___x_2843_ = lean_unbox_float(v_fst_2814_);
v___x_2844_ = lean_float_sub(v___x_2842_, v___x_2843_);
v___x_2845_ = lean_float_decLt(v___y_2841_, v___x_2844_);
v___y_2835_ = v___x_2845_;
goto v___jp_2834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object* v_inst_2861_, lean_object* v_inst_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_always_2865_, lean_object* v_inst_2866_, lean_object* v_cls_2867_, lean_object* v_collapsed_2868_, lean_object* v_tag_2869_, lean_object* v_opts_2870_, lean_object* v_clsEnabled_2871_, lean_object* v_oldTraces_2872_, lean_object* v_ref_2873_, lean_object* v_msg_2874_, lean_object* v_resStartStop_2875_){
_start:
{
uint8_t v_collapsed_boxed_2876_; uint8_t v_clsEnabled_boxed_2877_; lean_object* v_res_2878_; 
v_collapsed_boxed_2876_ = lean_unbox(v_collapsed_2868_);
v_clsEnabled_boxed_2877_ = lean_unbox(v_clsEnabled_2871_);
v_res_2878_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2861_, v_inst_2862_, v_inst_2863_, v_inst_2864_, v_always_2865_, v_inst_2866_, v_cls_2867_, v_collapsed_boxed_2876_, v_tag_2869_, v_opts_2870_, v_clsEnabled_boxed_2877_, v_oldTraces_2872_, v_ref_2873_, v_msg_2874_, v_resStartStop_2875_);
lean_dec_ref(v_opts_2870_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object* v_00_u03b1_2879_, lean_object* v_m_2880_, lean_object* v_inst_2881_, lean_object* v_inst_2882_, lean_object* v_00_u03b5_2883_, lean_object* v_inst_2884_, lean_object* v_inst_2885_, lean_object* v_always_2886_, lean_object* v_inst_2887_, lean_object* v_cls_2888_, uint8_t v_collapsed_2889_, lean_object* v_tag_2890_, lean_object* v_opts_2891_, uint8_t v_clsEnabled_2892_, lean_object* v_oldTraces_2893_, lean_object* v_ref_2894_, lean_object* v_msg_2895_, lean_object* v_resStartStop_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2881_, v_inst_2882_, v_inst_2884_, v_inst_2885_, v_always_2886_, v_inst_2887_, v_cls_2888_, v_collapsed_2889_, v_tag_2890_, v_opts_2891_, v_clsEnabled_2892_, v_oldTraces_2893_, v_ref_2894_, v_msg_2895_, v_resStartStop_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_2898_ = _args[0];
lean_object* v_m_2899_ = _args[1];
lean_object* v_inst_2900_ = _args[2];
lean_object* v_inst_2901_ = _args[3];
lean_object* v_00_u03b5_2902_ = _args[4];
lean_object* v_inst_2903_ = _args[5];
lean_object* v_inst_2904_ = _args[6];
lean_object* v_always_2905_ = _args[7];
lean_object* v_inst_2906_ = _args[8];
lean_object* v_cls_2907_ = _args[9];
lean_object* v_collapsed_2908_ = _args[10];
lean_object* v_tag_2909_ = _args[11];
lean_object* v_opts_2910_ = _args[12];
lean_object* v_clsEnabled_2911_ = _args[13];
lean_object* v_oldTraces_2912_ = _args[14];
lean_object* v_ref_2913_ = _args[15];
lean_object* v_msg_2914_ = _args[16];
lean_object* v_resStartStop_2915_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2916_; uint8_t v_clsEnabled_boxed_2917_; lean_object* v_res_2918_; 
v_collapsed_boxed_2916_ = lean_unbox(v_collapsed_2908_);
v_clsEnabled_boxed_2917_ = lean_unbox(v_clsEnabled_2911_);
v_res_2918_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(v_00_u03b1_2898_, v_m_2899_, v_inst_2900_, v_inst_2901_, v_00_u03b5_2902_, v_inst_2903_, v_inst_2904_, v_always_2905_, v_inst_2906_, v_cls_2907_, v_collapsed_boxed_2916_, v_tag_2909_, v_opts_2910_, v_clsEnabled_boxed_2917_, v_oldTraces_2912_, v_ref_2913_, v_msg_2914_, v_resStartStop_2915_);
lean_dec_ref(v_opts_2910_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object* v_inst_2919_, lean_object* v_____do__lift_2920_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_apply_1(v_inst_2919_, v_____do__lift_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_always_2926_, lean_object* v_inst_2927_, lean_object* v_cls_2928_, uint8_t v_collapsed_2929_, lean_object* v_tag_2930_, lean_object* v_opts_2931_, uint8_t v_clsEnabled_2932_, lean_object* v_oldTraces_2933_, lean_object* v_ref_2934_, lean_object* v_msg_2935_, lean_object* v_resStartStop_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2922_, v_inst_2923_, v_inst_2924_, v_inst_2925_, v_always_2926_, v_inst_2927_, v_cls_2928_, v_collapsed_2929_, v_tag_2930_, v_opts_2931_, v_clsEnabled_2932_, v_oldTraces_2933_, v_ref_2934_, v_msg_2935_, v_resStartStop_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object* v_inst_2938_, lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_always_2942_, lean_object* v_inst_2943_, lean_object* v_cls_2944_, lean_object* v_collapsed_2945_, lean_object* v_tag_2946_, lean_object* v_opts_2947_, lean_object* v_clsEnabled_2948_, lean_object* v_oldTraces_2949_, lean_object* v_ref_2950_, lean_object* v_msg_2951_, lean_object* v_resStartStop_2952_){
_start:
{
uint8_t v_collapsed_boxed_2953_; uint8_t v_clsEnabled_boxed_2954_; lean_object* v_res_2955_; 
v_collapsed_boxed_2953_ = lean_unbox(v_collapsed_2945_);
v_clsEnabled_boxed_2954_ = lean_unbox(v_clsEnabled_2948_);
v_res_2955_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_2938_, v_inst_2939_, v_inst_2940_, v_inst_2941_, v_always_2942_, v_inst_2943_, v_cls_2944_, v_collapsed_boxed_2953_, v_tag_2946_, v_opts_2947_, v_clsEnabled_boxed_2954_, v_oldTraces_2949_, v_ref_2950_, v_msg_2951_, v_resStartStop_2952_);
lean_dec_ref(v_opts_2947_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object* v_always_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_inst_2959_, lean_object* v_inst_2960_, lean_object* v_inst_2961_, lean_object* v_cls_2962_, uint8_t v_collapsed_2963_, lean_object* v_tag_2964_, lean_object* v_opts_2965_, uint8_t v_clsEnabled_2966_, lean_object* v_oldTraces_2967_, lean_object* v_ref_2968_, lean_object* v_toPure_2969_, lean_object* v_toBind_2970_, lean_object* v_k_2971_, lean_object* v_inst_2972_, lean_object* v_msg_2973_){
_start:
{
lean_object* v_tryCatch_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___f_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v_tryCatch_2974_ = lean_ctor_get(v_always_2956_, 1);
lean_inc(v_tryCatch_2974_);
v___x_2975_ = lean_box(v_collapsed_2963_);
v___x_2976_ = lean_box(v_clsEnabled_2966_);
lean_inc_ref(v_opts_2965_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__1___boxed), 15, 14);
lean_closure_set(v___f_2977_, 0, v_inst_2957_);
lean_closure_set(v___f_2977_, 1, v_inst_2958_);
lean_closure_set(v___f_2977_, 2, v_inst_2959_);
lean_closure_set(v___f_2977_, 3, v_inst_2960_);
lean_closure_set(v___f_2977_, 4, v_always_2956_);
lean_closure_set(v___f_2977_, 5, v_inst_2961_);
lean_closure_set(v___f_2977_, 6, v_cls_2962_);
lean_closure_set(v___f_2977_, 7, v___x_2975_);
lean_closure_set(v___f_2977_, 8, v_tag_2964_);
lean_closure_set(v___f_2977_, 9, v_opts_2965_);
lean_closure_set(v___f_2977_, 10, v___x_2976_);
lean_closure_set(v___f_2977_, 11, v_oldTraces_2967_);
lean_closure_set(v___f_2977_, 12, v_ref_2968_);
lean_closure_set(v___f_2977_, 13, v_msg_2973_);
lean_inc_n(v_toPure_2969_, 2);
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2978_, 0, v_toPure_2969_);
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2979_, 0, v_toPure_2969_);
lean_inc(v_toBind_2970_);
v___x_2980_ = lean_apply_4(v_toBind_2970_, lean_box(0), lean_box(0), v_k_2971_, v___f_2979_);
v___x_2981_ = lean_apply_3(v_tryCatch_2974_, lean_box(0), v___x_2980_, v___f_2978_);
v___x_2982_ = l_Lean_KVMap_instValueBool;
v___x_2983_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2984_ = l_Lean_Option_get___redArg(v___x_2982_, v_opts_2965_, v___x_2983_);
lean_dec_ref(v_opts_2965_);
v___x_2985_ = lean_unbox(v___x_2984_);
lean_dec(v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___f_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2986_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_2987_ = lean_apply_2(v_inst_2972_, lean_box(0), v___x_2986_);
lean_inc(v___x_2987_);
lean_inc_n(v_toBind_2970_, 2);
v___f_2988_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_2988_, 0, v_toPure_2969_);
lean_closure_set(v___f_2988_, 1, v_toBind_2970_);
lean_closure_set(v___f_2988_, 2, v___x_2987_);
lean_closure_set(v___f_2988_, 3, v___x_2981_);
v___x_2989_ = lean_apply_4(v_toBind_2970_, lean_box(0), lean_box(0), v___x_2987_, v___f_2988_);
v___x_2990_ = lean_apply_4(v_toBind_2970_, lean_box(0), lean_box(0), v___x_2989_, v___f_2977_);
return v___x_2990_;
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___f_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2991_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_2992_ = lean_apply_2(v_inst_2972_, lean_box(0), v___x_2991_);
lean_inc(v___x_2992_);
lean_inc_n(v_toBind_2970_, 2);
v___f_2993_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_2993_, 0, v_toPure_2969_);
lean_closure_set(v___f_2993_, 1, v_toBind_2970_);
lean_closure_set(v___f_2993_, 2, v___x_2992_);
lean_closure_set(v___f_2993_, 3, v___x_2981_);
v___x_2994_ = lean_apply_4(v_toBind_2970_, lean_box(0), lean_box(0), v___x_2992_, v___f_2993_);
v___x_2995_ = lean_apply_4(v_toBind_2970_, lean_box(0), lean_box(0), v___x_2994_, v___f_2977_);
return v___x_2995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_2996_ = _args[0];
lean_object* v_inst_2997_ = _args[1];
lean_object* v_inst_2998_ = _args[2];
lean_object* v_inst_2999_ = _args[3];
lean_object* v_inst_3000_ = _args[4];
lean_object* v_inst_3001_ = _args[5];
lean_object* v_cls_3002_ = _args[6];
lean_object* v_collapsed_3003_ = _args[7];
lean_object* v_tag_3004_ = _args[8];
lean_object* v_opts_3005_ = _args[9];
lean_object* v_clsEnabled_3006_ = _args[10];
lean_object* v_oldTraces_3007_ = _args[11];
lean_object* v_ref_3008_ = _args[12];
lean_object* v_toPure_3009_ = _args[13];
lean_object* v_toBind_3010_ = _args[14];
lean_object* v_k_3011_ = _args[15];
lean_object* v_inst_3012_ = _args[16];
lean_object* v_msg_3013_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3014_; uint8_t v_clsEnabled_boxed_3015_; lean_object* v_res_3016_; 
v_collapsed_boxed_3014_ = lean_unbox(v_collapsed_3003_);
v_clsEnabled_boxed_3015_ = lean_unbox(v_clsEnabled_3006_);
v_res_3016_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_always_2996_, v_inst_2997_, v_inst_2998_, v_inst_2999_, v_inst_3000_, v_inst_3001_, v_cls_3002_, v_collapsed_boxed_3014_, v_tag_3004_, v_opts_3005_, v_clsEnabled_boxed_3015_, v_oldTraces_3007_, v_ref_3008_, v_toPure_3009_, v_toBind_3010_, v_k_3011_, v_inst_3012_, v_msg_3013_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object* v_always_3017_, lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_inst_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_cls_3023_, uint8_t v_collapsed_3024_, lean_object* v_tag_3025_, lean_object* v_opts_3026_, uint8_t v_clsEnabled_3027_, lean_object* v_oldTraces_3028_, lean_object* v_toPure_3029_, lean_object* v_toBind_3030_, lean_object* v_k_3031_, lean_object* v_inst_3032_, lean_object* v_msg_3033_, lean_object* v___f_3034_, lean_object* v_withRef_3035_, lean_object* v_getRef_3036_, lean_object* v_ref_3037_){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___f_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___f_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3038_ = lean_box(v_collapsed_3024_);
v___x_3039_ = lean_box(v_clsEnabled_3027_);
lean_inc_n(v_toBind_3030_, 3);
lean_inc(v_ref_3037_);
v___f_3040_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__10___boxed), 18, 17);
lean_closure_set(v___f_3040_, 0, v_always_3017_);
lean_closure_set(v___f_3040_, 1, v_inst_3018_);
lean_closure_set(v___f_3040_, 2, v_inst_3019_);
lean_closure_set(v___f_3040_, 3, v_inst_3020_);
lean_closure_set(v___f_3040_, 4, v_inst_3021_);
lean_closure_set(v___f_3040_, 5, v_inst_3022_);
lean_closure_set(v___f_3040_, 6, v_cls_3023_);
lean_closure_set(v___f_3040_, 7, v___x_3038_);
lean_closure_set(v___f_3040_, 8, v_tag_3025_);
lean_closure_set(v___f_3040_, 9, v_opts_3026_);
lean_closure_set(v___f_3040_, 10, v___x_3039_);
lean_closure_set(v___f_3040_, 11, v_oldTraces_3028_);
lean_closure_set(v___f_3040_, 12, v_ref_3037_);
lean_closure_set(v___f_3040_, 13, v_toPure_3029_);
lean_closure_set(v___f_3040_, 14, v_toBind_3030_);
lean_closure_set(v___f_3040_, 15, v_k_3031_);
lean_closure_set(v___f_3040_, 16, v_inst_3032_);
v___x_3041_ = lean_box(0);
v___x_3042_ = lean_apply_1(v_msg_3033_, v___x_3041_);
v___x_3043_ = lean_apply_4(v_toBind_3030_, lean_box(0), lean_box(0), v___x_3042_, v___f_3034_);
v___f_3044_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3044_, 0, v_ref_3037_);
lean_closure_set(v___f_3044_, 1, v_withRef_3035_);
lean_closure_set(v___f_3044_, 2, v___x_3043_);
v___x_3045_ = lean_apply_4(v_toBind_3030_, lean_box(0), lean_box(0), v_getRef_3036_, v___f_3044_);
v___x_3046_ = lean_apply_4(v_toBind_3030_, lean_box(0), lean_box(0), v___x_3045_, v___f_3040_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_3047_ = _args[0];
lean_object* v_inst_3048_ = _args[1];
lean_object* v_inst_3049_ = _args[2];
lean_object* v_inst_3050_ = _args[3];
lean_object* v_inst_3051_ = _args[4];
lean_object* v_inst_3052_ = _args[5];
lean_object* v_cls_3053_ = _args[6];
lean_object* v_collapsed_3054_ = _args[7];
lean_object* v_tag_3055_ = _args[8];
lean_object* v_opts_3056_ = _args[9];
lean_object* v_clsEnabled_3057_ = _args[10];
lean_object* v_oldTraces_3058_ = _args[11];
lean_object* v_toPure_3059_ = _args[12];
lean_object* v_toBind_3060_ = _args[13];
lean_object* v_k_3061_ = _args[14];
lean_object* v_inst_3062_ = _args[15];
lean_object* v_msg_3063_ = _args[16];
lean_object* v___f_3064_ = _args[17];
lean_object* v_withRef_3065_ = _args[18];
lean_object* v_getRef_3066_ = _args[19];
lean_object* v_ref_3067_ = _args[20];
_start:
{
uint8_t v_collapsed_boxed_3068_; uint8_t v_clsEnabled_boxed_3069_; lean_object* v_res_3070_; 
v_collapsed_boxed_3068_ = lean_unbox(v_collapsed_3054_);
v_clsEnabled_boxed_3069_ = lean_unbox(v_clsEnabled_3057_);
v_res_3070_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_always_3047_, v_inst_3048_, v_inst_3049_, v_inst_3050_, v_inst_3051_, v_inst_3052_, v_cls_3053_, v_collapsed_boxed_3068_, v_tag_3055_, v_opts_3056_, v_clsEnabled_boxed_3069_, v_oldTraces_3058_, v_toPure_3059_, v_toBind_3060_, v_k_3061_, v_inst_3062_, v_msg_3063_, v___f_3064_, v_withRef_3065_, v_getRef_3066_, v_ref_3067_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object* v_inst_3071_, lean_object* v_always_3072_, lean_object* v_inst_3073_, lean_object* v_inst_3074_, lean_object* v_inst_3075_, lean_object* v_inst_3076_, lean_object* v_cls_3077_, uint8_t v_collapsed_3078_, lean_object* v_tag_3079_, lean_object* v_opts_3080_, uint8_t v_clsEnabled_3081_, lean_object* v_toPure_3082_, lean_object* v_toBind_3083_, lean_object* v_k_3084_, lean_object* v_inst_3085_, lean_object* v_msg_3086_, lean_object* v___f_3087_, lean_object* v_oldTraces_3088_){
_start:
{
lean_object* v_getRef_3089_; lean_object* v_withRef_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___f_3093_; lean_object* v___x_3094_; 
v_getRef_3089_ = lean_ctor_get(v_inst_3071_, 0);
lean_inc_n(v_getRef_3089_, 2);
v_withRef_3090_ = lean_ctor_get(v_inst_3071_, 1);
lean_inc(v_withRef_3090_);
v___x_3091_ = lean_box(v_collapsed_3078_);
v___x_3092_ = lean_box(v_clsEnabled_3081_);
lean_inc(v_toBind_3083_);
v___f_3093_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__3___boxed), 21, 20);
lean_closure_set(v___f_3093_, 0, v_always_3072_);
lean_closure_set(v___f_3093_, 1, v_inst_3073_);
lean_closure_set(v___f_3093_, 2, v_inst_3074_);
lean_closure_set(v___f_3093_, 3, v_inst_3071_);
lean_closure_set(v___f_3093_, 4, v_inst_3075_);
lean_closure_set(v___f_3093_, 5, v_inst_3076_);
lean_closure_set(v___f_3093_, 6, v_cls_3077_);
lean_closure_set(v___f_3093_, 7, v___x_3091_);
lean_closure_set(v___f_3093_, 8, v_tag_3079_);
lean_closure_set(v___f_3093_, 9, v_opts_3080_);
lean_closure_set(v___f_3093_, 10, v___x_3092_);
lean_closure_set(v___f_3093_, 11, v_oldTraces_3088_);
lean_closure_set(v___f_3093_, 12, v_toPure_3082_);
lean_closure_set(v___f_3093_, 13, v_toBind_3083_);
lean_closure_set(v___f_3093_, 14, v_k_3084_);
lean_closure_set(v___f_3093_, 15, v_inst_3085_);
lean_closure_set(v___f_3093_, 16, v_msg_3086_);
lean_closure_set(v___f_3093_, 17, v___f_3087_);
lean_closure_set(v___f_3093_, 18, v_withRef_3090_);
lean_closure_set(v___f_3093_, 19, v_getRef_3089_);
v___x_3094_ = lean_apply_4(v_toBind_3083_, lean_box(0), lean_box(0), v_getRef_3089_, v___f_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_3095_ = _args[0];
lean_object* v_always_3096_ = _args[1];
lean_object* v_inst_3097_ = _args[2];
lean_object* v_inst_3098_ = _args[3];
lean_object* v_inst_3099_ = _args[4];
lean_object* v_inst_3100_ = _args[5];
lean_object* v_cls_3101_ = _args[6];
lean_object* v_collapsed_3102_ = _args[7];
lean_object* v_tag_3103_ = _args[8];
lean_object* v_opts_3104_ = _args[9];
lean_object* v_clsEnabled_3105_ = _args[10];
lean_object* v_toPure_3106_ = _args[11];
lean_object* v_toBind_3107_ = _args[12];
lean_object* v_k_3108_ = _args[13];
lean_object* v_inst_3109_ = _args[14];
lean_object* v_msg_3110_ = _args[15];
lean_object* v___f_3111_ = _args[16];
lean_object* v_oldTraces_3112_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3113_; uint8_t v_clsEnabled_boxed_3114_; lean_object* v_res_3115_; 
v_collapsed_boxed_3113_ = lean_unbox(v_collapsed_3102_);
v_clsEnabled_boxed_3114_ = lean_unbox(v_clsEnabled_3105_);
v_res_3115_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3095_, v_always_3096_, v_inst_3097_, v_inst_3098_, v_inst_3099_, v_inst_3100_, v_cls_3101_, v_collapsed_boxed_3113_, v_tag_3103_, v_opts_3104_, v_clsEnabled_boxed_3114_, v_toPure_3106_, v_toBind_3107_, v_k_3108_, v_inst_3109_, v_msg_3110_, v___f_3111_, v_oldTraces_3112_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object* v_inst_3116_, lean_object* v_always_3117_, lean_object* v_inst_3118_, lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_inst_3121_, lean_object* v_cls_3122_, uint8_t v_collapsed_3123_, lean_object* v_tag_3124_, lean_object* v_opts_3125_, lean_object* v_toPure_3126_, lean_object* v_toBind_3127_, lean_object* v_k_3128_, lean_object* v_inst_3129_, lean_object* v_msg_3130_, lean_object* v___f_3131_, uint8_t v_clsEnabled_3132_){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___f_3135_; 
v___x_3133_ = lean_box(v_collapsed_3123_);
v___x_3134_ = lean_box(v_clsEnabled_3132_);
lean_inc(v_k_3128_);
lean_inc(v_toBind_3127_);
lean_inc_ref(v_opts_3125_);
lean_inc_ref(v_inst_3119_);
lean_inc_ref(v_inst_3118_);
v___f_3135_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__2___boxed), 18, 17);
lean_closure_set(v___f_3135_, 0, v_inst_3116_);
lean_closure_set(v___f_3135_, 1, v_always_3117_);
lean_closure_set(v___f_3135_, 2, v_inst_3118_);
lean_closure_set(v___f_3135_, 3, v_inst_3119_);
lean_closure_set(v___f_3135_, 4, v_inst_3120_);
lean_closure_set(v___f_3135_, 5, v_inst_3121_);
lean_closure_set(v___f_3135_, 6, v_cls_3122_);
lean_closure_set(v___f_3135_, 7, v___x_3133_);
lean_closure_set(v___f_3135_, 8, v_tag_3124_);
lean_closure_set(v___f_3135_, 9, v_opts_3125_);
lean_closure_set(v___f_3135_, 10, v___x_3134_);
lean_closure_set(v___f_3135_, 11, v_toPure_3126_);
lean_closure_set(v___f_3135_, 12, v_toBind_3127_);
lean_closure_set(v___f_3135_, 13, v_k_3128_);
lean_closure_set(v___f_3135_, 14, v_inst_3129_);
lean_closure_set(v___f_3135_, 15, v_msg_3130_);
lean_closure_set(v___f_3135_, 16, v___f_3131_);
if (v_clsEnabled_3132_ == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3139_ = l_Lean_KVMap_instValueBool;
v___x_3140_ = l_Lean_trace_profiler;
v___x_3141_ = l_Lean_Option_get___redArg(v___x_3139_, v_opts_3125_, v___x_3140_);
lean_dec_ref(v_opts_3125_);
v___x_3142_ = lean_unbox(v___x_3141_);
lean_dec(v___x_3141_);
if (v___x_3142_ == 0)
{
lean_dec_ref(v___f_3135_);
lean_dec(v_toBind_3127_);
lean_dec_ref(v_inst_3119_);
lean_dec_ref(v_inst_3118_);
return v_k_3128_;
}
else
{
lean_dec(v_k_3128_);
goto v___jp_3136_;
}
}
else
{
lean_dec(v_k_3128_);
lean_dec_ref(v_opts_3125_);
goto v___jp_3136_;
}
v___jp_3136_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3118_, v_inst_3119_);
v___x_3138_ = lean_apply_4(v_toBind_3127_, lean_box(0), lean_box(0), v___x_3137_, v___f_3135_);
return v___x_3138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_3143_ = _args[0];
lean_object* v_always_3144_ = _args[1];
lean_object* v_inst_3145_ = _args[2];
lean_object* v_inst_3146_ = _args[3];
lean_object* v_inst_3147_ = _args[4];
lean_object* v_inst_3148_ = _args[5];
lean_object* v_cls_3149_ = _args[6];
lean_object* v_collapsed_3150_ = _args[7];
lean_object* v_tag_3151_ = _args[8];
lean_object* v_opts_3152_ = _args[9];
lean_object* v_toPure_3153_ = _args[10];
lean_object* v_toBind_3154_ = _args[11];
lean_object* v_k_3155_ = _args[12];
lean_object* v_inst_3156_ = _args[13];
lean_object* v_msg_3157_ = _args[14];
lean_object* v___f_3158_ = _args[15];
lean_object* v_clsEnabled_3159_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3160_; uint8_t v_clsEnabled_boxed_3161_; lean_object* v_res_3162_; 
v_collapsed_boxed_3160_ = lean_unbox(v_collapsed_3150_);
v_clsEnabled_boxed_3161_ = lean_unbox(v_clsEnabled_3159_);
v_res_3162_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3143_, v_always_3144_, v_inst_3145_, v_inst_3146_, v_inst_3147_, v_inst_3148_, v_cls_3149_, v_collapsed_boxed_3160_, v_tag_3151_, v_opts_3152_, v_toPure_3153_, v_toBind_3154_, v_k_3155_, v_inst_3156_, v_msg_3157_, v___f_3158_, v_clsEnabled_boxed_3161_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object* v_k_3163_, lean_object* v_inst_3164_, lean_object* v_toApplicative_3165_, lean_object* v_inst_3166_, lean_object* v_always_3167_, lean_object* v_inst_3168_, lean_object* v_inst_3169_, lean_object* v_inst_3170_, lean_object* v_cls_3171_, uint8_t v_collapsed_3172_, lean_object* v_tag_3173_, lean_object* v_toBind_3174_, lean_object* v_inst_3175_, lean_object* v_msg_3176_, lean_object* v___f_3177_, lean_object* v_inst_3178_, lean_object* v_opts_3179_){
_start:
{
uint8_t v_hasTrace_3180_; 
v_hasTrace_3180_ = lean_ctor_get_uint8(v_opts_3179_, sizeof(void*)*1);
if (v_hasTrace_3180_ == 0)
{
lean_dec_ref(v_opts_3179_);
lean_dec(v_inst_3178_);
lean_dec(v___f_3177_);
lean_dec(v_msg_3176_);
lean_dec(v_inst_3175_);
lean_dec(v_toBind_3174_);
lean_dec_ref(v_tag_3173_);
lean_dec(v_cls_3171_);
lean_dec_ref(v_inst_3170_);
lean_dec(v_inst_3169_);
lean_dec_ref(v_inst_3168_);
lean_dec_ref(v_always_3167_);
lean_dec_ref(v_inst_3166_);
lean_dec_ref(v_toApplicative_3165_);
lean_dec_ref(v_inst_3164_);
return v_k_3163_;
}
else
{
lean_object* v_getInheritedTraceOptions_3181_; lean_object* v_toPure_3182_; lean_object* v___x_3183_; lean_object* v___f_3184_; lean_object* v___f_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_getInheritedTraceOptions_3181_ = lean_ctor_get(v_inst_3164_, 2);
lean_inc(v_getInheritedTraceOptions_3181_);
v_toPure_3182_ = lean_ctor_get(v_toApplicative_3165_, 1);
lean_inc_n(v_toPure_3182_, 2);
lean_dec_ref(v_toApplicative_3165_);
v___x_3183_ = lean_box(v_collapsed_3172_);
lean_inc_n(v_toBind_3174_, 3);
lean_inc(v_cls_3171_);
v___f_3184_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_3184_, 0, v_inst_3166_);
lean_closure_set(v___f_3184_, 1, v_always_3167_);
lean_closure_set(v___f_3184_, 2, v_inst_3168_);
lean_closure_set(v___f_3184_, 3, v_inst_3164_);
lean_closure_set(v___f_3184_, 4, v_inst_3169_);
lean_closure_set(v___f_3184_, 5, v_inst_3170_);
lean_closure_set(v___f_3184_, 6, v_cls_3171_);
lean_closure_set(v___f_3184_, 7, v___x_3183_);
lean_closure_set(v___f_3184_, 8, v_tag_3173_);
lean_closure_set(v___f_3184_, 9, v_opts_3179_);
lean_closure_set(v___f_3184_, 10, v_toPure_3182_);
lean_closure_set(v___f_3184_, 11, v_toBind_3174_);
lean_closure_set(v___f_3184_, 12, v_k_3163_);
lean_closure_set(v___f_3184_, 13, v_inst_3175_);
lean_closure_set(v___f_3184_, 14, v_msg_3176_);
lean_closure_set(v___f_3184_, 15, v___f_3177_);
v___f_3185_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3185_, 0, v_toPure_3182_);
lean_closure_set(v___f_3185_, 1, v_cls_3171_);
lean_closure_set(v___f_3185_, 2, v_toBind_3174_);
lean_closure_set(v___f_3185_, 3, v_inst_3178_);
v___x_3186_ = lean_apply_4(v_toBind_3174_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3181_, v___f_3185_);
v___x_3187_ = lean_apply_4(v_toBind_3174_, lean_box(0), lean_box(0), v___x_3186_, v___f_3184_);
return v___x_3187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_k_3188_ = _args[0];
lean_object* v_inst_3189_ = _args[1];
lean_object* v_toApplicative_3190_ = _args[2];
lean_object* v_inst_3191_ = _args[3];
lean_object* v_always_3192_ = _args[4];
lean_object* v_inst_3193_ = _args[5];
lean_object* v_inst_3194_ = _args[6];
lean_object* v_inst_3195_ = _args[7];
lean_object* v_cls_3196_ = _args[8];
lean_object* v_collapsed_3197_ = _args[9];
lean_object* v_tag_3198_ = _args[10];
lean_object* v_toBind_3199_ = _args[11];
lean_object* v_inst_3200_ = _args[12];
lean_object* v_msg_3201_ = _args[13];
lean_object* v___f_3202_ = _args[14];
lean_object* v_inst_3203_ = _args[15];
lean_object* v_opts_3204_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_3205_; lean_object* v_res_3206_; 
v_collapsed_boxed_3205_ = lean_unbox(v_collapsed_3197_);
v_res_3206_ = l_Lean_withTraceNodeBefore___redArg___lam__7(v_k_3188_, v_inst_3189_, v_toApplicative_3190_, v_inst_3191_, v_always_3192_, v_inst_3193_, v_inst_3194_, v_inst_3195_, v_cls_3196_, v_collapsed_boxed_3205_, v_tag_3198_, v_toBind_3199_, v_inst_3200_, v_msg_3201_, v___f_3202_, v_inst_3203_, v_opts_3204_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object* v_inst_3207_, lean_object* v_inst_3208_, lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_always_3212_, lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_cls_3215_, lean_object* v_msg_3216_, lean_object* v_k_3217_, uint8_t v_collapsed_3218_, lean_object* v_tag_3219_){
_start:
{
lean_object* v_toApplicative_3220_; lean_object* v_toBind_3221_; lean_object* v___f_3222_; lean_object* v___x_3223_; lean_object* v___f_3224_; lean_object* v___x_3225_; 
v_toApplicative_3220_ = lean_ctor_get(v_inst_3207_, 0);
lean_inc_ref(v_toApplicative_3220_);
v_toBind_3221_ = lean_ctor_get(v_inst_3207_, 1);
lean_inc_n(v_toBind_3221_, 2);
lean_inc(v_inst_3210_);
v___f_3222_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3222_, 0, v_inst_3210_);
v___x_3223_ = lean_box(v_collapsed_3218_);
lean_inc(v_inst_3211_);
v___f_3224_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3224_, 0, v_k_3217_);
lean_closure_set(v___f_3224_, 1, v_inst_3208_);
lean_closure_set(v___f_3224_, 2, v_toApplicative_3220_);
lean_closure_set(v___f_3224_, 3, v_inst_3209_);
lean_closure_set(v___f_3224_, 4, v_always_3212_);
lean_closure_set(v___f_3224_, 5, v_inst_3207_);
lean_closure_set(v___f_3224_, 6, v_inst_3210_);
lean_closure_set(v___f_3224_, 7, v_inst_3214_);
lean_closure_set(v___f_3224_, 8, v_cls_3215_);
lean_closure_set(v___f_3224_, 9, v___x_3223_);
lean_closure_set(v___f_3224_, 10, v_tag_3219_);
lean_closure_set(v___f_3224_, 11, v_toBind_3221_);
lean_closure_set(v___f_3224_, 12, v_inst_3213_);
lean_closure_set(v___f_3224_, 13, v_msg_3216_);
lean_closure_set(v___f_3224_, 14, v___f_3222_);
lean_closure_set(v___f_3224_, 15, v_inst_3211_);
v___x_3225_ = lean_apply_4(v_toBind_3221_, lean_box(0), lean_box(0), v_inst_3211_, v___f_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object* v_inst_3226_, lean_object* v_inst_3227_, lean_object* v_inst_3228_, lean_object* v_inst_3229_, lean_object* v_inst_3230_, lean_object* v_always_3231_, lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_cls_3234_, lean_object* v_msg_3235_, lean_object* v_k_3236_, lean_object* v_collapsed_3237_, lean_object* v_tag_3238_){
_start:
{
uint8_t v_collapsed_boxed_3239_; lean_object* v_res_3240_; 
v_collapsed_boxed_3239_ = lean_unbox(v_collapsed_3237_);
v_res_3240_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3226_, v_inst_3227_, v_inst_3228_, v_inst_3229_, v_inst_3230_, v_always_3231_, v_inst_3232_, v_inst_3233_, v_cls_3234_, v_msg_3235_, v_k_3236_, v_collapsed_boxed_3239_, v_tag_3238_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object* v_00_u03b1_3241_, lean_object* v_m_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_00_u03b5_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_always_3249_, lean_object* v_inst_3250_, lean_object* v_inst_3251_, lean_object* v_cls_3252_, lean_object* v_msg_3253_, lean_object* v_k_3254_, uint8_t v_collapsed_3255_, lean_object* v_tag_3256_){
_start:
{
lean_object* v_toApplicative_3257_; lean_object* v_toBind_3258_; lean_object* v___f_3259_; lean_object* v___x_3260_; lean_object* v___f_3261_; lean_object* v___x_3262_; 
v_toApplicative_3257_ = lean_ctor_get(v_inst_3243_, 0);
lean_inc_ref(v_toApplicative_3257_);
v_toBind_3258_ = lean_ctor_get(v_inst_3243_, 1);
lean_inc_n(v_toBind_3258_, 2);
lean_inc(v_inst_3247_);
v___f_3259_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3259_, 0, v_inst_3247_);
v___x_3260_ = lean_box(v_collapsed_3255_);
lean_inc(v_inst_3248_);
v___f_3261_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_3261_, 0, v_k_3254_);
lean_closure_set(v___f_3261_, 1, v_inst_3244_);
lean_closure_set(v___f_3261_, 2, v_toApplicative_3257_);
lean_closure_set(v___f_3261_, 3, v_inst_3246_);
lean_closure_set(v___f_3261_, 4, v_always_3249_);
lean_closure_set(v___f_3261_, 5, v_inst_3243_);
lean_closure_set(v___f_3261_, 6, v_inst_3247_);
lean_closure_set(v___f_3261_, 7, v_inst_3251_);
lean_closure_set(v___f_3261_, 8, v_cls_3252_);
lean_closure_set(v___f_3261_, 9, v___x_3260_);
lean_closure_set(v___f_3261_, 10, v_tag_3256_);
lean_closure_set(v___f_3261_, 11, v_toBind_3258_);
lean_closure_set(v___f_3261_, 12, v_inst_3250_);
lean_closure_set(v___f_3261_, 13, v_msg_3253_);
lean_closure_set(v___f_3261_, 14, v___f_3259_);
lean_closure_set(v___f_3261_, 15, v_inst_3248_);
v___x_3262_ = lean_apply_4(v_toBind_3258_, lean_box(0), lean_box(0), v_inst_3248_, v___f_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object* v_00_u03b1_3263_, lean_object* v_m_3264_, lean_object* v_inst_3265_, lean_object* v_inst_3266_, lean_object* v_00_u03b5_3267_, lean_object* v_inst_3268_, lean_object* v_inst_3269_, lean_object* v_inst_3270_, lean_object* v_always_3271_, lean_object* v_inst_3272_, lean_object* v_inst_3273_, lean_object* v_cls_3274_, lean_object* v_msg_3275_, lean_object* v_k_3276_, lean_object* v_collapsed_3277_, lean_object* v_tag_3278_){
_start:
{
uint8_t v_collapsed_boxed_3279_; lean_object* v_res_3280_; 
v_collapsed_boxed_3279_ = lean_unbox(v_collapsed_3277_);
v_res_3280_ = l_Lean_withTraceNodeBefore(v_00_u03b1_3263_, v_m_3264_, v_inst_3265_, v_inst_3266_, v_00_u03b5_3267_, v_inst_3268_, v_inst_3269_, v_inst_3270_, v_always_3271_, v_inst_3272_, v_inst_3273_, v_cls_3274_, v_msg_3275_, v_k_3276_, v_collapsed_boxed_3279_, v_tag_3278_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0(lean_object* v_toApplicative_3281_, lean_object* v_____s_3282_){
_start:
{
lean_object* v_toPure_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_toPure_3283_ = lean_ctor_get(v_toApplicative_3281_, 1);
lean_inc(v_toPure_3283_);
lean_dec_ref(v_toApplicative_3281_);
v___x_3284_ = lean_box(0);
v___x_3285_ = lean_apply_2(v_toPure_3283_, lean_box(0), v___x_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__1(lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v_fst_3288_; lean_object* v_fst_3289_; lean_object* v_fst_3290_; lean_object* v_fst_3291_; uint8_t v___x_3292_; 
v_fst_3288_ = lean_ctor_get(v_x_3286_, 0);
v_fst_3289_ = lean_ctor_get(v_x_3287_, 0);
v_fst_3290_ = lean_ctor_get(v_fst_3288_, 0);
v_fst_3291_ = lean_ctor_get(v_fst_3289_, 0);
v___x_3292_ = lean_nat_dec_lt(v_fst_3290_, v_fst_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1___boxed(lean_object* v_x_3293_, lean_object* v_x_3294_){
_start:
{
uint8_t v_res_3295_; lean_object* v_r_3296_; 
v_res_3295_ = l_Lean_addTraceAsMessages___redArg___lam__1(v_x_3293_, v_x_3294_);
lean_dec_ref(v_x_3294_);
lean_dec_ref(v_x_3293_);
v_r_3296_ = lean_box(v_res_3295_);
return v_r_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object* v_x1_3297_, lean_object* v_x2_3298_, lean_object* v_x3_3299_){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v_x2_3298_);
lean_ctor_set(v___x_3300_, 1, v_x3_3299_);
v___x_3301_ = lean_array_push(v_x1_3297_, v___x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object* v_toApplicative_3302_, lean_object* v___x_3303_, lean_object* v_r_3304_){
_start:
{
lean_object* v_toPure_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_toPure_3305_ = lean_ctor_get(v_toApplicative_3302_, 1);
lean_inc(v_toPure_3305_);
lean_dec_ref(v_toApplicative_3302_);
v___x_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3303_);
v___x_3307_ = lean_apply_2(v_toPure_3305_, lean_box(0), v___x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object* v_____do__lift_3308_, lean_object* v___x_3309_, lean_object* v_fst_3310_, lean_object* v_snd_3311_, lean_object* v_logMessage_3312_, lean_object* v_toBind_3313_, lean_object* v___f_3314_, lean_object* v_____do__lift_3315_){
_start:
{
uint8_t v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3316_ = 0;
v___x_3317_ = l_Lean_Elab_mkMessageCore(v_____do__lift_3308_, v_____do__lift_3315_, v___x_3309_, v___x_3316_, v_fst_3310_, v_snd_3311_);
v___x_3318_ = lean_apply_1(v_logMessage_3312_, v___x_3317_);
v___x_3319_ = lean_apply_4(v_toBind_3313_, lean_box(0), lean_box(0), v___x_3318_, v___f_3314_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object* v_____do__lift_3320_, lean_object* v___x_3321_, lean_object* v_fst_3322_, lean_object* v_snd_3323_, lean_object* v_logMessage_3324_, lean_object* v_toBind_3325_, lean_object* v___f_3326_, lean_object* v_____do__lift_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_addTraceAsMessages___redArg___lam__4(v_____do__lift_3320_, v___x_3321_, v_fst_3322_, v_snd_3323_, v_logMessage_3324_, v_toBind_3325_, v___f_3326_, v_____do__lift_3327_);
lean_dec(v_snd_3323_);
lean_dec(v_fst_3322_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object* v___x_3329_, lean_object* v_fst_3330_, lean_object* v_snd_3331_, lean_object* v_logMessage_3332_, lean_object* v_toBind_3333_, lean_object* v___f_3334_, lean_object* v_toMonadFileMap_3335_, lean_object* v_____do__lift_3336_){
_start:
{
lean_object* v___f_3337_; lean_object* v___x_3338_; 
lean_inc(v_toBind_3333_);
v___f_3337_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_3337_, 0, v_____do__lift_3336_);
lean_closure_set(v___f_3337_, 1, v___x_3329_);
lean_closure_set(v___f_3337_, 2, v_fst_3330_);
lean_closure_set(v___f_3337_, 3, v_snd_3331_);
lean_closure_set(v___f_3337_, 4, v_logMessage_3332_);
lean_closure_set(v___f_3337_, 5, v_toBind_3333_);
lean_closure_set(v___f_3337_, 6, v___f_3334_);
v___x_3338_ = lean_apply_4(v_toBind_3333_, lean_box(0), lean_box(0), v_toMonadFileMap_3335_, v___f_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object* v___x_3339_, uint8_t v___x_3340_, lean_object* v_inst_3341_, lean_object* v_toBind_3342_, lean_object* v___f_3343_, lean_object* v_a_3344_, lean_object* v_x_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_fst_3347_; lean_object* v_snd_3348_; lean_object* v_fst_3349_; lean_object* v_snd_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3370_; 
v_fst_3347_ = lean_ctor_get(v_a_3344_, 0);
lean_inc(v_fst_3347_);
v_snd_3348_ = lean_ctor_get(v_a_3344_, 1);
lean_inc(v_snd_3348_);
lean_dec_ref(v_a_3344_);
v_fst_3349_ = lean_ctor_get(v_fst_3347_, 0);
v_snd_3350_ = lean_ctor_get(v_fst_3347_, 1);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_fst_3347_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3352_ = v_fst_3347_;
v_isShared_3353_ = v_isSharedCheck_3370_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_snd_3350_);
lean_inc(v_fst_3349_);
lean_dec(v_fst_3347_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3370_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; double v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v_toMonadFileMap_3359_; lean_object* v_getFileName_3360_; lean_object* v_logMessage_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3354_ = lean_box(0);
v___x_3355_ = lean_box(0);
v___x_3356_ = lean_float_of_nat(v___x_3339_);
v___x_3357_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_3358_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3358_, 0, v___x_3354_);
lean_ctor_set(v___x_3358_, 1, v___x_3355_);
lean_ctor_set(v___x_3358_, 2, v___x_3357_);
lean_ctor_set_float(v___x_3358_, sizeof(void*)*3, v___x_3356_);
lean_ctor_set_float(v___x_3358_, sizeof(void*)*3 + 8, v___x_3356_);
lean_ctor_set_uint8(v___x_3358_, sizeof(void*)*3 + 16, v___x_3340_);
v_toMonadFileMap_3359_ = lean_ctor_get(v_inst_3341_, 0);
lean_inc(v_toMonadFileMap_3359_);
v_getFileName_3360_ = lean_ctor_get(v_inst_3341_, 2);
lean_inc(v_getFileName_3360_);
v_logMessage_3361_ = lean_ctor_get(v_inst_3341_, 4);
lean_inc(v_logMessage_3361_);
lean_dec_ref(v_inst_3341_);
v___x_3362_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_3363_ = l_Lean_MessageData_nil;
v___x_3364_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3358_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
lean_ctor_set(v___x_3364_, 2, v_snd_3348_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set_tag(v___x_3352_, 8);
lean_ctor_set(v___x_3352_, 1, v___x_3364_);
lean_ctor_set(v___x_3352_, 0, v___x_3362_);
v___x_3366_ = v___x_3352_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___f_3367_; lean_object* v___x_3368_; 
lean_inc(v_toBind_3342_);
v___f_3367_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__5), 8, 7);
lean_closure_set(v___f_3367_, 0, v___x_3366_);
lean_closure_set(v___f_3367_, 1, v_fst_3349_);
lean_closure_set(v___f_3367_, 2, v_snd_3350_);
lean_closure_set(v___f_3367_, 3, v_logMessage_3361_);
lean_closure_set(v___f_3367_, 4, v_toBind_3342_);
lean_closure_set(v___f_3367_, 5, v___f_3343_);
lean_closure_set(v___f_3367_, 6, v_toMonadFileMap_3359_);
v___x_3368_ = lean_apply_4(v_toBind_3342_, lean_box(0), lean_box(0), v_getFileName_3360_, v___f_3367_);
return v___x_3368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object* v___x_3371_, lean_object* v___x_3372_, lean_object* v_inst_3373_, lean_object* v_toBind_3374_, lean_object* v___f_3375_, lean_object* v_a_3376_, lean_object* v_x_3377_, lean_object* v___y_3378_){
_start:
{
uint8_t v___x_1730__boxed_3379_; lean_object* v_res_3380_; 
v___x_1730__boxed_3379_ = lean_unbox(v___x_3372_);
v_res_3380_ = l_Lean_addTraceAsMessages___redArg___lam__6(v___x_3371_, v___x_1730__boxed_3379_, v_inst_3373_, v_toBind_3374_, v___f_3375_, v_a_3376_, v_x_3377_, v___y_3378_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object* v___x_3381_, lean_object* v___f_3382_, lean_object* v_acc_3383_, lean_object* v_l_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_3381_, v___f_3382_, v_acc_3383_, v_l_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object* v_toApplicative_3386_, uint8_t v___x_3387_, lean_object* v_inst_3388_, lean_object* v_toBind_3389_, lean_object* v_inst_3390_, lean_object* v___f_3391_, lean_object* v___f_3392_, lean_object* v___f_3393_, lean_object* v_____s_3394_){
_start:
{
lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3421_; lean_object* v_size_3428_; lean_object* v_buckets_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v_size_3428_ = lean_ctor_get(v_____s_3394_, 0);
lean_inc(v_size_3428_);
v_buckets_3429_ = lean_ctor_get(v_____s_3394_, 1);
lean_inc_ref(v_buckets_3429_);
lean_dec_ref(v_____s_3394_);
v___x_3430_ = lean_mk_empty_array_with_capacity(v_size_3428_);
lean_dec(v_size_3428_);
v___x_3431_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = lean_array_get_size(v_buckets_3429_);
v___x_3434_ = lean_nat_dec_lt(v___x_3432_, v___x_3433_);
if (v___x_3434_ == 0)
{
lean_dec_ref(v_buckets_3429_);
lean_dec_ref(v___f_3393_);
v___y_3421_ = v___x_3430_;
goto v___jp_3420_;
}
else
{
lean_object* v___f_3435_; uint8_t v___x_3436_; 
v___f_3435_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__7), 4, 2);
lean_closure_set(v___f_3435_, 0, v___x_3431_);
lean_closure_set(v___f_3435_, 1, v___f_3393_);
v___x_3436_ = lean_nat_dec_le(v___x_3433_, v___x_3433_);
if (v___x_3436_ == 0)
{
if (v___x_3434_ == 0)
{
lean_dec_ref(v___f_3435_);
lean_dec_ref(v_buckets_3429_);
v___y_3421_ = v___x_3430_;
goto v___jp_3420_;
}
else
{
size_t v___x_3437_; size_t v___x_3438_; lean_object* v___x_3439_; 
v___x_3437_ = ((size_t)0ULL);
v___x_3438_ = lean_usize_of_nat(v___x_3433_);
v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3431_, v___f_3435_, v_buckets_3429_, v___x_3437_, v___x_3438_, v___x_3430_);
v___y_3421_ = v___x_3439_;
goto v___jp_3420_;
}
}
else
{
size_t v___x_3440_; size_t v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = ((size_t)0ULL);
v___x_3441_ = lean_usize_of_nat(v___x_3433_);
v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3431_, v___f_3435_, v_buckets_3429_, v___x_3440_, v___x_3441_, v___x_3430_);
v___y_3421_ = v___x_3442_;
goto v___jp_3420_;
}
}
v___jp_3395_:
{
lean_object* v___x_3398_; lean_object* v___f_3399_; lean_object* v___x_3400_; lean_object* v___f_3401_; size_t v_sz_3402_; size_t v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3398_ = lean_box(0);
v___f_3399_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__3), 3, 2);
lean_closure_set(v___f_3399_, 0, v_toApplicative_3386_);
lean_closure_set(v___f_3399_, 1, v___x_3398_);
v___x_3400_ = lean_box(v___x_3387_);
lean_inc(v_toBind_3389_);
v___f_3401_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__6___boxed), 8, 5);
lean_closure_set(v___f_3401_, 0, v___y_3396_);
lean_closure_set(v___f_3401_, 1, v___x_3400_);
lean_closure_set(v___f_3401_, 2, v_inst_3388_);
lean_closure_set(v___f_3401_, 3, v_toBind_3389_);
lean_closure_set(v___f_3401_, 4, v___f_3399_);
v_sz_3402_ = lean_array_size(v___y_3397_);
v___x_3403_ = ((size_t)0ULL);
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3390_, v___y_3397_, v___f_3401_, v_sz_3402_, v___x_3403_, v___x_3398_);
v___x_3405_ = lean_apply_4(v_toBind_3389_, lean_box(0), lean_box(0), v___x_3404_, v___f_3391_);
return v___x_3405_;
}
v___jp_3406_:
{
lean_object* v___x_3412_; 
v___x_3412_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_3392_, v___y_3410_, v___y_3409_, v___y_3408_, v___y_3411_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_3411_);
lean_dec(v___y_3410_);
v___y_3396_ = v___y_3407_;
v___y_3397_ = v___x_3412_;
goto v___jp_3395_;
}
v___jp_3413_:
{
uint8_t v___x_3419_; 
v___x_3419_ = lean_nat_dec_le(v___y_3418_, v___y_3416_);
if (v___x_3419_ == 0)
{
lean_dec(v___y_3416_);
lean_inc(v___y_3418_);
v___y_3407_ = v___y_3414_;
v___y_3408_ = v___y_3418_;
v___y_3409_ = v___y_3415_;
v___y_3410_ = v___y_3417_;
v___y_3411_ = v___y_3418_;
goto v___jp_3406_;
}
else
{
v___y_3407_ = v___y_3414_;
v___y_3408_ = v___y_3418_;
v___y_3409_ = v___y_3415_;
v___y_3410_ = v___y_3417_;
v___y_3411_ = v___y_3416_;
goto v___jp_3406_;
}
}
v___jp_3420_:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3422_ = lean_unsigned_to_nat(0u);
v___x_3423_ = lean_array_get_size(v___y_3421_);
v___x_3424_ = lean_nat_dec_eq(v___x_3423_, v___x_3422_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3425_ = lean_unsigned_to_nat(1u);
v___x_3426_ = lean_nat_sub(v___x_3423_, v___x_3425_);
v___x_3427_ = lean_nat_dec_le(v___x_3422_, v___x_3426_);
if (v___x_3427_ == 0)
{
lean_inc(v___x_3426_);
v___y_3414_ = v___x_3422_;
v___y_3415_ = v___y_3421_;
v___y_3416_ = v___x_3426_;
v___y_3417_ = v___x_3423_;
v___y_3418_ = v___x_3426_;
goto v___jp_3413_;
}
else
{
v___y_3414_ = v___x_3422_;
v___y_3415_ = v___y_3421_;
v___y_3416_ = v___x_3426_;
v___y_3417_ = v___x_3423_;
v___y_3418_ = v___x_3422_;
goto v___jp_3413_;
}
}
else
{
lean_dec_ref(v___f_3392_);
v___y_3396_ = v___x_3422_;
v___y_3397_ = v___y_3421_;
goto v___jp_3395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object* v_toApplicative_3443_, lean_object* v___x_3444_, lean_object* v_inst_3445_, lean_object* v_toBind_3446_, lean_object* v_inst_3447_, lean_object* v___f_3448_, lean_object* v___f_3449_, lean_object* v___f_3450_, lean_object* v_____s_3451_){
_start:
{
uint8_t v___x_1818__boxed_3452_; lean_object* v_res_3453_; 
v___x_1818__boxed_3452_ = lean_unbox(v___x_3444_);
v_res_3453_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_toApplicative_3443_, v___x_1818__boxed_3452_, v_inst_3445_, v_toBind_3446_, v_inst_3447_, v___f_3448_, v___f_3449_, v___f_3450_, v_____s_3451_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object* v_traceElem_3454_, lean_object* v_toApplicative_3455_, lean_object* v___f_3456_, lean_object* v___f_3457_, lean_object* v_____s_3458_, uint8_t v___x_3459_, lean_object* v_____do__lift_3460_){
_start:
{
lean_object* v_ref_3461_; lean_object* v_msg_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3487_; 
v_ref_3461_ = lean_ctor_get(v_traceElem_3454_, 0);
v_msg_3462_ = lean_ctor_get(v_traceElem_3454_, 1);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_traceElem_3454_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3464_ = v_traceElem_3454_;
v_isShared_3465_ = v_isSharedCheck_3487_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_msg_3462_);
lean_inc(v_ref_3461_);
lean_dec(v_traceElem_3454_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3487_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v_ref_3479_; lean_object* v___y_3481_; lean_object* v___x_3484_; 
v_ref_3479_ = l_Lean_replaceRef(v_ref_3461_, v_____do__lift_3460_);
lean_dec(v_ref_3461_);
v___x_3484_ = l_Lean_Syntax_getPos_x3f(v_ref_3479_, v___x_3459_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_unsigned_to_nat(0u);
v___y_3481_ = v___x_3485_;
goto v___jp_3480_;
}
else
{
lean_object* v_val_3486_; 
v_val_3486_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_val_3486_);
lean_dec_ref_known(v___x_3484_, 1);
v___y_3481_ = v_val_3486_;
goto v___jp_3480_;
}
v___jp_3466_:
{
lean_object* v_toPure_3469_; lean_object* v___x_3471_; 
v_toPure_3469_ = lean_ctor_get(v_toApplicative_3455_, 1);
lean_inc(v_toPure_3469_);
lean_dec_ref(v_toApplicative_3455_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 1, v___y_3468_);
lean_ctor_set(v___x_3464_, 0, v___y_3467_);
v___x_3471_ = v___x_3464_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___y_3467_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___y_3468_);
v___x_3471_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v_pos2traces_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3472_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
lean_inc_ref(v___x_3471_);
lean_inc_ref(v___f_3457_);
lean_inc_ref(v___f_3456_);
v___x_3473_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_3456_, v___f_3457_, v_____s_3458_, v___x_3471_, v___x_3472_);
v___x_3474_ = lean_array_push(v___x_3473_, v_msg_3462_);
v_pos2traces_3475_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3456_, v___f_3457_, v_____s_3458_, v___x_3471_, v___x_3474_);
v___x_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3476_, 0, v_pos2traces_3475_);
v___x_3477_ = lean_apply_2(v_toPure_3469_, lean_box(0), v___x_3476_);
return v___x_3477_;
}
}
v___jp_3480_:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Lean_Syntax_getTailPos_x3f(v_ref_3479_, v___x_3459_);
lean_dec(v_ref_3479_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_inc(v___y_3481_);
v___y_3467_ = v___y_3481_;
v___y_3468_ = v___y_3481_;
goto v___jp_3466_;
}
else
{
lean_object* v_val_3483_; 
v_val_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_val_3483_);
lean_dec_ref_known(v___x_3482_, 1);
v___y_3467_ = v___y_3481_;
v___y_3468_ = v_val_3483_;
goto v___jp_3466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object* v_traceElem_3488_, lean_object* v_toApplicative_3489_, lean_object* v___f_3490_, lean_object* v___f_3491_, lean_object* v_____s_3492_, lean_object* v___x_3493_, lean_object* v_____do__lift_3494_){
_start:
{
uint8_t v___x_1943__boxed_3495_; lean_object* v_res_3496_; 
v___x_1943__boxed_3495_ = lean_unbox(v___x_3493_);
v_res_3496_ = l_Lean_addTraceAsMessages___redArg___lam__9(v_traceElem_3488_, v_toApplicative_3489_, v___f_3490_, v___f_3491_, v_____s_3492_, v___x_1943__boxed_3495_, v_____do__lift_3494_);
lean_dec(v_____do__lift_3494_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object* v_inst_3497_, lean_object* v_toApplicative_3498_, lean_object* v___f_3499_, lean_object* v___f_3500_, uint8_t v___x_3501_, lean_object* v_toBind_3502_, lean_object* v_traceElem_3503_, lean_object* v_____s_3504_){
_start:
{
lean_object* v_getRef_3505_; lean_object* v___x_3506_; lean_object* v___f_3507_; lean_object* v___x_3508_; 
v_getRef_3505_ = lean_ctor_get(v_inst_3497_, 0);
lean_inc(v_getRef_3505_);
lean_dec_ref(v_inst_3497_);
v___x_3506_ = lean_box(v___x_3501_);
v___f_3507_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_3507_, 0, v_traceElem_3503_);
lean_closure_set(v___f_3507_, 1, v_toApplicative_3498_);
lean_closure_set(v___f_3507_, 2, v___f_3499_);
lean_closure_set(v___f_3507_, 3, v___f_3500_);
lean_closure_set(v___f_3507_, 4, v_____s_3504_);
lean_closure_set(v___f_3507_, 5, v___x_3506_);
v___x_3508_ = lean_apply_4(v_toBind_3502_, lean_box(0), lean_box(0), v_getRef_3505_, v___f_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object* v_inst_3509_, lean_object* v_toApplicative_3510_, lean_object* v___f_3511_, lean_object* v___f_3512_, lean_object* v___x_3513_, lean_object* v_toBind_3514_, lean_object* v_traceElem_3515_, lean_object* v_____s_3516_){
_start:
{
uint8_t v___x_2003__boxed_3517_; lean_object* v_res_3518_; 
v___x_2003__boxed_3517_ = lean_unbox(v___x_3513_);
v_res_3518_ = l_Lean_addTraceAsMessages___redArg___lam__10(v_inst_3509_, v_toApplicative_3510_, v___f_3511_, v___f_3512_, v___x_2003__boxed_3517_, v_toBind_3514_, v_traceElem_3515_, v_____s_3516_);
return v_res_3518_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___f_3520_; 
v___x_3519_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_3520_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3520_, 0, v___x_3519_);
return v___f_3520_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___f_3521_; lean_object* v___f_3522_; 
v___f_3521_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__0, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__0_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__0);
v___f_3522_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3522_, 0, v___f_3521_);
lean_closure_set(v___f_3522_, 1, v___f_3521_);
return v___f_3522_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3526_ = lean_box(0);
v___x_3527_ = lean_unsigned_to_nat(16u);
v___x_3528_ = lean_mk_array(v___x_3527_, v___x_3526_);
return v___x_3528_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v_pos2traces_3531_; 
v___x_3529_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__4, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__4_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__4);
v___x_3530_ = lean_unsigned_to_nat(0u);
v_pos2traces_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_3531_, 0, v___x_3530_);
lean_ctor_set(v_pos2traces_3531_, 1, v___x_3529_);
return v_pos2traces_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11(lean_object* v_inst_3532_, lean_object* v_toApplicative_3533_, lean_object* v_toBind_3534_, lean_object* v_inst_3535_, lean_object* v___f_3536_, lean_object* v_traces_3537_){
_start:
{
uint8_t v___x_3538_; 
v___x_3538_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_3537_);
if (v___x_3538_ == 0)
{
lean_object* v___f_3539_; lean_object* v___f_3540_; lean_object* v___x_3541_; lean_object* v___f_3542_; lean_object* v_pos2traces_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___f_3539_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__1, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__1_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__1);
v___f_3540_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___lam__11___closed__3));
v___x_3541_ = lean_box(v___x_3538_);
lean_inc(v_toBind_3534_);
v___f_3542_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_3542_, 0, v_inst_3532_);
lean_closure_set(v___f_3542_, 1, v_toApplicative_3533_);
lean_closure_set(v___f_3542_, 2, v___f_3539_);
lean_closure_set(v___f_3542_, 3, v___f_3540_);
lean_closure_set(v___f_3542_, 4, v___x_3541_);
lean_closure_set(v___f_3542_, 5, v_toBind_3534_);
v_pos2traces_3543_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__11___closed__5, &l_Lean_addTraceAsMessages___redArg___lam__11___closed__5_once, _init_l_Lean_addTraceAsMessages___redArg___lam__11___closed__5);
v___x_3544_ = l_Lean_PersistentArray_forIn___redArg(v_inst_3535_, v_traces_3537_, v_pos2traces_3543_, v___f_3542_);
v___x_3545_ = lean_apply_4(v_toBind_3534_, lean_box(0), lean_box(0), v___x_3544_, v___f_3536_);
return v___x_3545_;
}
else
{
lean_object* v_toPure_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
lean_dec(v___f_3536_);
lean_dec_ref(v_inst_3535_);
lean_dec(v_toBind_3534_);
lean_dec_ref(v_inst_3532_);
v_toPure_3546_ = lean_ctor_get(v_toApplicative_3533_, 1);
lean_inc(v_toPure_3546_);
lean_dec_ref(v_toApplicative_3533_);
v___x_3547_ = lean_box(0);
v___x_3548_ = lean_apply_2(v_toPure_3546_, lean_box(0), v___x_3547_);
return v___x_3548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__11___boxed(lean_object* v_inst_3549_, lean_object* v_toApplicative_3550_, lean_object* v_toBind_3551_, lean_object* v_inst_3552_, lean_object* v___f_3553_, lean_object* v_traces_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_addTraceAsMessages___redArg___lam__11(v_inst_3549_, v_toApplicative_3550_, v_toBind_3551_, v_inst_3552_, v___f_3553_, v_traces_3554_);
lean_dec_ref(v_traces_3554_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12(lean_object* v_toApplicative_3556_, lean_object* v_inst_3557_, lean_object* v_toBind_3558_, lean_object* v_inst_3559_, lean_object* v___f_3560_, lean_object* v___f_3561_, lean_object* v___f_3562_, lean_object* v_inst_3563_, lean_object* v_inst_3564_, lean_object* v_____do__lift_3565_){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3570_ = l_Lean_KVMap_instValueBool;
v___x_3571_ = l_Lean_KVMap_instValueString;
v___x_3572_ = l_Lean_trace_profiler_output;
v___x_3573_ = l_Lean_Option_get_x3f___redArg(v___x_3571_, v_____do__lift_3565_, v___x_3572_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3574_ = l_Lean_trace_profiler_serve;
v___x_3575_ = l_Lean_Option_get___redArg(v___x_3570_, v_____do__lift_3565_, v___x_3574_);
v___x_3576_ = lean_unbox(v___x_3575_);
lean_dec(v___x_3575_);
if (v___x_3576_ == 0)
{
uint8_t v___x_3577_; lean_object* v___x_3578_; lean_object* v___f_3579_; lean_object* v___f_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3577_ = 1;
v___x_3578_ = lean_box(v___x_3577_);
lean_inc_ref_n(v_inst_3559_, 2);
lean_inc_n(v_toBind_3558_, 2);
lean_inc_ref(v_toApplicative_3556_);
v___f_3579_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__8___boxed), 9, 8);
lean_closure_set(v___f_3579_, 0, v_toApplicative_3556_);
lean_closure_set(v___f_3579_, 1, v___x_3578_);
lean_closure_set(v___f_3579_, 2, v_inst_3557_);
lean_closure_set(v___f_3579_, 3, v_toBind_3558_);
lean_closure_set(v___f_3579_, 4, v_inst_3559_);
lean_closure_set(v___f_3579_, 5, v___f_3560_);
lean_closure_set(v___f_3579_, 6, v___f_3561_);
lean_closure_set(v___f_3579_, 7, v___f_3562_);
v___f_3580_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__11___boxed), 6, 5);
lean_closure_set(v___f_3580_, 0, v_inst_3563_);
lean_closure_set(v___f_3580_, 1, v_toApplicative_3556_);
lean_closure_set(v___f_3580_, 2, v_toBind_3558_);
lean_closure_set(v___f_3580_, 3, v_inst_3559_);
lean_closure_set(v___f_3580_, 4, v___f_3579_);
v___x_3581_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3559_, v_inst_3564_);
v___x_3582_ = lean_apply_4(v_toBind_3558_, lean_box(0), lean_box(0), v___x_3581_, v___f_3580_);
return v___x_3582_;
}
else
{
lean_dec_ref(v_inst_3564_);
lean_dec_ref(v_inst_3563_);
lean_dec_ref(v___f_3562_);
lean_dec_ref(v___f_3561_);
lean_dec(v___f_3560_);
lean_dec_ref(v_inst_3559_);
lean_dec(v_toBind_3558_);
lean_dec_ref(v_inst_3557_);
goto v___jp_3566_;
}
}
else
{
lean_dec_ref_known(v___x_3573_, 1);
lean_dec_ref(v_inst_3564_);
lean_dec_ref(v_inst_3563_);
lean_dec_ref(v___f_3562_);
lean_dec_ref(v___f_3561_);
lean_dec(v___f_3560_);
lean_dec_ref(v_inst_3559_);
lean_dec(v_toBind_3558_);
lean_dec_ref(v_inst_3557_);
goto v___jp_3566_;
}
v___jp_3566_:
{
lean_object* v_toPure_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_toPure_3567_ = lean_ctor_get(v_toApplicative_3556_, 1);
lean_inc(v_toPure_3567_);
lean_dec_ref(v_toApplicative_3556_);
v___x_3568_ = lean_box(0);
v___x_3569_ = lean_apply_2(v_toPure_3567_, lean_box(0), v___x_3568_);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__12___boxed(lean_object* v_toApplicative_3583_, lean_object* v_inst_3584_, lean_object* v_toBind_3585_, lean_object* v_inst_3586_, lean_object* v___f_3587_, lean_object* v___f_3588_, lean_object* v___f_3589_, lean_object* v_inst_3590_, lean_object* v_inst_3591_, lean_object* v_____do__lift_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_addTraceAsMessages___redArg___lam__12(v_toApplicative_3583_, v_inst_3584_, v_toBind_3585_, v_inst_3586_, v___f_3587_, v___f_3588_, v___f_3589_, v_inst_3590_, v_inst_3591_, v_____do__lift_3592_);
lean_dec_ref(v_____do__lift_3592_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object* v_inst_3596_, lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_inst_3600_){
_start:
{
lean_object* v_toApplicative_3601_; lean_object* v_toBind_3602_; lean_object* v___f_3603_; lean_object* v___f_3604_; lean_object* v___f_3605_; lean_object* v___f_3606_; lean_object* v___x_3607_; 
v_toApplicative_3601_ = lean_ctor_get(v_inst_3597_, 0);
lean_inc_ref_n(v_toApplicative_3601_, 2);
v_toBind_3602_ = lean_ctor_get(v_inst_3597_, 1);
lean_inc_n(v_toBind_3602_, 2);
v___f_3603_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3603_, 0, v_toApplicative_3601_);
v___f_3604_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__0));
v___f_3605_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__1));
v___f_3606_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__12___boxed), 10, 9);
lean_closure_set(v___f_3606_, 0, v_toApplicative_3601_);
lean_closure_set(v___f_3606_, 1, v_inst_3599_);
lean_closure_set(v___f_3606_, 2, v_toBind_3602_);
lean_closure_set(v___f_3606_, 3, v_inst_3597_);
lean_closure_set(v___f_3606_, 4, v___f_3603_);
lean_closure_set(v___f_3606_, 5, v___f_3604_);
lean_closure_set(v___f_3606_, 6, v___f_3605_);
lean_closure_set(v___f_3606_, 7, v_inst_3598_);
lean_closure_set(v___f_3606_, 8, v_inst_3600_);
v___x_3607_ = lean_apply_4(v_toBind_3602_, lean_box(0), lean_box(0), v_inst_3596_, v___f_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object* v_m_3608_, lean_object* v_inst_3609_, lean_object* v_inst_3610_, lean_object* v_inst_3611_, lean_object* v_inst_3612_, lean_object* v_inst_3613_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l_Lean_addTraceAsMessages___redArg(v_inst_3609_, v_inst_3610_, v_inst_3611_, v_inst_3612_, v_inst_3613_);
return v___x_3614_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3656_ = lean_unsigned_to_nat(2826257906u);
v___x_3657_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3658_ = l_Lean_Name_num___override(v___x_3657_, v___x_3656_);
return v___x_3658_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3660_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3661_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3662_ = l_Lean_Name_str___override(v___x_3661_, v___x_3660_);
return v___x_3662_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3665_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3666_ = l_Lean_Name_str___override(v___x_3665_, v___x_3664_);
return v___x_3666_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3667_ = lean_unsigned_to_nat(2u);
v___x_3668_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3669_ = l_Lean_Name_num___override(v___x_3668_, v___x_3667_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3671_; uint8_t v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3671_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3672_ = 0;
v___x_3673_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3674_ = l_Lean_registerTraceClass(v___x_3671_, v___x_3672_, v___x_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object* v_a_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
return v_res_3676_;
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
