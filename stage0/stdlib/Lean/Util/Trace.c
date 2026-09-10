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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_instHashableRaw_hash___boxed(lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, double, double, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__1(lean_object* v_toPure_318_, lean_object* v_cls_319_, lean_object* v_toBind_320_, lean_object* v_inst_321_, lean_object* v_____do__lift_322_){
_start:
{
lean_object* v___f_323_; lean_object* v___x_324_; 
v___f_323_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_323_, 0, v_toPure_318_);
lean_closure_set(v___f_323_, 1, v_cls_319_);
lean_closure_set(v___f_323_, 2, v_____do__lift_322_);
v___x_324_ = lean_apply_4(v_toBind_320_, lean_box(0), lean_box(0), v_inst_321_, v___f_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_cls_328_){
_start:
{
lean_object* v_toApplicative_329_; lean_object* v_toBind_330_; lean_object* v_getInheritedTraceOptions_331_; lean_object* v_toPure_332_; lean_object* v___f_333_; lean_object* v___x_334_; 
v_toApplicative_329_ = lean_ctor_get(v_inst_325_, 0);
lean_inc_ref(v_toApplicative_329_);
v_toBind_330_ = lean_ctor_get(v_inst_325_, 1);
lean_inc_n(v_toBind_330_, 2);
lean_dec_ref(v_inst_325_);
v_getInheritedTraceOptions_331_ = lean_ctor_get(v_inst_326_, 2);
lean_inc(v_getInheritedTraceOptions_331_);
lean_dec_ref(v_inst_326_);
v_toPure_332_ = lean_ctor_get(v_toApplicative_329_, 1);
lean_inc(v_toPure_332_);
lean_dec_ref(v_toApplicative_329_);
v___f_333_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_333_, 0, v_toPure_332_);
lean_closure_set(v___f_333_, 1, v_cls_328_);
lean_closure_set(v___f_333_, 2, v_toBind_330_);
lean_closure_set(v___f_333_, 3, v_inst_327_);
v___x_334_ = lean_apply_4(v_toBind_330_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_331_, v___f_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor(lean_object* v_m_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_cls_339_){
_start:
{
lean_object* v_toApplicative_340_; lean_object* v_toBind_341_; lean_object* v_getInheritedTraceOptions_342_; lean_object* v_toPure_343_; lean_object* v___f_344_; lean_object* v___x_345_; 
v_toApplicative_340_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toApplicative_340_);
v_toBind_341_ = lean_ctor_get(v_inst_336_, 1);
lean_inc_n(v_toBind_341_, 2);
lean_dec_ref(v_inst_336_);
v_getInheritedTraceOptions_342_ = lean_ctor_get(v_inst_337_, 2);
lean_inc(v_getInheritedTraceOptions_342_);
lean_dec_ref(v_inst_337_);
v_toPure_343_ = lean_ctor_get(v_toApplicative_340_, 1);
lean_inc(v_toPure_343_);
lean_dec_ref(v_toApplicative_340_);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_344_, 0, v_toPure_343_);
lean_closure_set(v___f_344_, 1, v_cls_339_);
lean_closure_set(v___f_344_, 2, v_toBind_341_);
lean_closure_set(v___f_344_, 3, v_inst_338_);
v___x_345_ = lean_apply_4(v_toBind_341_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_342_, v___f_344_);
return v___x_345_;
}
}
LEAN_EXPORT uint8_t lean_is_trace_class_enabled(lean_object* v_opts_346_, lean_object* v_cls_347_){
_start:
{
uint8_t v_hasTrace_349_; 
v_hasTrace_349_ = lean_ctor_get_uint8(v_opts_346_, sizeof(void*)*1);
if (v_hasTrace_349_ == 0)
{
lean_dec(v_cls_347_);
lean_dec_ref(v_opts_346_);
return v_hasTrace_349_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_350_ = l_Lean_inheritedTraceOptions;
v___x_351_ = lean_st_ref_get(v___x_350_);
v___x_352_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_353_ = l_Lean_Name_append(v___x_352_, v_cls_347_);
v___x_354_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_351_, v_opts_346_, v___x_353_);
lean_dec(v___x_353_);
lean_dec_ref(v_opts_346_);
lean_dec(v___x_351_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object* v_opts_355_, lean_object* v_cls_356_, lean_object* v_a_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = lean_is_trace_class_enabled(v_opts_355_, v_cls_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object* v_toPure_360_, lean_object* v_s_361_){
_start:
{
lean_object* v_traces_362_; lean_object* v___x_363_; 
v_traces_362_ = lean_ctor_get(v_s_361_, 0);
lean_inc_ref(v_traces_362_);
lean_dec_ref(v_s_361_);
v___x_363_ = lean_apply_2(v_toPure_360_, lean_box(0), v_traces_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object* v_inst_364_, lean_object* v_inst_365_){
_start:
{
lean_object* v_toApplicative_366_; lean_object* v_toBind_367_; lean_object* v_getTraceState_368_; lean_object* v_toPure_369_; lean_object* v___f_370_; lean_object* v___x_371_; 
v_toApplicative_366_ = lean_ctor_get(v_inst_364_, 0);
lean_inc_ref(v_toApplicative_366_);
v_toBind_367_ = lean_ctor_get(v_inst_364_, 1);
lean_inc(v_toBind_367_);
lean_dec_ref(v_inst_364_);
v_getTraceState_368_ = lean_ctor_get(v_inst_365_, 1);
lean_inc(v_getTraceState_368_);
lean_dec_ref(v_inst_365_);
v_toPure_369_ = lean_ctor_get(v_toApplicative_366_, 1);
lean_inc(v_toPure_369_);
lean_dec_ref(v_toApplicative_366_);
v___f_370_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_370_, 0, v_toPure_369_);
v___x_371_ = lean_apply_4(v_toBind_367_, lean_box(0), lean_box(0), v_getTraceState_368_, v___f_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object* v_m_372_, lean_object* v_inst_373_, lean_object* v_inst_374_){
_start:
{
lean_object* v_toApplicative_375_; lean_object* v_toBind_376_; lean_object* v_getTraceState_377_; lean_object* v_toPure_378_; lean_object* v___f_379_; lean_object* v___x_380_; 
v_toApplicative_375_ = lean_ctor_get(v_inst_373_, 0);
lean_inc_ref(v_toApplicative_375_);
v_toBind_376_ = lean_ctor_get(v_inst_373_, 1);
lean_inc(v_toBind_376_);
lean_dec_ref(v_inst_373_);
v_getTraceState_377_ = lean_ctor_get(v_inst_374_, 1);
lean_inc(v_getTraceState_377_);
lean_dec_ref(v_inst_374_);
v_toPure_378_ = lean_ctor_get(v_toApplicative_375_, 1);
lean_inc(v_toPure_378_);
lean_dec_ref(v_toApplicative_375_);
v___f_379_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_379_, 0, v_toPure_378_);
v___x_380_ = lean_apply_4(v_toBind_376_, lean_box(0), lean_box(0), v_getTraceState_377_, v___f_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object* v_f_381_, lean_object* v_s_382_){
_start:
{
uint64_t v_tid_383_; lean_object* v_traces_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_392_; 
v_tid_383_ = lean_ctor_get_uint64(v_s_382_, sizeof(void*)*1);
v_traces_384_ = lean_ctor_get(v_s_382_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v_s_382_);
if (v_isSharedCheck_392_ == 0)
{
v___x_386_ = v_s_382_;
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_traces_384_);
lean_dec(v_s_382_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_apply_1(v_f_381_, v_traces_384_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v___x_388_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
lean_ctor_set_uint64(v_reuseFailAlloc_391_, sizeof(void*)*1, v_tid_383_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object* v_inst_393_, lean_object* v_f_394_){
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
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object* v_m_398_, lean_object* v_inst_399_, lean_object* v_f_400_){
_start:
{
lean_object* v_modifyTraceState_401_; lean_object* v___f_402_; lean_object* v___x_403_; 
v_modifyTraceState_401_ = lean_ctor_get(v_inst_399_, 0);
lean_inc(v_modifyTraceState_401_);
lean_dec_ref(v_inst_399_);
v___f_402_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_402_, 0, v_f_400_);
v___x_403_ = lean_apply_1(v_modifyTraceState_401_, v___f_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object* v_s_404_, lean_object* v_x_405_){
_start:
{
lean_inc_ref(v_s_404_);
return v_s_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object* v_s_406_, lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_setTraceState___redArg___lam__0(v_s_406_, v_x_407_);
lean_dec_ref(v_x_407_);
lean_dec_ref(v_s_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object* v_inst_409_, lean_object* v_s_410_){
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
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object* v_m_414_, lean_object* v_inst_415_, lean_object* v_s_416_){
_start:
{
lean_object* v_modifyTraceState_417_; lean_object* v___f_418_; lean_object* v___x_419_; 
v_modifyTraceState_417_ = lean_ctor_get(v_inst_415_, 0);
lean_inc(v_modifyTraceState_417_);
lean_dec_ref(v_inst_415_);
v___f_418_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_418_, 0, v_s_416_);
v___x_419_ = lean_apply_1(v_modifyTraceState_417_, v___f_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object* v_s_420_){
_start:
{
uint64_t v_tid_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_431_; 
v_tid_421_ = lean_ctor_get_uint64(v_s_420_, sizeof(void*)*1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_s_420_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v_s_420_, 0);
lean_dec(v_unused_432_);
v___x_423_ = v_s_420_;
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
else
{
lean_dec(v_s_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_425_ = lean_unsigned_to_nat(32u);
v___x_426_ = lean_mk_empty_array_with_capacity(v___x_425_);
lean_dec_ref(v___x_426_);
v___x_427_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__1, &l_Lean_instInhabitedTraceState_default___closed__1_once, _init_l_Lean_instInhabitedTraceState_default___closed__1);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_427_);
v___x_429_ = v___x_423_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
lean_ctor_set_uint64(v_reuseFailAlloc_430_, sizeof(void*)*1, v_tid_421_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object* v_toPure_433_, lean_object* v_oldTraces_434_, lean_object* v_____r_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_apply_2(v_toPure_433_, lean_box(0), v_oldTraces_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object* v_toPure_437_, lean_object* v_modifyTraceState_438_, lean_object* v___f_439_, lean_object* v_toBind_440_, lean_object* v_oldTraces_441_){
_start:
{
lean_object* v___f_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___f_442_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_442_, 0, v_toPure_437_);
lean_closure_set(v___f_442_, 1, v_oldTraces_441_);
v___x_443_ = lean_apply_1(v_modifyTraceState_438_, v___f_439_);
v___x_444_ = lean_apply_4(v_toBind_440_, lean_box(0), lean_box(0), v___x_443_, v___f_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object* v_inst_446_, lean_object* v_inst_447_){
_start:
{
lean_object* v_toApplicative_448_; lean_object* v_toBind_449_; lean_object* v_modifyTraceState_450_; lean_object* v_getTraceState_451_; lean_object* v_toPure_452_; lean_object* v___f_453_; lean_object* v___f_454_; lean_object* v___f_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_toApplicative_448_ = lean_ctor_get(v_inst_446_, 0);
lean_inc_ref(v_toApplicative_448_);
v_toBind_449_ = lean_ctor_get(v_inst_446_, 1);
lean_inc_n(v_toBind_449_, 3);
lean_dec_ref(v_inst_446_);
v_modifyTraceState_450_ = lean_ctor_get(v_inst_447_, 0);
lean_inc(v_modifyTraceState_450_);
v_getTraceState_451_ = lean_ctor_get(v_inst_447_, 1);
lean_inc(v_getTraceState_451_);
lean_dec_ref(v_inst_447_);
v_toPure_452_ = lean_ctor_get(v_toApplicative_448_, 1);
lean_inc_n(v_toPure_452_, 2);
lean_dec_ref(v_toApplicative_448_);
v___f_453_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0));
v___f_454_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_454_, 0, v_toPure_452_);
lean_closure_set(v___f_454_, 1, v_modifyTraceState_450_);
lean_closure_set(v___f_454_, 2, v___f_453_);
lean_closure_set(v___f_454_, 3, v_toBind_449_);
v___f_455_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_455_, 0, v_toPure_452_);
v___x_456_ = lean_apply_4(v_toBind_449_, lean_box(0), lean_box(0), v_getTraceState_451_, v___f_455_);
v___x_457_ = lean_apply_4(v_toBind_449_, lean_box(0), lean_box(0), v___x_456_, v___f_454_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object* v_m_458_, lean_object* v_inst_459_, lean_object* v_inst_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_459_, v_inst_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object* v_ref_462_, lean_object* v_msg_463_, lean_object* v_s_464_){
_start:
{
uint64_t v_tid_465_; lean_object* v_traces_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_475_; 
v_tid_465_ = lean_ctor_get_uint64(v_s_464_, sizeof(void*)*1);
v_traces_466_ = lean_ctor_get(v_s_464_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_s_464_);
if (v_isSharedCheck_475_ == 0)
{
v___x_468_ = v_s_464_;
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_traces_466_);
lean_dec(v_s_464_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v_ref_462_);
lean_ctor_set(v___x_470_, 1, v_msg_463_);
v___x_471_ = l_Lean_PersistentArray_push___redArg(v_traces_466_, v___x_470_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
lean_ctor_set_uint64(v_reuseFailAlloc_474_, sizeof(void*)*1, v_tid_465_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object* v_inst_476_, lean_object* v_ref_477_, lean_object* v_msg_478_){
_start:
{
lean_object* v_modifyTraceState_479_; lean_object* v___f_480_; lean_object* v___x_481_; 
v_modifyTraceState_479_ = lean_ctor_get(v_inst_476_, 0);
lean_inc(v_modifyTraceState_479_);
lean_dec_ref(v_inst_476_);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__0), 3, 2);
lean_closure_set(v___f_480_, 0, v_ref_477_);
lean_closure_set(v___f_480_, 1, v_msg_478_);
v___x_481_ = lean_apply_1(v_modifyTraceState_479_, v___f_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_msg_484_, lean_object* v_toBind_485_, lean_object* v_ref_486_){
_start:
{
lean_object* v___f_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___f_487_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__1), 3, 2);
lean_closure_set(v___f_487_, 0, v_inst_482_);
lean_closure_set(v___f_487_, 1, v_ref_486_);
v___x_488_ = lean_apply_1(v_inst_483_, v_msg_484_);
v___x_489_ = lean_apply_4(v_toBind_485_, lean_box(0), lean_box(0), v___x_488_, v___f_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_msg_494_){
_start:
{
lean_object* v_toBind_495_; lean_object* v_getRef_496_; lean_object* v___f_497_; lean_object* v___x_498_; 
v_toBind_495_ = lean_ctor_get(v_inst_490_, 1);
lean_inc_n(v_toBind_495_, 2);
lean_dec_ref(v_inst_490_);
v_getRef_496_ = lean_ctor_get(v_inst_492_, 0);
lean_inc(v_getRef_496_);
lean_dec_ref(v_inst_492_);
v___f_497_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__2), 5, 4);
lean_closure_set(v___f_497_, 0, v_inst_491_);
lean_closure_set(v___f_497_, 1, v_inst_493_);
lean_closure_set(v___f_497_, 2, v_msg_494_);
lean_closure_set(v___f_497_, 3, v_toBind_495_);
v___x_498_ = lean_apply_4(v_toBind_495_, lean_box(0), lean_box(0), v_getRef_496_, v___f_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object* v_m_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_msg_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_addRawTrace___redArg(v_inst_500_, v_inst_501_, v_inst_502_, v_inst_503_, v_msg_504_);
return v___x_505_;
}
}
static double _init_l_Lean_addTrace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_506_; double v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_float_of_nat(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object* v_cls_511_, lean_object* v_msg_512_, lean_object* v_ref_513_, lean_object* v_s_514_){
_start:
{
uint64_t v_tid_515_; lean_object* v_traces_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_532_; 
v_tid_515_ = lean_ctor_get_uint64(v_s_514_, sizeof(void*)*1);
v_traces_516_ = lean_ctor_get(v_s_514_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_s_514_);
if (v_isSharedCheck_532_ == 0)
{
v___x_518_ = v_s_514_;
v_isShared_519_ = v_isSharedCheck_532_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_traces_516_);
lean_dec(v_s_514_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_532_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; double v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_520_ = lean_box(0);
v___x_521_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
v___x_522_ = 0;
v___x_523_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_524_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_524_, 0, v_cls_511_);
lean_ctor_set(v___x_524_, 1, v___x_520_);
lean_ctor_set(v___x_524_, 2, v___x_523_);
lean_ctor_set_float(v___x_524_, sizeof(void*)*3, v___x_521_);
lean_ctor_set_float(v___x_524_, sizeof(void*)*3 + 8, v___x_521_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*3 + 16, v___x_522_);
v___x_525_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
v___x_526_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v_msg_512_);
lean_ctor_set(v___x_526_, 2, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_ref_513_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_PersistentArray_push___redArg(v_traces_516_, v___x_527_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_528_);
v___x_530_ = v___x_518_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
lean_ctor_set_uint64(v_reuseFailAlloc_531_, sizeof(void*)*1, v_tid_515_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object* v_inst_533_, lean_object* v_cls_534_, lean_object* v_ref_535_, lean_object* v_msg_536_){
_start:
{
lean_object* v_modifyTraceState_537_; lean_object* v___f_538_; lean_object* v___x_539_; 
v_modifyTraceState_537_ = lean_ctor_get(v_inst_533_, 0);
lean_inc(v_modifyTraceState_537_);
lean_dec_ref(v_inst_533_);
v___f_538_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_538_, 0, v_cls_534_);
lean_closure_set(v___f_538_, 1, v_msg_536_);
lean_closure_set(v___f_538_, 2, v_ref_535_);
v___x_539_ = lean_apply_1(v_modifyTraceState_537_, v___f_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object* v_inst_540_, lean_object* v_cls_541_, lean_object* v_inst_542_, lean_object* v_msg_543_, lean_object* v_toBind_544_, lean_object* v_ref_545_){
_start:
{
lean_object* v___f_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___f_546_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__1), 4, 3);
lean_closure_set(v___f_546_, 0, v_inst_540_);
lean_closure_set(v___f_546_, 1, v_cls_541_);
lean_closure_set(v___f_546_, 2, v_ref_545_);
v___x_547_ = lean_apply_1(v_inst_542_, v_msg_543_);
v___x_548_ = lean_apply_4(v_toBind_544_, lean_box(0), lean_box(0), v___x_547_, v___f_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_cls_553_, lean_object* v_msg_554_){
_start:
{
lean_object* v_toBind_555_; lean_object* v_getRef_556_; lean_object* v___f_557_; lean_object* v___x_558_; 
v_toBind_555_ = lean_ctor_get(v_inst_549_, 1);
lean_inc_n(v_toBind_555_, 2);
lean_dec_ref(v_inst_549_);
v_getRef_556_ = lean_ctor_get(v_inst_551_, 0);
lean_inc(v_getRef_556_);
lean_dec_ref(v_inst_551_);
v___f_557_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__2), 6, 5);
lean_closure_set(v___f_557_, 0, v_inst_550_);
lean_closure_set(v___f_557_, 1, v_cls_553_);
lean_closure_set(v___f_557_, 2, v_inst_552_);
lean_closure_set(v___f_557_, 3, v_msg_554_);
lean_closure_set(v___f_557_, 4, v_toBind_555_);
v___x_558_ = lean_apply_4(v_toBind_555_, lean_box(0), lean_box(0), v_getRef_556_, v___f_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object* v_m_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_cls_564_, lean_object* v_msg_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_addTrace___redArg(v_inst_560_, v_inst_561_, v_inst_562_, v_inst_563_, v_cls_564_, v_msg_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0(lean_object* v_toPure_567_, lean_object* v_msg_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_cls_573_, uint8_t v_____do__lift_574_){
_start:
{
if (v_____do__lift_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec(v_cls_573_);
lean_dec(v_inst_572_);
lean_dec_ref(v_inst_571_);
lean_dec_ref(v_inst_570_);
lean_dec_ref(v_inst_569_);
lean_dec_ref(v_msg_568_);
v___x_575_ = lean_box(0);
v___x_576_ = lean_apply_2(v_toPure_567_, lean_box(0), v___x_575_);
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_toPure_567_);
v___x_577_ = lean_box(0);
v___x_578_ = lean_apply_1(v_msg_568_, v___x_577_);
v___x_579_ = l_Lean_addTrace___redArg(v_inst_569_, v_inst_570_, v_inst_571_, v_inst_572_, v_cls_573_, v___x_578_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object* v_toPure_580_, lean_object* v_msg_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_cls_586_, lean_object* v_____do__lift_587_){
_start:
{
uint8_t v_____do__lift_125__boxed_588_; lean_object* v_res_589_; 
v_____do__lift_125__boxed_588_ = lean_unbox(v_____do__lift_587_);
v_res_589_ = l_Lean_trace___redArg___lam__0(v_toPure_580_, v_msg_581_, v_inst_582_, v_inst_583_, v_inst_584_, v_inst_585_, v_cls_586_, v_____do__lift_125__boxed_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_cls_595_, lean_object* v_msg_596_){
_start:
{
lean_object* v_toApplicative_597_; lean_object* v_toBind_598_; lean_object* v_getInheritedTraceOptions_599_; lean_object* v_toPure_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_toApplicative_597_ = lean_ctor_get(v_inst_590_, 0);
v_toBind_598_ = lean_ctor_get(v_inst_590_, 1);
lean_inc_n(v_toBind_598_, 3);
v_getInheritedTraceOptions_599_ = lean_ctor_get(v_inst_591_, 2);
lean_inc(v_getInheritedTraceOptions_599_);
v_toPure_600_ = lean_ctor_get(v_toApplicative_597_, 1);
lean_inc_n(v_toPure_600_, 2);
lean_inc(v_cls_595_);
v___f_601_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_601_, 0, v_toPure_600_);
lean_closure_set(v___f_601_, 1, v_msg_596_);
lean_closure_set(v___f_601_, 2, v_inst_590_);
lean_closure_set(v___f_601_, 3, v_inst_591_);
lean_closure_set(v___f_601_, 4, v_inst_592_);
lean_closure_set(v___f_601_, 5, v_inst_593_);
lean_closure_set(v___f_601_, 6, v_cls_595_);
v___f_602_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_602_, 0, v_toPure_600_);
lean_closure_set(v___f_602_, 1, v_cls_595_);
lean_closure_set(v___f_602_, 2, v_toBind_598_);
lean_closure_set(v___f_602_, 3, v_inst_594_);
v___x_603_ = lean_apply_4(v_toBind_598_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_599_, v___f_602_);
v___x_604_ = lean_apply_4(v_toBind_598_, lean_box(0), lean_box(0), v___x_603_, v___f_601_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace(lean_object* v_m_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_cls_611_, lean_object* v_msg_612_){
_start:
{
lean_object* v_toApplicative_613_; lean_object* v_toBind_614_; lean_object* v_getInheritedTraceOptions_615_; lean_object* v_toPure_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_toApplicative_613_ = lean_ctor_get(v_inst_606_, 0);
v_toBind_614_ = lean_ctor_get(v_inst_606_, 1);
lean_inc_n(v_toBind_614_, 3);
v_getInheritedTraceOptions_615_ = lean_ctor_get(v_inst_607_, 2);
lean_inc(v_getInheritedTraceOptions_615_);
v_toPure_616_ = lean_ctor_get(v_toApplicative_613_, 1);
lean_inc_n(v_toPure_616_, 2);
lean_inc(v_cls_611_);
v___f_617_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_617_, 0, v_toPure_616_);
lean_closure_set(v___f_617_, 1, v_msg_612_);
lean_closure_set(v___f_617_, 2, v_inst_606_);
lean_closure_set(v___f_617_, 3, v_inst_607_);
lean_closure_set(v___f_617_, 4, v_inst_608_);
lean_closure_set(v___f_617_, 5, v_inst_609_);
lean_closure_set(v___f_617_, 6, v_cls_611_);
v___f_618_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_618_, 0, v_toPure_616_);
lean_closure_set(v___f_618_, 1, v_cls_611_);
lean_closure_set(v___f_618_, 2, v_toBind_614_);
lean_closure_set(v___f_618_, 3, v_inst_610_);
v___x_619_ = lean_apply_4(v_toBind_614_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_615_, v___f_618_);
v___x_620_ = lean_apply_4(v_toBind_614_, lean_box(0), lean_box(0), v___x_619_, v___f_617_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_cls_625_, lean_object* v_msg_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_addTrace___redArg(v_inst_621_, v_inst_622_, v_inst_623_, v_inst_624_, v_cls_625_, v_msg_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1(lean_object* v_toPure_628_, lean_object* v_toBind_629_, lean_object* v_mkMsg_630_, lean_object* v___f_631_, uint8_t v_____do__lift_632_){
_start:
{
if (v_____do__lift_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v___f_631_);
lean_dec(v_mkMsg_630_);
lean_dec(v_toBind_629_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_apply_2(v_toPure_628_, lean_box(0), v___x_633_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; 
lean_dec(v_toPure_628_);
v___x_635_ = lean_apply_4(v_toBind_629_, lean_box(0), lean_box(0), v_mkMsg_630_, v___f_631_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object* v_toPure_636_, lean_object* v_toBind_637_, lean_object* v_mkMsg_638_, lean_object* v___f_639_, lean_object* v_____do__lift_640_){
_start:
{
uint8_t v_____do__lift_131__boxed_641_; lean_object* v_res_642_; 
v_____do__lift_131__boxed_641_ = lean_unbox(v_____do__lift_640_);
v_res_642_ = l_Lean_traceM___redArg___lam__1(v_toPure_636_, v_toBind_637_, v_mkMsg_638_, v___f_639_, v_____do__lift_131__boxed_641_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_cls_648_, lean_object* v_mkMsg_649_){
_start:
{
lean_object* v_toApplicative_650_; lean_object* v_toBind_651_; lean_object* v_getInheritedTraceOptions_652_; lean_object* v_toPure_653_; lean_object* v___f_654_; lean_object* v___f_655_; lean_object* v___f_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_toApplicative_650_ = lean_ctor_get(v_inst_643_, 0);
v_toBind_651_ = lean_ctor_get(v_inst_643_, 1);
lean_inc_n(v_toBind_651_, 4);
v_getInheritedTraceOptions_652_ = lean_ctor_get(v_inst_644_, 2);
lean_inc(v_getInheritedTraceOptions_652_);
v_toPure_653_ = lean_ctor_get(v_toApplicative_650_, 1);
lean_inc_n(v_toPure_653_, 2);
lean_inc(v_cls_648_);
v___f_654_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_654_, 0, v_inst_643_);
lean_closure_set(v___f_654_, 1, v_inst_644_);
lean_closure_set(v___f_654_, 2, v_inst_645_);
lean_closure_set(v___f_654_, 3, v_inst_646_);
lean_closure_set(v___f_654_, 4, v_cls_648_);
v___f_655_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_655_, 0, v_toPure_653_);
lean_closure_set(v___f_655_, 1, v_toBind_651_);
lean_closure_set(v___f_655_, 2, v_mkMsg_649_);
lean_closure_set(v___f_655_, 3, v___f_654_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_656_, 0, v_toPure_653_);
lean_closure_set(v___f_656_, 1, v_cls_648_);
lean_closure_set(v___f_656_, 2, v_toBind_651_);
lean_closure_set(v___f_656_, 3, v_inst_647_);
v___x_657_ = lean_apply_4(v_toBind_651_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_652_, v___f_656_);
v___x_658_ = lean_apply_4(v_toBind_651_, lean_box(0), lean_box(0), v___x_657_, v___f_655_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object* v_m_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_cls_665_, lean_object* v_mkMsg_666_){
_start:
{
lean_object* v_toApplicative_667_; lean_object* v_toBind_668_; lean_object* v_getInheritedTraceOptions_669_; lean_object* v_toPure_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_toApplicative_667_ = lean_ctor_get(v_inst_660_, 0);
v_toBind_668_ = lean_ctor_get(v_inst_660_, 1);
lean_inc_n(v_toBind_668_, 4);
v_getInheritedTraceOptions_669_ = lean_ctor_get(v_inst_661_, 2);
lean_inc(v_getInheritedTraceOptions_669_);
v_toPure_670_ = lean_ctor_get(v_toApplicative_667_, 1);
lean_inc_n(v_toPure_670_, 2);
lean_inc(v_cls_665_);
v___f_671_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_671_, 0, v_inst_660_);
lean_closure_set(v___f_671_, 1, v_inst_661_);
lean_closure_set(v___f_671_, 2, v_inst_662_);
lean_closure_set(v___f_671_, 3, v_inst_663_);
lean_closure_set(v___f_671_, 4, v_cls_665_);
v___f_672_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_672_, 0, v_toPure_670_);
lean_closure_set(v___f_672_, 1, v_toBind_668_);
lean_closure_set(v___f_672_, 2, v_mkMsg_666_);
lean_closure_set(v___f_672_, 3, v___f_671_);
v___f_673_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_673_, 0, v_toPure_670_);
lean_closure_set(v___f_673_, 1, v_cls_665_);
lean_closure_set(v___f_673_, 2, v_toBind_668_);
lean_closure_set(v___f_673_, 3, v_inst_664_);
v___x_674_ = lean_apply_4(v_toBind_668_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_669_, v___f_673_);
v___x_675_ = lean_apply_4(v_toBind_668_, lean_box(0), lean_box(0), v___x_674_, v___f_672_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object* v_x_676_){
_start:
{
lean_object* v_msg_677_; 
v_msg_677_ = lean_ctor_get(v_x_676_, 1);
lean_inc_ref(v_msg_677_);
return v_msg_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object* v_x_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_678_);
lean_dec_ref(v_x_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object* v_ref_680_, lean_object* v_msg_681_, lean_object* v_oldTraces_682_, lean_object* v_s_683_){
_start:
{
uint64_t v_tid_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_693_; 
v_tid_684_ = lean_ctor_get_uint64(v_s_683_, sizeof(void*)*1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_s_683_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v_s_683_, 0);
lean_dec(v_unused_694_);
v___x_686_ = v_s_683_;
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
else
{
lean_dec(v_s_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_ref_680_);
lean_ctor_set(v___x_688_, 1, v_msg_681_);
v___x_689_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_682_, v___x_688_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_689_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
lean_ctor_set_uint64(v_reuseFailAlloc_692_, sizeof(void*)*1, v_tid_684_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object* v_ref_695_, lean_object* v_oldTraces_696_, lean_object* v_modifyTraceState_697_, lean_object* v_msg_698_){
_start:
{
lean_object* v___f_699_; lean_object* v___x_700_; 
v___f_699_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0), 4, 3);
lean_closure_set(v___f_699_, 0, v_ref_695_);
lean_closure_set(v___f_699_, 1, v_msg_698_);
lean_closure_set(v___f_699_, 2, v_oldTraces_696_);
v___x_700_ = lean_apply_1(v_modifyTraceState_697_, v___f_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object* v___f_720_, lean_object* v_data_721_, lean_object* v_msg_722_, lean_object* v_inst_723_, lean_object* v_toBind_724_, lean_object* v___f_725_, lean_object* v_____do__lift_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; size_t v_sz_729_; size_t v___x_730_; lean_object* v___x_731_; lean_object* v_msg_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_727_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_726_);
v___x_728_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v_sz_729_ = lean_array_size(v___x_727_);
v___x_730_ = ((size_t)0ULL);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_728_, v___f_720_, v_sz_729_, v___x_730_, v___x_727_);
v_msg_732_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_732_, 0, v_data_721_);
lean_ctor_set(v_msg_732_, 1, v_msg_722_);
lean_ctor_set(v_msg_732_, 2, v___x_731_);
v___x_733_ = lean_apply_1(v_inst_723_, v_msg_732_);
v___x_734_ = lean_apply_4(v_toBind_724_, lean_box(0), lean_box(0), v___x_733_, v___f_725_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object* v___f_735_, lean_object* v_data_736_, lean_object* v_msg_737_, lean_object* v_inst_738_, lean_object* v_toBind_739_, lean_object* v___f_740_, lean_object* v_____do__lift_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(v___f_735_, v_data_736_, v_msg_737_, v_inst_738_, v_toBind_739_, v___f_740_, v_____do__lift_741_);
lean_dec_ref(v_____do__lift_741_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object* v_ref_743_, lean_object* v_withRef_744_, lean_object* v___x_745_, lean_object* v_oldRef_746_){
_start:
{
lean_object* v_ref_747_; lean_object* v___x_748_; 
v_ref_747_ = l_Lean_replaceRef(v_ref_743_, v_oldRef_746_);
v___x_748_ = lean_apply_3(v_withRef_744_, lean_box(0), v_ref_747_, v___x_745_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object* v_ref_749_, lean_object* v_withRef_750_, lean_object* v___x_751_, lean_object* v_oldRef_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(v_ref_749_, v_withRef_750_, v___x_751_, v_oldRef_752_);
lean_dec(v_oldRef_752_);
lean_dec(v_ref_749_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_oldTraces_759_, lean_object* v_data_760_, lean_object* v_ref_761_, lean_object* v_msg_762_){
_start:
{
lean_object* v_toApplicative_763_; lean_object* v_toBind_764_; lean_object* v_modifyTraceState_765_; lean_object* v_getTraceState_766_; lean_object* v_toPure_767_; lean_object* v_getRef_768_; lean_object* v_withRef_769_; lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___x_777_; 
v_toApplicative_763_ = lean_ctor_get(v_inst_755_, 0);
lean_inc_ref(v_toApplicative_763_);
v_toBind_764_ = lean_ctor_get(v_inst_755_, 1);
lean_inc_n(v_toBind_764_, 4);
lean_dec_ref(v_inst_755_);
v_modifyTraceState_765_ = lean_ctor_get(v_inst_756_, 0);
lean_inc(v_modifyTraceState_765_);
v_getTraceState_766_ = lean_ctor_get(v_inst_756_, 1);
lean_inc(v_getTraceState_766_);
lean_dec_ref(v_inst_756_);
v_toPure_767_ = lean_ctor_get(v_toApplicative_763_, 1);
lean_inc(v_toPure_767_);
lean_dec_ref(v_toApplicative_763_);
v_getRef_768_ = lean_ctor_get(v_inst_757_, 0);
lean_inc(v_getRef_768_);
v_withRef_769_ = lean_ctor_get(v_inst_757_, 1);
lean_inc(v_withRef_769_);
lean_dec_ref(v_inst_757_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_770_, 0, v_toPure_767_);
v___x_771_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v_getTraceState_766_, v___f_770_);
v___f_772_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0));
lean_inc(v_ref_761_);
v___f_773_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2), 4, 3);
lean_closure_set(v___f_773_, 0, v_ref_761_);
lean_closure_set(v___f_773_, 1, v_oldTraces_759_);
lean_closure_set(v___f_773_, 2, v_modifyTraceState_765_);
v___f_774_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_774_, 0, v___f_772_);
lean_closure_set(v___f_774_, 1, v_data_760_);
lean_closure_set(v___f_774_, 2, v_msg_762_);
lean_closure_set(v___f_774_, 3, v_inst_758_);
lean_closure_set(v___f_774_, 4, v_toBind_764_);
lean_closure_set(v___f_774_, 5, v___f_773_);
v___x_775_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_771_, v___f_774_);
v___f_776_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_776_, 0, v_ref_761_);
lean_closure_set(v___f_776_, 1, v_withRef_769_);
lean_closure_set(v___f_776_, 2, v___x_775_);
v___x_777_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v_getRef_768_, v___f_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object* v_m_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_oldTraces_783_, lean_object* v_data_784_, lean_object* v_ref_785_, lean_object* v_msg_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_779_, v_inst_780_, v_inst_781_, v_inst_782_, v_oldTraces_783_, v_data_784_, v_ref_785_, v_msg_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object* v_name_788_, lean_object* v_decl_789_, lean_object* v_ref_790_){
_start:
{
lean_object* v_defValue_792_; lean_object* v_descr_793_; lean_object* v_deprecation_x3f_794_; lean_object* v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_defValue_792_ = lean_ctor_get(v_decl_789_, 0);
v_descr_793_ = lean_ctor_get(v_decl_789_, 1);
v_deprecation_x3f_794_ = lean_ctor_get(v_decl_789_, 2);
v___x_795_ = lean_alloc_ctor(1, 0, 1);
v___x_796_ = lean_unbox(v_defValue_792_);
lean_ctor_set_uint8(v___x_795_, 0, v___x_796_);
lean_inc(v_deprecation_x3f_794_);
lean_inc_ref(v_descr_793_);
lean_inc_n(v_name_788_, 2);
v___x_797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_797_, 0, v_name_788_);
lean_ctor_set(v___x_797_, 1, v_ref_790_);
lean_ctor_set(v___x_797_, 2, v___x_795_);
lean_ctor_set(v___x_797_, 3, v_descr_793_);
lean_ctor_set(v___x_797_, 4, v_deprecation_x3f_794_);
v___x_798_ = lean_register_option(v_name_788_, v___x_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v___x_798_, 0);
lean_dec(v_unused_807_);
v___x_800_ = v___x_798_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_dec(v___x_798_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_inc(v_defValue_792_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_name_788_);
lean_ctor_set(v___x_802_, 1, v_defValue_792_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_name_788_);
v_a_808_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_798_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_798_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_816_, lean_object* v_decl_817_, lean_object* v_ref_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_816_, v_decl_817_, v_ref_818_);
lean_dec_ref(v_decl_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_836_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_837_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_838_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_839_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_836_, v___x_837_, v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object* v_name_842_, lean_object* v_decl_843_, lean_object* v_ref_844_){
_start:
{
lean_object* v_defValue_846_; lean_object* v_descr_847_; lean_object* v_deprecation_x3f_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_defValue_846_ = lean_ctor_get(v_decl_843_, 0);
v_descr_847_ = lean_ctor_get(v_decl_843_, 1);
v_deprecation_x3f_848_ = lean_ctor_get(v_decl_843_, 2);
lean_inc(v_defValue_846_);
v___x_849_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_849_, 0, v_defValue_846_);
lean_inc(v_deprecation_x3f_848_);
lean_inc_ref(v_descr_847_);
lean_inc_n(v_name_842_, 2);
v___x_850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_850_, 0, v_name_842_);
lean_ctor_set(v___x_850_, 1, v_ref_844_);
lean_ctor_set(v___x_850_, 2, v___x_849_);
lean_ctor_set(v___x_850_, 3, v_descr_847_);
lean_ctor_set(v___x_850_, 4, v_deprecation_x3f_848_);
v___x_851_ = lean_register_option(v_name_842_, v___x_850_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; 
v_unused_860_ = lean_ctor_get(v___x_851_, 0);
lean_dec(v_unused_860_);
v___x_853_ = v___x_851_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_dec(v___x_851_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
lean_inc(v_defValue_846_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v_name_842_);
lean_ctor_set(v___x_855_, 1, v_defValue_846_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_name_842_);
v_a_861_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_851_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_851_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_869_, lean_object* v_decl_870_, lean_object* v_ref_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_869_, v_decl_870_, v_ref_871_);
lean_dec_ref(v_decl_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_890_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_891_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_892_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_893_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_890_, v___x_891_, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_913_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_914_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_915_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_916_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_913_, v___x_914_, v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object* v_name_919_, lean_object* v_decl_920_, lean_object* v_ref_921_){
_start:
{
lean_object* v_defValue_923_; lean_object* v_descr_924_; lean_object* v_deprecation_x3f_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_defValue_923_ = lean_ctor_get(v_decl_920_, 0);
v_descr_924_ = lean_ctor_get(v_decl_920_, 1);
v_deprecation_x3f_925_ = lean_ctor_get(v_decl_920_, 2);
lean_inc(v_defValue_923_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v_defValue_923_);
lean_inc(v_deprecation_x3f_925_);
lean_inc_ref(v_descr_924_);
lean_inc_n(v_name_919_, 2);
v___x_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_927_, 0, v_name_919_);
lean_ctor_set(v___x_927_, 1, v_ref_921_);
lean_ctor_set(v___x_927_, 2, v___x_926_);
lean_ctor_set(v___x_927_, 3, v_descr_924_);
lean_ctor_set(v___x_927_, 4, v_deprecation_x3f_925_);
v___x_928_ = lean_register_option(v_name_919_, v___x_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_936_; 
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v___x_928_, 0);
lean_dec(v_unused_937_);
v___x_930_ = v___x_928_;
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
else
{
lean_dec(v___x_928_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
lean_inc(v_defValue_923_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_name_919_);
lean_ctor_set(v___x_932_, 1, v_defValue_923_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_932_);
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_name_919_);
v_a_938_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_928_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_928_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_946_, lean_object* v_decl_947_, lean_object* v_ref_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_946_, v_decl_947_, v_ref_948_);
lean_dec_ref(v_decl_947_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_967_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_968_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_969_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_970_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_967_, v___x_968_, v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_990_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_991_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_992_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_993_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_990_, v___x_991_, v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4____boxed(lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
return v_res_995_;
}
}
LEAN_EXPORT uint8_t l_Lean_trace_profiler_isExporting(lean_object* v_opts_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_997_ = l_Lean_KVMap_instValueBool;
v___x_998_ = l_Lean_KVMap_instValueString;
v___x_999_ = l_Lean_trace_profiler_output;
v___x_1000_ = l_Lean_Option_get_x3f___redArg(v___x_998_, v_opts_996_, v___x_999_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1001_ = l_Lean_trace_profiler_serve;
v___x_1002_ = l_Lean_Option_get___redArg(v___x_997_, v_opts_996_, v___x_1001_);
v___x_1003_ = lean_unbox(v___x_1002_);
lean_dec(v___x_1002_);
return v___x_1003_;
}
else
{
uint8_t v___x_1004_; 
lean_dec_ref_known(v___x_1000_, 1);
v___x_1004_ = 1;
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_isExporting___boxed(lean_object* v_opts_1005_){
_start:
{
uint8_t v_res_1006_; lean_object* v_r_1007_; 
v_res_1006_ = l_Lean_trace_profiler_isExporting(v_opts_1005_);
lean_dec_ref(v_opts_1005_);
v_r_1007_ = lean_box(v_res_1006_);
return v_r_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1028_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1029_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1030_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_1027_, v___x_1028_, v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
return v_res_1032_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1033_; double v___x_1034_; 
v___x_1033_ = lean_unsigned_to_nat(1000000000u);
v___x_1034_ = lean_float_of_nat(v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object* v_start_1035_, lean_object* v_a_1036_, lean_object* v_toPure_1037_, lean_object* v_stop_1038_){
_start:
{
double v___x_1039_; double v___x_1040_; double v___x_1041_; double v___x_1042_; double v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1039_ = lean_float_of_nat(v_start_1035_);
v___x_1040_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1041_ = lean_float_div(v___x_1039_, v___x_1040_);
v___x_1042_ = lean_float_of_nat(v_stop_1038_);
v___x_1043_ = lean_float_div(v___x_1042_, v___x_1040_);
v___x_1044_ = lean_box_float(v___x_1041_);
v___x_1045_ = lean_box_float(v___x_1043_);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_a_1036_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_apply_2(v_toPure_1037_, lean_box(0), v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object* v_start_1049_, lean_object* v_toPure_1050_, lean_object* v_toBind_1051_, lean_object* v___x_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___f_1054_; lean_object* v___x_1055_; 
v___f_1054_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1054_, 0, v_start_1049_);
lean_closure_set(v___f_1054_, 1, v_a_1053_);
lean_closure_set(v___f_1054_, 2, v_toPure_1050_);
v___x_1055_ = lean_apply_4(v_toBind_1051_, lean_box(0), lean_box(0), v___x_1052_, v___f_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object* v_toPure_1056_, lean_object* v_toBind_1057_, lean_object* v___x_1058_, lean_object* v_act_1059_, lean_object* v_start_1060_){
_start:
{
lean_object* v___f_1061_; lean_object* v___x_1062_; 
lean_inc(v_toBind_1057_);
v___f_1061_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1061_, 0, v_start_1060_);
lean_closure_set(v___f_1061_, 1, v_toPure_1056_);
lean_closure_set(v___f_1061_, 2, v_toBind_1057_);
lean_closure_set(v___f_1061_, 3, v___x_1058_);
v___x_1062_ = lean_apply_4(v_toBind_1057_, lean_box(0), lean_box(0), v_act_1059_, v___f_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object* v_start_1063_, lean_object* v_a_1064_, lean_object* v_toPure_1065_, lean_object* v_stop_1066_){
_start:
{
double v___x_1067_; double v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1067_ = lean_float_of_nat(v_start_1063_);
v___x_1068_ = lean_float_of_nat(v_stop_1066_);
v___x_1069_ = lean_box_float(v___x_1067_);
v___x_1070_ = lean_box_float(v___x_1068_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_a_1064_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_apply_2(v_toPure_1065_, lean_box(0), v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object* v_start_1074_, lean_object* v_toPure_1075_, lean_object* v_toBind_1076_, lean_object* v___x_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v___f_1079_; lean_object* v___x_1080_; 
v___f_1079_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1079_, 0, v_start_1074_);
lean_closure_set(v___f_1079_, 1, v_a_1078_);
lean_closure_set(v___f_1079_, 2, v_toPure_1075_);
v___x_1080_ = lean_apply_4(v_toBind_1076_, lean_box(0), lean_box(0), v___x_1077_, v___f_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object* v_toPure_1081_, lean_object* v_toBind_1082_, lean_object* v___x_1083_, lean_object* v_act_1084_, lean_object* v_start_1085_){
_start:
{
lean_object* v___f_1086_; lean_object* v___x_1087_; 
lean_inc(v_toBind_1082_);
v___f_1086_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1086_, 0, v_start_1085_);
lean_closure_set(v___f_1086_, 1, v_toPure_1081_);
lean_closure_set(v___f_1086_, 2, v_toBind_1082_);
lean_closure_set(v___f_1086_, 3, v___x_1083_);
v___x_1087_ = lean_apply_4(v_toBind_1082_, lean_box(0), lean_box(0), v_act_1084_, v___f_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_opts_1092_, lean_object* v_act_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v_toApplicative_1095_; lean_object* v_toBind_1096_; lean_object* v_toPure_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1094_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1095_ = lean_ctor_get(v_inst_1090_, 0);
lean_inc_ref(v_toApplicative_1095_);
v_toBind_1096_ = lean_ctor_get(v_inst_1090_, 1);
lean_inc(v_toBind_1096_);
lean_dec_ref(v_inst_1090_);
v_toPure_1097_ = lean_ctor_get(v_toApplicative_1095_, 1);
lean_inc(v_toPure_1097_);
lean_dec_ref(v_toApplicative_1095_);
v___x_1098_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1099_ = l_Lean_Option_get___redArg(v___x_1094_, v_opts_1092_, v___x_1098_);
v___x_1100_ = lean_unbox(v___x_1099_);
lean_dec(v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; 
v___x_1101_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1102_ = lean_apply_2(v_inst_1091_, lean_box(0), v___x_1101_);
lean_inc(v___x_1102_);
lean_inc(v_toBind_1096_);
v___f_1103_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1103_, 0, v_toPure_1097_);
lean_closure_set(v___f_1103_, 1, v_toBind_1096_);
lean_closure_set(v___f_1103_, 2, v___x_1102_);
lean_closure_set(v___f_1103_, 3, v_act_1093_);
v___x_1104_ = lean_apply_4(v_toBind_1096_, lean_box(0), lean_box(0), v___x_1102_, v___f_1103_);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; 
v___x_1105_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1106_ = lean_apply_2(v_inst_1091_, lean_box(0), v___x_1105_);
lean_inc(v___x_1106_);
lean_inc(v_toBind_1096_);
v___f_1107_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1107_, 0, v_toPure_1097_);
lean_closure_set(v___f_1107_, 1, v_toBind_1096_);
lean_closure_set(v___f_1107_, 2, v___x_1106_);
lean_closure_set(v___f_1107_, 3, v_act_1093_);
v___x_1108_ = lean_apply_4(v_toBind_1096_, lean_box(0), lean_box(0), v___x_1106_, v___f_1107_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_opts_1111_, lean_object* v_act_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(v_inst_1109_, v_inst_1110_, v_opts_1111_, v_act_1112_);
lean_dec_ref(v_opts_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object* v_00_u03b1_1114_, lean_object* v_m_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_opts_1118_, lean_object* v_act_1119_){
_start:
{
lean_object* v___x_1120_; lean_object* v_toApplicative_1121_; lean_object* v_toBind_1122_; lean_object* v_toPure_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1120_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1121_ = lean_ctor_get(v_inst_1116_, 0);
lean_inc_ref(v_toApplicative_1121_);
v_toBind_1122_ = lean_ctor_get(v_inst_1116_, 1);
lean_inc(v_toBind_1122_);
lean_dec_ref(v_inst_1116_);
v_toPure_1123_ = lean_ctor_get(v_toApplicative_1121_, 1);
lean_inc(v_toPure_1123_);
lean_dec_ref(v_toApplicative_1121_);
v___x_1124_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1125_ = l_Lean_Option_get___redArg(v___x_1120_, v_opts_1118_, v___x_1124_);
v___x_1126_ = lean_unbox(v___x_1125_);
lean_dec(v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; 
v___x_1127_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1128_ = lean_apply_2(v_inst_1117_, lean_box(0), v___x_1127_);
lean_inc(v___x_1128_);
lean_inc(v_toBind_1122_);
v___f_1129_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1129_, 0, v_toPure_1123_);
lean_closure_set(v___f_1129_, 1, v_toBind_1122_);
lean_closure_set(v___f_1129_, 2, v___x_1128_);
lean_closure_set(v___f_1129_, 3, v_act_1119_);
v___x_1130_ = lean_apply_4(v_toBind_1122_, lean_box(0), lean_box(0), v___x_1128_, v___f_1129_);
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1132_ = lean_apply_2(v_inst_1117_, lean_box(0), v___x_1131_);
lean_inc(v___x_1132_);
lean_inc(v_toBind_1122_);
v___f_1133_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1133_, 0, v_toPure_1123_);
lean_closure_set(v___f_1133_, 1, v_toBind_1122_);
lean_closure_set(v___f_1133_, 2, v___x_1132_);
lean_closure_set(v___f_1133_, 3, v_act_1119_);
v___x_1134_ = lean_apply_4(v_toBind_1122_, lean_box(0), lean_box(0), v___x_1132_, v___f_1133_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object* v_00_u03b1_1135_, lean_object* v_m_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_opts_1139_, lean_object* v_act_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(v_00_u03b1_1135_, v_m_1136_, v_inst_1137_, v_inst_1138_, v_opts_1139_, v_act_1140_);
lean_dec_ref(v_opts_1139_);
return v_res_1141_;
}
}
static double _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0(void){
_start:
{
lean_object* v___x_1142_; double v___x_1143_; 
v___x_1142_ = lean_unsigned_to_nat(1000u);
v___x_1143_ = lean_float_of_nat(v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object* v_o_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1145_ = l_Lean_KVMap_instValueBool;
v___x_1146_ = l_Lean_KVMap_instValueNat;
v___x_1147_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1148_ = l_Lean_Option_get___redArg(v___x_1145_, v_o_1144_, v___x_1147_);
v___x_1149_ = lean_unbox(v___x_1148_);
lean_dec(v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; double v___x_1152_; double v___x_1153_; double v___x_1154_; 
v___x_1150_ = l_Lean_trace_profiler_threshold;
v___x_1151_ = l_Lean_Option_get___redArg(v___x_1146_, v_o_1144_, v___x_1150_);
v___x_1152_ = lean_float_of_nat(v___x_1151_);
v___x_1153_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1154_ = lean_float_div(v___x_1152_, v___x_1153_);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; double v___x_1157_; 
v___x_1155_ = l_Lean_trace_profiler_threshold;
v___x_1156_ = l_Lean_Option_get___redArg(v___x_1146_, v_o_1144_, v___x_1155_);
v___x_1157_ = lean_float_of_nat(v___x_1156_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object* v_o_1158_){
_start:
{
double v_res_1159_; lean_object* v_r_1160_; 
v_res_1159_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1158_);
lean_dec_ref(v_o_1158_);
v_r_1160_ = lean_box_float(v_res_1159_);
return v_r_1160_;
}
}
static lean_object* _init_l_Lean_instMonadAlwaysExceptEIO___closed__0(void){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object* v_00_u03b5_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___closed__0, &l_Lean_instMonadAlwaysExceptEIO___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___closed__0);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object* v_inst_1164_, lean_object* v_always_1165_){
_start:
{
lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___x_1168_; 
lean_inc_ref(v_always_1165_);
v___f_1166_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1166_, 0, v_always_1165_);
lean_closure_set(v___f_1166_, 1, v_inst_1164_);
v___f_1167_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_1167_, 0, v_always_1165_);
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___f_1166_);
lean_ctor_set(v___x_1168_, 1, v___f_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object* v_m_1169_, lean_object* v_inst_1170_, lean_object* v_00_u03b5_1171_, lean_object* v_00_u03c3_1172_, lean_object* v_always_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_1170_, v_always_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object* v_always_1175_){
_start:
{
lean_object* v___f_1176_; lean_object* v___f_1177_; lean_object* v___x_1178_; 
lean_inc_ref(v_always_1175_);
v___f_1176_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1176_, 0, v_always_1175_);
v___f_1177_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1177_, 0, v_always_1175_);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___f_1176_);
lean_ctor_set(v___x_1178_, 1, v___f_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object* v_m_1179_, lean_object* v_00_u03b5_1180_, lean_object* v_00_u03c9_1181_, lean_object* v_00_u03c3_1182_, lean_object* v_always_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object* v_always_1185_){
_start:
{
lean_object* v___f_1186_; lean_object* v___f_1187_; lean_object* v___x_1188_; 
lean_inc_ref(v_always_1185_);
v___f_1186_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1186_, 0, v_always_1185_);
v___f_1187_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1187_, 0, v_always_1185_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___f_1186_);
lean_ctor_set(v___x_1188_, 1, v___f_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object* v_m_1189_, lean_object* v_00_u03b5_1190_, lean_object* v_00_u03c1_1191_, lean_object* v_always_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object* v_always_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1195_, v_inst_1196_, v_inst_1197_, v_always_1194_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object* v_00_u03b1_1199_, lean_object* v_m_1200_, lean_object* v_00_u03b5_1201_, lean_object* v_00_u03c9_1202_, lean_object* v_00_u03b2_1203_, lean_object* v_always_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1205_, v_inst_1206_, v_inst_1207_, v_always_1204_);
return v___x_1208_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultBool___lam__0(lean_object* v_x_1215_){
_start:
{
if (lean_obj_tag(v_x_1215_) == 0)
{
uint8_t v___x_1216_; 
v___x_1216_ = 2;
return v___x_1216_;
}
else
{
lean_object* v_a_1217_; uint8_t v___x_1218_; 
v_a_1217_ = lean_ctor_get(v_x_1215_, 0);
v___x_1218_ = lean_unbox(v_a_1217_);
if (v___x_1218_ == 0)
{
uint8_t v___x_1219_; 
v___x_1219_ = 1;
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
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object* v_x_1221_){
_start:
{
uint8_t v_res_1222_; lean_object* v_r_1223_; 
v_res_1222_ = l_Lean_instExceptToTraceResultBool___lam__0(v_x_1221_);
lean_dec_ref(v_x_1221_);
v_r_1223_ = lean_box(v_res_1222_);
return v_r_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object* v_00_u03b5_1225_){
_start:
{
lean_object* v___f_1226_; 
v___f_1226_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___closed__0));
return v___f_1226_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultOption___lam__0(lean_object* v_x_1227_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 0)
{
uint8_t v___x_1228_; 
v___x_1228_ = 2;
return v___x_1228_;
}
else
{
lean_object* v_a_1229_; 
v_a_1229_ = lean_ctor_get(v_x_1227_, 0);
if (lean_obj_tag(v_a_1229_) == 0)
{
uint8_t v___x_1230_; 
v___x_1230_ = 1;
return v___x_1230_;
}
else
{
uint8_t v___x_1231_; 
v___x_1231_ = 0;
return v___x_1231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___lam__0___boxed(lean_object* v_x_1232_){
_start:
{
uint8_t v_res_1233_; lean_object* v_r_1234_; 
v_res_1233_ = l_Lean_instExceptToTraceResultOption___lam__0(v_x_1232_);
lean_dec_ref(v_x_1232_);
v_r_1234_ = lean_box(v_res_1233_);
return v_r_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object* v_00_u03b1_1236_, lean_object* v_00_u03b5_1237_){
_start:
{
lean_object* v___f_1238_; 
v___f_1238_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___closed__0));
return v___f_1238_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResultExpr___lam__0(lean_object* v_x_1239_){
_start:
{
if (lean_obj_tag(v_x_1239_) == 0)
{
uint8_t v___x_1240_; 
v___x_1240_ = 2;
return v___x_1240_;
}
else
{
lean_object* v_a_1241_; uint8_t v___x_1242_; 
v_a_1241_ = lean_ctor_get(v_x_1239_, 0);
v___x_1242_ = l_Lean_Expr_hasSyntheticSorry(v_a_1241_);
if (v___x_1242_ == 0)
{
uint8_t v___x_1243_; 
v___x_1243_ = 0;
return v___x_1243_;
}
else
{
uint8_t v___x_1244_; 
v___x_1244_ = 1;
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___lam__0___boxed(lean_object* v_x_1245_){
_start:
{
uint8_t v_res_1246_; lean_object* v_r_1247_; 
v_res_1246_ = l_Lean_instExceptToTraceResultExpr___lam__0(v_x_1245_);
lean_dec_ref(v_x_1245_);
v_r_1247_ = lean_box(v_res_1246_);
return v_r_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr(lean_object* v_00_u03b5_1249_){
_start:
{
lean_object* v___f_1250_; 
v___f_1250_ = ((lean_object*)(l_Lean_instExceptToTraceResultExpr___closed__0));
return v___f_1250_;
}
}
LEAN_EXPORT uint8_t l_Lean_instExceptToTraceResult___lam__0(lean_object* v_x_1251_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = 2;
return v___x_1252_;
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = 0;
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___lam__0___boxed(lean_object* v_x_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Lean_instExceptToTraceResult___lam__0(v_x_1254_);
lean_dec_ref(v_x_1254_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object* v_00_u03b1_1258_, lean_object* v_00_u03b5_1259_){
_start:
{
lean_object* v___f_1260_; 
v___f_1260_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
return v___f_1260_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___redArg(lean_object* v_inst_1261_, lean_object* v_e_1262_){
_start:
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = lean_apply_1(v_inst_1261_, v_e_1262_);
v___x_1264_ = lean_unbox(v___x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___redArg___boxed(lean_object* v_inst_1265_, lean_object* v_e_1266_){
_start:
{
uint8_t v_res_1267_; lean_object* v_r_1268_; 
v_res_1267_ = l_Lean_Except_toTraceResult___redArg(v_inst_1265_, v_e_1266_);
v_r_1268_ = lean_box(v_res_1267_);
return v_r_1268_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult(lean_object* v_00_u03b1_1269_, lean_object* v_00_u03b5_1270_, lean_object* v_inst_1271_, lean_object* v_e_1272_){
_start:
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = lean_apply_1(v_inst_1271_, v_e_1272_);
v___x_1274_ = lean_unbox(v___x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___boxed(lean_object* v_00_u03b1_1275_, lean_object* v_00_u03b5_1276_, lean_object* v_inst_1277_, lean_object* v_e_1278_){
_start:
{
uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_res_1279_ = l_Lean_Except_toTraceResult(v_00_u03b1_1275_, v_00_u03b5_1276_, v_inst_1277_, v_e_1278_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object* v_oldTraces_1281_, lean_object* v_s_1282_){
_start:
{
uint64_t v_tid_1283_; lean_object* v_traces_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1292_; 
v_tid_1283_ = lean_ctor_get_uint64(v_s_1282_, sizeof(void*)*1);
v_traces_1284_ = lean_ctor_get(v_s_1282_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_s_1282_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1286_ = v_s_1282_;
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_traces_1284_);
lean_dec(v_s_1282_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1281_, v_traces_1284_);
lean_dec_ref(v_traces_1284_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1288_);
v___x_1290_ = v___x_1286_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
lean_ctor_set_uint64(v_reuseFailAlloc_1291_, sizeof(void*)*1, v_tid_1283_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__0));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object* v_toPure_1296_, lean_object* v_x_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1);
v___x_1299_ = lean_apply_2(v_toPure_1296_, lean_box(0), v___x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___boxed(lean_object* v_toPure_1300_, lean_object* v_x_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(v_toPure_1300_, v_x_1301_);
lean_dec(v_x_1301_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object* v_inst_1303_, lean_object* v___x_1304_, lean_object* v_fst_1305_, lean_object* v_____r_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_MonadExcept_ofExcept___redArg(v_inst_1303_, v___x_1304_, v_fst_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_oldTraces_1312_, lean_object* v_ref_1313_, lean_object* v_toBind_1314_, lean_object* v___f_1315_, lean_object* v_inst_1316_, lean_object* v_fst_1317_, lean_object* v_cls_1318_, uint8_t v_collapsed_1319_, lean_object* v_tag_1320_, uint8_t v___x_1321_, double v_fst_1322_, double v_snd_1323_, lean_object* v_m_1324_){
_start:
{
lean_object* v_data_1326_; lean_object* v_result_1329_; lean_object* v___x_1330_; double v___x_1331_; lean_object* v_data_1332_; 
v_result_1329_ = lean_apply_1(v_inst_1316_, v_fst_1317_);
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v_result_1329_);
v___x_1331_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_1320_);
lean_inc_ref(v___x_1330_);
lean_inc(v_cls_1318_);
v_data_1332_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1332_, 0, v_cls_1318_);
lean_ctor_set(v_data_1332_, 1, v___x_1330_);
lean_ctor_set(v_data_1332_, 2, v_tag_1320_);
lean_ctor_set_float(v_data_1332_, sizeof(void*)*3, v___x_1331_);
lean_ctor_set_float(v_data_1332_, sizeof(void*)*3 + 8, v___x_1331_);
lean_ctor_set_uint8(v_data_1332_, sizeof(void*)*3 + 16, v_collapsed_1319_);
if (v___x_1321_ == 0)
{
lean_dec_ref_known(v___x_1330_, 1);
lean_dec_ref(v_tag_1320_);
lean_dec(v_cls_1318_);
v_data_1326_ = v_data_1332_;
goto v___jp_1325_;
}
else
{
lean_object* v_data_1333_; 
lean_dec_ref_known(v_data_1332_, 3);
v_data_1333_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1333_, 0, v_cls_1318_);
lean_ctor_set(v_data_1333_, 1, v___x_1330_);
lean_ctor_set(v_data_1333_, 2, v_tag_1320_);
lean_ctor_set_float(v_data_1333_, sizeof(void*)*3, v_fst_1322_);
lean_ctor_set_float(v_data_1333_, sizeof(void*)*3 + 8, v_snd_1323_);
lean_ctor_set_uint8(v_data_1333_, sizeof(void*)*3 + 16, v_collapsed_1319_);
v_data_1326_ = v_data_1333_;
goto v___jp_1325_;
}
v___jp_1325_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_1308_, v_inst_1309_, v_inst_1310_, v_inst_1311_, v_oldTraces_1312_, v_data_1326_, v_ref_1313_, v_m_1324_);
v___x_1328_ = lean_apply_4(v_toBind_1314_, lean_box(0), lean_box(0), v___x_1327_, v___f_1315_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_1334_ = _args[0];
lean_object* v_inst_1335_ = _args[1];
lean_object* v_inst_1336_ = _args[2];
lean_object* v_inst_1337_ = _args[3];
lean_object* v_oldTraces_1338_ = _args[4];
lean_object* v_ref_1339_ = _args[5];
lean_object* v_toBind_1340_ = _args[6];
lean_object* v___f_1341_ = _args[7];
lean_object* v_inst_1342_ = _args[8];
lean_object* v_fst_1343_ = _args[9];
lean_object* v_cls_1344_ = _args[10];
lean_object* v_collapsed_1345_ = _args[11];
lean_object* v_tag_1346_ = _args[12];
lean_object* v___x_1347_ = _args[13];
lean_object* v_fst_1348_ = _args[14];
lean_object* v_snd_1349_ = _args[15];
lean_object* v_m_1350_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1351_; uint8_t v___x_436__boxed_1352_; double v_fst_437__boxed_1353_; double v_snd_438__boxed_1354_; lean_object* v_res_1355_; 
v_collapsed_boxed_1351_ = lean_unbox(v_collapsed_1345_);
v___x_436__boxed_1352_ = lean_unbox(v___x_1347_);
v_fst_437__boxed_1353_ = lean_unbox_float(v_fst_1348_);
lean_dec_ref(v_fst_1348_);
v_snd_438__boxed_1354_ = lean_unbox_float(v_snd_1349_);
lean_dec_ref(v_snd_1349_);
v_res_1355_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1334_, v_inst_1335_, v_inst_1336_, v_inst_1337_, v_oldTraces_1338_, v_ref_1339_, v_toBind_1340_, v___f_1341_, v_inst_1342_, v_fst_1343_, v_cls_1344_, v_collapsed_boxed_1351_, v_tag_1346_, v___x_436__boxed_1352_, v_fst_437__boxed_1353_, v_snd_438__boxed_1354_, v_m_1350_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object* v_always_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_oldTraces_1361_, lean_object* v_toBind_1362_, lean_object* v___f_1363_, lean_object* v_inst_1364_, lean_object* v_fst_1365_, lean_object* v_cls_1366_, uint8_t v_collapsed_1367_, lean_object* v_tag_1368_, uint8_t v___x_1369_, double v_fst_1370_, double v_snd_1371_, lean_object* v_msg_1372_, lean_object* v___f_1373_, lean_object* v_ref_1374_){
_start:
{
lean_object* v_tryCatch_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___f_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_tryCatch_1375_ = lean_ctor_get(v_always_1356_, 1);
lean_inc(v_tryCatch_1375_);
lean_dec_ref(v_always_1356_);
v___x_1376_ = lean_box(v_collapsed_1367_);
v___x_1377_ = lean_box(v___x_1369_);
v___x_1378_ = lean_box_float(v_fst_1370_);
v___x_1379_ = lean_box_float(v_snd_1371_);
lean_inc_ref(v_fst_1365_);
lean_inc(v_toBind_1362_);
v___f_1380_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1380_, 0, v_inst_1357_);
lean_closure_set(v___f_1380_, 1, v_inst_1358_);
lean_closure_set(v___f_1380_, 2, v_inst_1359_);
lean_closure_set(v___f_1380_, 3, v_inst_1360_);
lean_closure_set(v___f_1380_, 4, v_oldTraces_1361_);
lean_closure_set(v___f_1380_, 5, v_ref_1374_);
lean_closure_set(v___f_1380_, 6, v_toBind_1362_);
lean_closure_set(v___f_1380_, 7, v___f_1363_);
lean_closure_set(v___f_1380_, 8, v_inst_1364_);
lean_closure_set(v___f_1380_, 9, v_fst_1365_);
lean_closure_set(v___f_1380_, 10, v_cls_1366_);
lean_closure_set(v___f_1380_, 11, v___x_1376_);
lean_closure_set(v___f_1380_, 12, v_tag_1368_);
lean_closure_set(v___f_1380_, 13, v___x_1377_);
lean_closure_set(v___f_1380_, 14, v___x_1378_);
lean_closure_set(v___f_1380_, 15, v___x_1379_);
v___x_1381_ = lean_apply_1(v_msg_1372_, v_fst_1365_);
v___x_1382_ = lean_apply_3(v_tryCatch_1375_, lean_box(0), v___x_1381_, v___f_1373_);
v___x_1383_ = lean_apply_4(v_toBind_1362_, lean_box(0), lean_box(0), v___x_1382_, v___f_1380_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_1384_ = _args[0];
lean_object* v_inst_1385_ = _args[1];
lean_object* v_inst_1386_ = _args[2];
lean_object* v_inst_1387_ = _args[3];
lean_object* v_inst_1388_ = _args[4];
lean_object* v_oldTraces_1389_ = _args[5];
lean_object* v_toBind_1390_ = _args[6];
lean_object* v___f_1391_ = _args[7];
lean_object* v_inst_1392_ = _args[8];
lean_object* v_fst_1393_ = _args[9];
lean_object* v_cls_1394_ = _args[10];
lean_object* v_collapsed_1395_ = _args[11];
lean_object* v_tag_1396_ = _args[12];
lean_object* v___x_1397_ = _args[13];
lean_object* v_fst_1398_ = _args[14];
lean_object* v_snd_1399_ = _args[15];
lean_object* v_msg_1400_ = _args[16];
lean_object* v___f_1401_ = _args[17];
lean_object* v_ref_1402_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_1403_; uint8_t v___x_477__boxed_1404_; double v_fst_478__boxed_1405_; double v_snd_479__boxed_1406_; lean_object* v_res_1407_; 
v_collapsed_boxed_1403_ = lean_unbox(v_collapsed_1395_);
v___x_477__boxed_1404_ = lean_unbox(v___x_1397_);
v_fst_478__boxed_1405_ = lean_unbox_float(v_fst_1398_);
lean_dec_ref(v_fst_1398_);
v_snd_479__boxed_1406_ = lean_unbox_float(v_snd_1399_);
lean_dec_ref(v_snd_1399_);
v_res_1407_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(v_always_1384_, v_inst_1385_, v_inst_1386_, v_inst_1387_, v_inst_1388_, v_oldTraces_1389_, v_toBind_1390_, v___f_1391_, v_inst_1392_, v_fst_1393_, v_cls_1394_, v_collapsed_boxed_1403_, v_tag_1396_, v___x_477__boxed_1404_, v_fst_478__boxed_1405_, v_snd_479__boxed_1406_, v_msg_1400_, v___f_1401_, v_ref_1402_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object* v_inst_1408_, lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_always_1412_, lean_object* v_inst_1413_, lean_object* v_cls_1414_, uint8_t v_collapsed_1415_, lean_object* v_tag_1416_, lean_object* v_opts_1417_, uint8_t v_clsEnabled_1418_, lean_object* v_oldTraces_1419_, lean_object* v_msg_1420_, lean_object* v_resStartStop_1421_){
_start:
{
lean_object* v___x_1422_; lean_object* v_toApplicative_1423_; lean_object* v_toBind_1424_; lean_object* v___x_1425_; lean_object* v_snd_1426_; lean_object* v_toPure_1427_; lean_object* v_fst_1428_; lean_object* v_fst_1429_; lean_object* v_snd_1430_; lean_object* v___f_1431_; lean_object* v___f_1432_; lean_object* v___f_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___f_1437_; uint8_t v___y_1442_; double v___y_1447_; uint8_t v___x_1452_; 
v___x_1422_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1423_ = lean_ctor_get(v_inst_1408_, 0);
v_toBind_1424_ = lean_ctor_get(v_inst_1408_, 1);
lean_inc_n(v_toBind_1424_, 2);
lean_inc_ref(v_always_1412_);
v___x_1425_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1412_);
v_snd_1426_ = lean_ctor_get(v_resStartStop_1421_, 1);
lean_inc(v_snd_1426_);
v_toPure_1427_ = lean_ctor_get(v_toApplicative_1423_, 1);
v_fst_1428_ = lean_ctor_get(v_resStartStop_1421_, 0);
lean_inc_n(v_fst_1428_, 2);
lean_dec_ref(v_resStartStop_1421_);
v_fst_1429_ = lean_ctor_get(v_snd_1426_, 0);
lean_inc_n(v_fst_1429_, 2);
v_snd_1430_ = lean_ctor_get(v_snd_1426_, 1);
lean_inc_n(v_snd_1430_, 2);
lean_dec(v_snd_1426_);
lean_inc_ref(v_oldTraces_1419_);
v___f_1431_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1431_, 0, v_oldTraces_1419_);
lean_inc(v_toPure_1427_);
v___f_1432_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1432_, 0, v_toPure_1427_);
lean_inc_ref(v_inst_1408_);
v___f_1433_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1433_, 0, v_inst_1408_);
lean_closure_set(v___f_1433_, 1, v___x_1425_);
lean_closure_set(v___f_1433_, 2, v_fst_1428_);
v___x_1434_ = l_Lean_trace_profiler;
v___x_1435_ = l_Lean_Option_get___redArg(v___x_1422_, v_opts_1417_, v___x_1434_);
v___x_1436_ = lean_box(v_collapsed_1415_);
lean_inc(v___x_1435_);
lean_inc_ref(v___f_1433_);
lean_inc_ref(v_inst_1410_);
lean_inc_ref(v_inst_1409_);
v___f_1437_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3___boxed), 19, 18);
lean_closure_set(v___f_1437_, 0, v_always_1412_);
lean_closure_set(v___f_1437_, 1, v_inst_1408_);
lean_closure_set(v___f_1437_, 2, v_inst_1409_);
lean_closure_set(v___f_1437_, 3, v_inst_1410_);
lean_closure_set(v___f_1437_, 4, v_inst_1411_);
lean_closure_set(v___f_1437_, 5, v_oldTraces_1419_);
lean_closure_set(v___f_1437_, 6, v_toBind_1424_);
lean_closure_set(v___f_1437_, 7, v___f_1433_);
lean_closure_set(v___f_1437_, 8, v_inst_1413_);
lean_closure_set(v___f_1437_, 9, v_fst_1428_);
lean_closure_set(v___f_1437_, 10, v_cls_1414_);
lean_closure_set(v___f_1437_, 11, v___x_1436_);
lean_closure_set(v___f_1437_, 12, v_tag_1416_);
lean_closure_set(v___f_1437_, 13, v___x_1435_);
lean_closure_set(v___f_1437_, 14, v_fst_1429_);
lean_closure_set(v___f_1437_, 15, v_snd_1430_);
lean_closure_set(v___f_1437_, 16, v_msg_1420_);
lean_closure_set(v___f_1437_, 17, v___f_1432_);
v___x_1452_ = lean_unbox(v___x_1435_);
if (v___x_1452_ == 0)
{
uint8_t v___x_1453_; 
lean_dec(v_snd_1430_);
lean_dec(v_fst_1429_);
v___x_1453_ = lean_unbox(v___x_1435_);
lean_dec(v___x_1435_);
v___y_1442_ = v___x_1453_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
lean_dec(v___x_1435_);
v___x_1454_ = l_Lean_KVMap_instValueNat;
v___x_1455_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1456_ = l_Lean_Option_get___redArg(v___x_1422_, v_opts_1417_, v___x_1455_);
v___x_1457_ = lean_unbox(v___x_1456_);
lean_dec(v___x_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; double v___x_1460_; double v___x_1461_; double v___x_1462_; 
v___x_1458_ = l_Lean_trace_profiler_threshold;
v___x_1459_ = l_Lean_Option_get___redArg(v___x_1454_, v_opts_1417_, v___x_1458_);
v___x_1460_ = lean_float_of_nat(v___x_1459_);
v___x_1461_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1462_ = lean_float_div(v___x_1460_, v___x_1461_);
v___y_1447_ = v___x_1462_;
goto v___jp_1446_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; double v___x_1465_; 
v___x_1463_ = l_Lean_trace_profiler_threshold;
v___x_1464_ = l_Lean_Option_get___redArg(v___x_1454_, v_opts_1417_, v___x_1463_);
v___x_1465_ = lean_float_of_nat(v___x_1464_);
v___y_1447_ = v___x_1465_;
goto v___jp_1446_;
}
}
v___jp_1438_:
{
lean_object* v_getRef_1439_; lean_object* v___x_1440_; 
v_getRef_1439_ = lean_ctor_get(v_inst_1410_, 0);
lean_inc(v_getRef_1439_);
lean_dec_ref(v_inst_1410_);
v___x_1440_ = lean_apply_4(v_toBind_1424_, lean_box(0), lean_box(0), v_getRef_1439_, v___f_1437_);
return v___x_1440_;
}
v___jp_1441_:
{
if (v_clsEnabled_1418_ == 0)
{
if (v___y_1442_ == 0)
{
lean_object* v_modifyTraceState_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec_ref(v___f_1437_);
lean_dec_ref(v_inst_1410_);
v_modifyTraceState_1443_ = lean_ctor_get(v_inst_1409_, 0);
lean_inc(v_modifyTraceState_1443_);
lean_dec_ref(v_inst_1409_);
v___x_1444_ = lean_apply_1(v_modifyTraceState_1443_, v___f_1431_);
v___x_1445_ = lean_apply_4(v_toBind_1424_, lean_box(0), lean_box(0), v___x_1444_, v___f_1433_);
return v___x_1445_;
}
else
{
lean_dec_ref(v___f_1433_);
lean_dec_ref(v___f_1431_);
lean_dec_ref(v_inst_1409_);
goto v___jp_1438_;
}
}
else
{
lean_dec_ref(v___f_1433_);
lean_dec_ref(v___f_1431_);
lean_dec_ref(v_inst_1409_);
goto v___jp_1438_;
}
}
v___jp_1446_:
{
double v___x_1448_; double v___x_1449_; double v___x_1450_; uint8_t v___x_1451_; 
v___x_1448_ = lean_unbox_float(v_snd_1430_);
lean_dec(v_snd_1430_);
v___x_1449_ = lean_unbox_float(v_fst_1429_);
lean_dec(v_fst_1429_);
v___x_1450_ = lean_float_sub(v___x_1448_, v___x_1449_);
v___x_1451_ = lean_float_decLt(v___y_1447_, v___x_1450_);
v___y_1442_ = v___x_1451_;
goto v___jp_1441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_always_1470_, lean_object* v_inst_1471_, lean_object* v_cls_1472_, lean_object* v_collapsed_1473_, lean_object* v_tag_1474_, lean_object* v_opts_1475_, lean_object* v_clsEnabled_1476_, lean_object* v_oldTraces_1477_, lean_object* v_msg_1478_, lean_object* v_resStartStop_1479_){
_start:
{
uint8_t v_collapsed_boxed_1480_; uint8_t v_clsEnabled_boxed_1481_; lean_object* v_res_1482_; 
v_collapsed_boxed_1480_ = lean_unbox(v_collapsed_1473_);
v_clsEnabled_boxed_1481_ = lean_unbox(v_clsEnabled_1476_);
v_res_1482_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1466_, v_inst_1467_, v_inst_1468_, v_inst_1469_, v_always_1470_, v_inst_1471_, v_cls_1472_, v_collapsed_boxed_1480_, v_tag_1474_, v_opts_1475_, v_clsEnabled_boxed_1481_, v_oldTraces_1477_, v_msg_1478_, v_resStartStop_1479_);
lean_dec_ref(v_opts_1475_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object* v_00_u03b1_1483_, lean_object* v_m_1484_, lean_object* v_inst_1485_, lean_object* v_inst_1486_, lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_00_u03b5_1489_, lean_object* v_always_1490_, lean_object* v_inst_1491_, lean_object* v_cls_1492_, uint8_t v_collapsed_1493_, lean_object* v_tag_1494_, lean_object* v_opts_1495_, uint8_t v_clsEnabled_1496_, lean_object* v_oldTraces_1497_, lean_object* v_msg_1498_, lean_object* v_resStartStop_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1485_, v_inst_1486_, v_inst_1487_, v_inst_1488_, v_always_1490_, v_inst_1491_, v_cls_1492_, v_collapsed_1493_, v_tag_1494_, v_opts_1495_, v_clsEnabled_1496_, v_oldTraces_1497_, v_msg_1498_, v_resStartStop_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_1501_ = _args[0];
lean_object* v_m_1502_ = _args[1];
lean_object* v_inst_1503_ = _args[2];
lean_object* v_inst_1504_ = _args[3];
lean_object* v_inst_1505_ = _args[4];
lean_object* v_inst_1506_ = _args[5];
lean_object* v_00_u03b5_1507_ = _args[6];
lean_object* v_always_1508_ = _args[7];
lean_object* v_inst_1509_ = _args[8];
lean_object* v_cls_1510_ = _args[9];
lean_object* v_collapsed_1511_ = _args[10];
lean_object* v_tag_1512_ = _args[11];
lean_object* v_opts_1513_ = _args[12];
lean_object* v_clsEnabled_1514_ = _args[13];
lean_object* v_oldTraces_1515_ = _args[14];
lean_object* v_msg_1516_ = _args[15];
lean_object* v_resStartStop_1517_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1518_; uint8_t v_clsEnabled_boxed_1519_; lean_object* v_res_1520_; 
v_collapsed_boxed_1518_ = lean_unbox(v_collapsed_1511_);
v_clsEnabled_boxed_1519_ = lean_unbox(v_clsEnabled_1514_);
v_res_1520_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(v_00_u03b1_1501_, v_m_1502_, v_inst_1503_, v_inst_1504_, v_inst_1505_, v_inst_1506_, v_00_u03b5_1507_, v_always_1508_, v_inst_1509_, v_cls_1510_, v_collapsed_boxed_1518_, v_tag_1512_, v_opts_1513_, v_clsEnabled_boxed_1519_, v_oldTraces_1515_, v_msg_1516_, v_resStartStop_1517_);
lean_dec_ref(v_opts_1513_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_always_1525_, lean_object* v_inst_1526_, lean_object* v_cls_1527_, uint8_t v_collapsed_1528_, lean_object* v_tag_1529_, lean_object* v_opts_1530_, uint8_t v_clsEnabled_1531_, lean_object* v_oldTraces_1532_, lean_object* v_msg_1533_, lean_object* v_resStartStop_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1521_, v_inst_1522_, v_inst_1523_, v_inst_1524_, v_always_1525_, v_inst_1526_, v_cls_1527_, v_collapsed_1528_, v_tag_1529_, v_opts_1530_, v_clsEnabled_1531_, v_oldTraces_1532_, v_msg_1533_, v_resStartStop_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_always_1540_, lean_object* v_inst_1541_, lean_object* v_cls_1542_, lean_object* v_collapsed_1543_, lean_object* v_tag_1544_, lean_object* v_opts_1545_, lean_object* v_clsEnabled_1546_, lean_object* v_oldTraces_1547_, lean_object* v_msg_1548_, lean_object* v_resStartStop_1549_){
_start:
{
uint8_t v_collapsed_boxed_1550_; uint8_t v_clsEnabled_boxed_1551_; lean_object* v_res_1552_; 
v_collapsed_boxed_1550_ = lean_unbox(v_collapsed_1543_);
v_clsEnabled_boxed_1551_ = lean_unbox(v_clsEnabled_1546_);
v_res_1552_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1536_, v_inst_1537_, v_inst_1538_, v_inst_1539_, v_always_1540_, v_inst_1541_, v_cls_1542_, v_collapsed_boxed_1550_, v_tag_1544_, v_opts_1545_, v_clsEnabled_boxed_1551_, v_oldTraces_1547_, v_msg_1548_, v_resStartStop_1549_);
lean_dec_ref(v_opts_1545_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object* v_toPure_1553_, lean_object* v_ex_1554_){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v_ex_1554_);
v___x_1556_ = lean_apply_2(v_toPure_1553_, lean_box(0), v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object* v_toPure_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1559_, 0, v_a_1558_);
v___x_1560_ = lean_apply_2(v_toPure_1557_, lean_box(0), v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object* v_start_1561_, lean_object* v_a_1562_, lean_object* v_toPure_1563_, lean_object* v_stop_1564_){
_start:
{
double v___x_1565_; double v___x_1566_; double v___x_1567_; double v___x_1568_; double v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1565_ = lean_float_of_nat(v_start_1561_);
v___x_1566_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1567_ = lean_float_div(v___x_1565_, v___x_1566_);
v___x_1568_ = lean_float_of_nat(v_stop_1564_);
v___x_1569_ = lean_float_div(v___x_1568_, v___x_1566_);
v___x_1570_ = lean_box_float(v___x_1567_);
v___x_1571_ = lean_box_float(v___x_1569_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v_a_1562_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = lean_apply_2(v_toPure_1563_, lean_box(0), v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object* v_start_1575_, lean_object* v_toPure_1576_, lean_object* v_toBind_1577_, lean_object* v___x_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___f_1580_; lean_object* v___x_1581_; 
v___f_1580_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1580_, 0, v_start_1575_);
lean_closure_set(v___f_1580_, 1, v_a_1579_);
lean_closure_set(v___f_1580_, 2, v_toPure_1576_);
v___x_1581_ = lean_apply_4(v_toBind_1577_, lean_box(0), lean_box(0), v___x_1578_, v___f_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object* v_toPure_1582_, lean_object* v_toBind_1583_, lean_object* v___x_1584_, lean_object* v___x_1585_, lean_object* v_start_1586_){
_start:
{
lean_object* v___f_1587_; lean_object* v___x_1588_; 
lean_inc(v_toBind_1583_);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1587_, 0, v_start_1586_);
lean_closure_set(v___f_1587_, 1, v_toPure_1582_);
lean_closure_set(v___f_1587_, 2, v_toBind_1583_);
lean_closure_set(v___f_1587_, 3, v___x_1584_);
v___x_1588_ = lean_apply_4(v_toBind_1583_, lean_box(0), lean_box(0), v___x_1585_, v___f_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object* v_start_1589_, lean_object* v_a_1590_, lean_object* v_toPure_1591_, lean_object* v_stop_1592_){
_start:
{
double v___x_1593_; double v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1593_ = lean_float_of_nat(v_start_1589_);
v___x_1594_ = lean_float_of_nat(v_stop_1592_);
v___x_1595_ = lean_box_float(v___x_1593_);
v___x_1596_ = lean_box_float(v___x_1594_);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_a_1590_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_apply_2(v_toPure_1591_, lean_box(0), v___x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object* v_start_1600_, lean_object* v_toPure_1601_, lean_object* v_toBind_1602_, lean_object* v___x_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v___f_1605_; lean_object* v___x_1606_; 
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__6), 4, 3);
lean_closure_set(v___f_1605_, 0, v_start_1600_);
lean_closure_set(v___f_1605_, 1, v_a_1604_);
lean_closure_set(v___f_1605_, 2, v_toPure_1601_);
v___x_1606_ = lean_apply_4(v_toBind_1602_, lean_box(0), lean_box(0), v___x_1603_, v___f_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object* v_toPure_1607_, lean_object* v_toBind_1608_, lean_object* v___x_1609_, lean_object* v___x_1610_, lean_object* v_start_1611_){
_start:
{
lean_object* v___f_1612_; lean_object* v___x_1613_; 
lean_inc(v_toBind_1608_);
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1612_, 0, v_start_1611_);
lean_closure_set(v___f_1612_, 1, v_toPure_1607_);
lean_closure_set(v___f_1612_, 2, v_toBind_1608_);
lean_closure_set(v___f_1612_, 3, v___x_1609_);
v___x_1613_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v___x_1610_, v___f_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object* v_always_1614_, lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_cls_1620_, uint8_t v_collapsed_1621_, lean_object* v_tag_1622_, lean_object* v_opts_1623_, uint8_t v_clsEnabled_1624_, lean_object* v_msg_1625_, lean_object* v_toPure_1626_, lean_object* v_toBind_1627_, lean_object* v_k_1628_, lean_object* v___x_1629_, lean_object* v_inst_1630_, lean_object* v_oldTraces_1631_){
_start:
{
lean_object* v_tryCatch_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___f_1635_; lean_object* v___f_1636_; lean_object* v___f_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v_tryCatch_1632_ = lean_ctor_get(v_always_1614_, 1);
lean_inc(v_tryCatch_1632_);
v___x_1633_ = lean_box(v_collapsed_1621_);
v___x_1634_ = lean_box(v_clsEnabled_1624_);
lean_inc_ref(v_opts_1623_);
v___f_1635_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1635_, 0, v_inst_1615_);
lean_closure_set(v___f_1635_, 1, v_inst_1616_);
lean_closure_set(v___f_1635_, 2, v_inst_1617_);
lean_closure_set(v___f_1635_, 3, v_inst_1618_);
lean_closure_set(v___f_1635_, 4, v_always_1614_);
lean_closure_set(v___f_1635_, 5, v_inst_1619_);
lean_closure_set(v___f_1635_, 6, v_cls_1620_);
lean_closure_set(v___f_1635_, 7, v___x_1633_);
lean_closure_set(v___f_1635_, 8, v_tag_1622_);
lean_closure_set(v___f_1635_, 9, v_opts_1623_);
lean_closure_set(v___f_1635_, 10, v___x_1634_);
lean_closure_set(v___f_1635_, 11, v_oldTraces_1631_);
lean_closure_set(v___f_1635_, 12, v_msg_1625_);
lean_inc_n(v_toPure_1626_, 2);
v___f_1636_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1636_, 0, v_toPure_1626_);
v___f_1637_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1637_, 0, v_toPure_1626_);
lean_inc(v_toBind_1627_);
v___x_1638_ = lean_apply_4(v_toBind_1627_, lean_box(0), lean_box(0), v_k_1628_, v___f_1637_);
v___x_1639_ = lean_apply_3(v_tryCatch_1632_, lean_box(0), v___x_1638_, v___f_1636_);
v___x_1640_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1641_ = l_Lean_Option_get___redArg(v___x_1629_, v_opts_1623_, v___x_1640_);
lean_dec_ref(v_opts_1623_);
v___x_1642_ = lean_unbox(v___x_1641_);
lean_dec(v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___f_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1643_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1644_ = lean_apply_2(v_inst_1630_, lean_box(0), v___x_1643_);
lean_inc(v___x_1644_);
lean_inc_n(v_toBind_1627_, 2);
v___f_1645_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1645_, 0, v_toPure_1626_);
lean_closure_set(v___f_1645_, 1, v_toBind_1627_);
lean_closure_set(v___f_1645_, 2, v___x_1644_);
lean_closure_set(v___f_1645_, 3, v___x_1639_);
v___x_1646_ = lean_apply_4(v_toBind_1627_, lean_box(0), lean_box(0), v___x_1644_, v___f_1645_);
v___x_1647_ = lean_apply_4(v_toBind_1627_, lean_box(0), lean_box(0), v___x_1646_, v___f_1635_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___f_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1648_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1649_ = lean_apply_2(v_inst_1630_, lean_box(0), v___x_1648_);
lean_inc(v___x_1649_);
lean_inc_n(v_toBind_1627_, 2);
v___f_1650_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_1650_, 0, v_toPure_1626_);
lean_closure_set(v___f_1650_, 1, v_toBind_1627_);
lean_closure_set(v___f_1650_, 2, v___x_1649_);
lean_closure_set(v___f_1650_, 3, v___x_1639_);
v___x_1651_ = lean_apply_4(v_toBind_1627_, lean_box(0), lean_box(0), v___x_1649_, v___f_1650_);
v___x_1652_ = lean_apply_4(v_toBind_1627_, lean_box(0), lean_box(0), v___x_1651_, v___f_1635_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_always_1653_ = _args[0];
lean_object* v_inst_1654_ = _args[1];
lean_object* v_inst_1655_ = _args[2];
lean_object* v_inst_1656_ = _args[3];
lean_object* v_inst_1657_ = _args[4];
lean_object* v_inst_1658_ = _args[5];
lean_object* v_cls_1659_ = _args[6];
lean_object* v_collapsed_1660_ = _args[7];
lean_object* v_tag_1661_ = _args[8];
lean_object* v_opts_1662_ = _args[9];
lean_object* v_clsEnabled_1663_ = _args[10];
lean_object* v_msg_1664_ = _args[11];
lean_object* v_toPure_1665_ = _args[12];
lean_object* v_toBind_1666_ = _args[13];
lean_object* v_k_1667_ = _args[14];
lean_object* v___x_1668_ = _args[15];
lean_object* v_inst_1669_ = _args[16];
lean_object* v_oldTraces_1670_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_1671_; uint8_t v_clsEnabled_boxed_1672_; lean_object* v_res_1673_; 
v_collapsed_boxed_1671_ = lean_unbox(v_collapsed_1660_);
v_clsEnabled_boxed_1672_ = lean_unbox(v_clsEnabled_1663_);
v_res_1673_ = l_Lean_withTraceNode___redArg___lam__9(v_always_1653_, v_inst_1654_, v_inst_1655_, v_inst_1656_, v_inst_1657_, v_inst_1658_, v_cls_1659_, v_collapsed_boxed_1671_, v_tag_1661_, v_opts_1662_, v_clsEnabled_boxed_1672_, v_msg_1664_, v_toPure_1665_, v_toBind_1666_, v_k_1667_, v___x_1668_, v_inst_1669_, v_oldTraces_1670_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object* v_always_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_cls_1680_, uint8_t v_collapsed_1681_, lean_object* v_tag_1682_, lean_object* v_opts_1683_, lean_object* v_msg_1684_, lean_object* v_toPure_1685_, lean_object* v_toBind_1686_, lean_object* v_k_1687_, lean_object* v___x_1688_, lean_object* v_inst_1689_, uint8_t v_clsEnabled_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___f_1693_; 
v___x_1691_ = lean_box(v_collapsed_1681_);
v___x_1692_ = lean_box(v_clsEnabled_1690_);
lean_inc_ref(v___x_1688_);
lean_inc(v_k_1687_);
lean_inc(v_toBind_1686_);
lean_inc_ref(v_opts_1683_);
lean_inc_ref(v_inst_1676_);
lean_inc_ref(v_inst_1675_);
v___f_1693_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__9___boxed), 18, 17);
lean_closure_set(v___f_1693_, 0, v_always_1674_);
lean_closure_set(v___f_1693_, 1, v_inst_1675_);
lean_closure_set(v___f_1693_, 2, v_inst_1676_);
lean_closure_set(v___f_1693_, 3, v_inst_1677_);
lean_closure_set(v___f_1693_, 4, v_inst_1678_);
lean_closure_set(v___f_1693_, 5, v_inst_1679_);
lean_closure_set(v___f_1693_, 6, v_cls_1680_);
lean_closure_set(v___f_1693_, 7, v___x_1691_);
lean_closure_set(v___f_1693_, 8, v_tag_1682_);
lean_closure_set(v___f_1693_, 9, v_opts_1683_);
lean_closure_set(v___f_1693_, 10, v___x_1692_);
lean_closure_set(v___f_1693_, 11, v_msg_1684_);
lean_closure_set(v___f_1693_, 12, v_toPure_1685_);
lean_closure_set(v___f_1693_, 13, v_toBind_1686_);
lean_closure_set(v___f_1693_, 14, v_k_1687_);
lean_closure_set(v___f_1693_, 15, v___x_1688_);
lean_closure_set(v___f_1693_, 16, v_inst_1689_);
if (v_clsEnabled_1690_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1697_ = l_Lean_trace_profiler;
v___x_1698_ = l_Lean_Option_get___redArg(v___x_1688_, v_opts_1683_, v___x_1697_);
lean_dec_ref(v_opts_1683_);
v___x_1699_ = lean_unbox(v___x_1698_);
lean_dec(v___x_1698_);
if (v___x_1699_ == 0)
{
lean_dec_ref(v___f_1693_);
lean_dec(v_toBind_1686_);
lean_dec_ref(v_inst_1676_);
lean_dec_ref(v_inst_1675_);
return v_k_1687_;
}
else
{
lean_dec(v_k_1687_);
goto v___jp_1694_;
}
}
else
{
lean_dec_ref(v___x_1688_);
lean_dec(v_k_1687_);
lean_dec_ref(v_opts_1683_);
goto v___jp_1694_;
}
v___jp_1694_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1675_, v_inst_1676_);
v___x_1696_ = lean_apply_4(v_toBind_1686_, lean_box(0), lean_box(0), v___x_1695_, v___f_1693_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_1700_ = _args[0];
lean_object* v_inst_1701_ = _args[1];
lean_object* v_inst_1702_ = _args[2];
lean_object* v_inst_1703_ = _args[3];
lean_object* v_inst_1704_ = _args[4];
lean_object* v_inst_1705_ = _args[5];
lean_object* v_cls_1706_ = _args[6];
lean_object* v_collapsed_1707_ = _args[7];
lean_object* v_tag_1708_ = _args[8];
lean_object* v_opts_1709_ = _args[9];
lean_object* v_msg_1710_ = _args[10];
lean_object* v_toPure_1711_ = _args[11];
lean_object* v_toBind_1712_ = _args[12];
lean_object* v_k_1713_ = _args[13];
lean_object* v___x_1714_ = _args[14];
lean_object* v_inst_1715_ = _args[15];
lean_object* v_clsEnabled_1716_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1717_; uint8_t v_clsEnabled_boxed_1718_; lean_object* v_res_1719_; 
v_collapsed_boxed_1717_ = lean_unbox(v_collapsed_1707_);
v_clsEnabled_boxed_1718_ = lean_unbox(v_clsEnabled_1716_);
v_res_1719_ = l_Lean_withTraceNode___redArg___lam__10(v_always_1700_, v_inst_1701_, v_inst_1702_, v_inst_1703_, v_inst_1704_, v_inst_1705_, v_cls_1706_, v_collapsed_boxed_1717_, v_tag_1708_, v_opts_1709_, v_msg_1710_, v_toPure_1711_, v_toBind_1712_, v_k_1713_, v___x_1714_, v_inst_1715_, v_clsEnabled_boxed_1718_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13(lean_object* v_k_1720_, lean_object* v_inst_1721_, lean_object* v_toApplicative_1722_, lean_object* v_always_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_cls_1728_, uint8_t v_collapsed_1729_, lean_object* v_tag_1730_, lean_object* v_msg_1731_, lean_object* v_toBind_1732_, lean_object* v___x_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_opts_1736_){
_start:
{
uint8_t v_hasTrace_1737_; 
v_hasTrace_1737_ = lean_ctor_get_uint8(v_opts_1736_, sizeof(void*)*1);
if (v_hasTrace_1737_ == 0)
{
lean_dec_ref(v_opts_1736_);
lean_dec(v_inst_1735_);
lean_dec(v_inst_1734_);
lean_dec_ref(v___x_1733_);
lean_dec(v_toBind_1732_);
lean_dec(v_msg_1731_);
lean_dec_ref(v_tag_1730_);
lean_dec(v_cls_1728_);
lean_dec_ref(v_inst_1727_);
lean_dec(v_inst_1726_);
lean_dec_ref(v_inst_1725_);
lean_dec_ref(v_inst_1724_);
lean_dec_ref(v_always_1723_);
lean_dec_ref(v_toApplicative_1722_);
lean_dec_ref(v_inst_1721_);
return v_k_1720_;
}
else
{
lean_object* v_getInheritedTraceOptions_1738_; lean_object* v_toPure_1739_; lean_object* v___x_1740_; lean_object* v___f_1741_; lean_object* v___f_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_getInheritedTraceOptions_1738_ = lean_ctor_get(v_inst_1721_, 2);
lean_inc(v_getInheritedTraceOptions_1738_);
v_toPure_1739_ = lean_ctor_get(v_toApplicative_1722_, 1);
lean_inc_n(v_toPure_1739_, 2);
lean_dec_ref(v_toApplicative_1722_);
v___x_1740_ = lean_box(v_collapsed_1729_);
lean_inc_n(v_toBind_1732_, 3);
lean_inc(v_cls_1728_);
v___f_1741_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__10___boxed), 17, 16);
lean_closure_set(v___f_1741_, 0, v_always_1723_);
lean_closure_set(v___f_1741_, 1, v_inst_1724_);
lean_closure_set(v___f_1741_, 2, v_inst_1721_);
lean_closure_set(v___f_1741_, 3, v_inst_1725_);
lean_closure_set(v___f_1741_, 4, v_inst_1726_);
lean_closure_set(v___f_1741_, 5, v_inst_1727_);
lean_closure_set(v___f_1741_, 6, v_cls_1728_);
lean_closure_set(v___f_1741_, 7, v___x_1740_);
lean_closure_set(v___f_1741_, 8, v_tag_1730_);
lean_closure_set(v___f_1741_, 9, v_opts_1736_);
lean_closure_set(v___f_1741_, 10, v_msg_1731_);
lean_closure_set(v___f_1741_, 11, v_toPure_1739_);
lean_closure_set(v___f_1741_, 12, v_toBind_1732_);
lean_closure_set(v___f_1741_, 13, v_k_1720_);
lean_closure_set(v___f_1741_, 14, v___x_1733_);
lean_closure_set(v___f_1741_, 15, v_inst_1734_);
v___f_1742_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1742_, 0, v_toPure_1739_);
lean_closure_set(v___f_1742_, 1, v_cls_1728_);
lean_closure_set(v___f_1742_, 2, v_toBind_1732_);
lean_closure_set(v___f_1742_, 3, v_inst_1735_);
v___x_1743_ = lean_apply_4(v_toBind_1732_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1738_, v___f_1742_);
v___x_1744_ = lean_apply_4(v_toBind_1732_, lean_box(0), lean_box(0), v___x_1743_, v___f_1741_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_k_1745_ = _args[0];
lean_object* v_inst_1746_ = _args[1];
lean_object* v_toApplicative_1747_ = _args[2];
lean_object* v_always_1748_ = _args[3];
lean_object* v_inst_1749_ = _args[4];
lean_object* v_inst_1750_ = _args[5];
lean_object* v_inst_1751_ = _args[6];
lean_object* v_inst_1752_ = _args[7];
lean_object* v_cls_1753_ = _args[8];
lean_object* v_collapsed_1754_ = _args[9];
lean_object* v_tag_1755_ = _args[10];
lean_object* v_msg_1756_ = _args[11];
lean_object* v_toBind_1757_ = _args[12];
lean_object* v___x_1758_ = _args[13];
lean_object* v_inst_1759_ = _args[14];
lean_object* v_inst_1760_ = _args[15];
lean_object* v_opts_1761_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1762_; lean_object* v_res_1763_; 
v_collapsed_boxed_1762_ = lean_unbox(v_collapsed_1754_);
v_res_1763_ = l_Lean_withTraceNode___redArg___lam__13(v_k_1745_, v_inst_1746_, v_toApplicative_1747_, v_always_1748_, v_inst_1749_, v_inst_1750_, v_inst_1751_, v_inst_1752_, v_cls_1753_, v_collapsed_boxed_1762_, v_tag_1755_, v_msg_1756_, v_toBind_1757_, v___x_1758_, v_inst_1759_, v_inst_1760_, v_opts_1761_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg(lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_always_1769_, lean_object* v_inst_1770_, lean_object* v_inst_1771_, lean_object* v_cls_1772_, lean_object* v_msg_1773_, lean_object* v_k_1774_, uint8_t v_collapsed_1775_, lean_object* v_tag_1776_){
_start:
{
lean_object* v___x_1777_; lean_object* v_toApplicative_1778_; lean_object* v_toBind_1779_; lean_object* v___x_1780_; lean_object* v___f_1781_; lean_object* v___x_1782_; 
v___x_1777_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1778_ = lean_ctor_get(v_inst_1764_, 0);
lean_inc_ref(v_toApplicative_1778_);
v_toBind_1779_ = lean_ctor_get(v_inst_1764_, 1);
lean_inc_n(v_toBind_1779_, 2);
v___x_1780_ = lean_box(v_collapsed_1775_);
lean_inc(v_inst_1768_);
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 17, 16);
lean_closure_set(v___f_1781_, 0, v_k_1774_);
lean_closure_set(v___f_1781_, 1, v_inst_1765_);
lean_closure_set(v___f_1781_, 2, v_toApplicative_1778_);
lean_closure_set(v___f_1781_, 3, v_always_1769_);
lean_closure_set(v___f_1781_, 4, v_inst_1764_);
lean_closure_set(v___f_1781_, 5, v_inst_1766_);
lean_closure_set(v___f_1781_, 6, v_inst_1767_);
lean_closure_set(v___f_1781_, 7, v_inst_1771_);
lean_closure_set(v___f_1781_, 8, v_cls_1772_);
lean_closure_set(v___f_1781_, 9, v___x_1780_);
lean_closure_set(v___f_1781_, 10, v_tag_1776_);
lean_closure_set(v___f_1781_, 11, v_msg_1773_);
lean_closure_set(v___f_1781_, 12, v_toBind_1779_);
lean_closure_set(v___f_1781_, 13, v___x_1777_);
lean_closure_set(v___f_1781_, 14, v_inst_1770_);
lean_closure_set(v___f_1781_, 15, v_inst_1768_);
v___x_1782_ = lean_apply_4(v_toBind_1779_, lean_box(0), lean_box(0), v_inst_1768_, v___f_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_inst_1787_, lean_object* v_always_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_cls_1791_, lean_object* v_msg_1792_, lean_object* v_k_1793_, lean_object* v_collapsed_1794_, lean_object* v_tag_1795_){
_start:
{
uint8_t v_collapsed_boxed_1796_; lean_object* v_res_1797_; 
v_collapsed_boxed_1796_ = lean_unbox(v_collapsed_1794_);
v_res_1797_ = l_Lean_withTraceNode___redArg(v_inst_1783_, v_inst_1784_, v_inst_1785_, v_inst_1786_, v_inst_1787_, v_always_1788_, v_inst_1789_, v_inst_1790_, v_cls_1791_, v_msg_1792_, v_k_1793_, v_collapsed_boxed_1796_, v_tag_1795_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode(lean_object* v_00_u03b1_1798_, lean_object* v_m_1799_, lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_inst_1804_, lean_object* v_00_u03b5_1805_, lean_object* v_always_1806_, lean_object* v_inst_1807_, lean_object* v_inst_1808_, lean_object* v_cls_1809_, lean_object* v_msg_1810_, lean_object* v_k_1811_, uint8_t v_collapsed_1812_, lean_object* v_tag_1813_){
_start:
{
lean_object* v___x_1814_; lean_object* v_toApplicative_1815_; lean_object* v_toBind_1816_; lean_object* v___x_1817_; lean_object* v___f_1818_; lean_object* v___x_1819_; 
v___x_1814_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1815_ = lean_ctor_get(v_inst_1800_, 0);
lean_inc_ref(v_toApplicative_1815_);
v_toBind_1816_ = lean_ctor_get(v_inst_1800_, 1);
lean_inc_n(v_toBind_1816_, 2);
v___x_1817_ = lean_box(v_collapsed_1812_);
lean_inc(v_inst_1804_);
v___f_1818_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__13___boxed), 17, 16);
lean_closure_set(v___f_1818_, 0, v_k_1811_);
lean_closure_set(v___f_1818_, 1, v_inst_1801_);
lean_closure_set(v___f_1818_, 2, v_toApplicative_1815_);
lean_closure_set(v___f_1818_, 3, v_always_1806_);
lean_closure_set(v___f_1818_, 4, v_inst_1800_);
lean_closure_set(v___f_1818_, 5, v_inst_1802_);
lean_closure_set(v___f_1818_, 6, v_inst_1803_);
lean_closure_set(v___f_1818_, 7, v_inst_1808_);
lean_closure_set(v___f_1818_, 8, v_cls_1809_);
lean_closure_set(v___f_1818_, 9, v___x_1817_);
lean_closure_set(v___f_1818_, 10, v_tag_1813_);
lean_closure_set(v___f_1818_, 11, v_msg_1810_);
lean_closure_set(v___f_1818_, 12, v_toBind_1816_);
lean_closure_set(v___f_1818_, 13, v___x_1814_);
lean_closure_set(v___f_1818_, 14, v_inst_1807_);
lean_closure_set(v___f_1818_, 15, v_inst_1804_);
v___x_1819_ = lean_apply_4(v_toBind_1816_, lean_box(0), lean_box(0), v_inst_1804_, v___f_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object* v_00_u03b1_1820_, lean_object* v_m_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_00_u03b5_1827_, lean_object* v_always_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_cls_1831_, lean_object* v_msg_1832_, lean_object* v_k_1833_, lean_object* v_collapsed_1834_, lean_object* v_tag_1835_){
_start:
{
uint8_t v_collapsed_boxed_1836_; lean_object* v_res_1837_; 
v_collapsed_boxed_1836_ = lean_unbox(v_collapsed_1834_);
v_res_1837_ = l_Lean_withTraceNode(v_00_u03b1_1820_, v_m_1821_, v_inst_1822_, v_inst_1823_, v_inst_1824_, v_inst_1825_, v_inst_1826_, v_00_u03b5_1827_, v_always_1828_, v_inst_1829_, v_inst_1830_, v_cls_1831_, v_msg_1832_, v_k_1833_, v_collapsed_boxed_1836_, v_tag_1835_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object* v_self_1838_){
_start:
{
lean_object* v_fst_1839_; 
v_fst_1839_ = lean_ctor_get(v_self_1838_, 0);
lean_inc(v_fst_1839_);
return v_fst_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object* v_self_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_1840_);
lean_dec_ref(v_self_1840_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object* v_toPure_1842_, lean_object* v_x_1843_){
_start:
{
if (lean_obj_tag(v_x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_a_1844_ = lean_ctor_get(v_x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v_x_1843_, 1);
v___x_1845_ = l_Lean_Exception_toMessageData(v_a_1844_);
v___x_1846_ = lean_apply_2(v_toPure_1842_, lean_box(0), v___x_1845_);
return v___x_1846_;
}
else
{
lean_object* v_a_1847_; lean_object* v_snd_1848_; lean_object* v___x_1849_; 
v_a_1847_ = lean_ctor_get(v_x_1843_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v_x_1843_, 1);
v_snd_1848_ = lean_ctor_get(v_a_1847_, 1);
lean_inc(v_snd_1848_);
lean_dec(v_a_1847_);
v___x_1849_ = lean_apply_2(v_toPure_1842_, lean_box(0), v_snd_1848_);
return v___x_1849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object* v_toPure_1850_, lean_object* v_ex_1851_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v_ex_1851_);
v___x_1853_ = lean_apply_2(v_toPure_1850_, lean_box(0), v___x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object* v_toPure_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_a_1855_);
v___x_1857_ = lean_apply_2(v_toPure_1854_, lean_box(0), v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_inst_1861_, lean_object* v_inst_1862_, lean_object* v___f_1863_, lean_object* v_cls_1864_, uint8_t v_collapsed_1865_, lean_object* v_tag_1866_, lean_object* v_opts_1867_, uint8_t v_clsEnabled_1868_, lean_object* v_oldTraces_1869_, lean_object* v_msg_1870_, lean_object* v_resStartStop_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1858_, v_inst_1859_, v_inst_1860_, v_inst_1861_, v_inst_1862_, v___f_1863_, v_cls_1864_, v_collapsed_1865_, v_tag_1866_, v_opts_1867_, v_clsEnabled_1868_, v_oldTraces_1869_, v_msg_1870_, v_resStartStop_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3___boxed(lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v___f_1878_, lean_object* v_cls_1879_, lean_object* v_collapsed_1880_, lean_object* v_tag_1881_, lean_object* v_opts_1882_, lean_object* v_clsEnabled_1883_, lean_object* v_oldTraces_1884_, lean_object* v_msg_1885_, lean_object* v_resStartStop_1886_){
_start:
{
uint8_t v_collapsed_boxed_1887_; uint8_t v_clsEnabled_boxed_1888_; lean_object* v_res_1889_; 
v_collapsed_boxed_1887_ = lean_unbox(v_collapsed_1880_);
v_clsEnabled_boxed_1888_ = lean_unbox(v_clsEnabled_1883_);
v_res_1889_ = l_Lean_withTraceNode_x27___redArg___lam__3(v_inst_1873_, v_inst_1874_, v_inst_1875_, v_inst_1876_, v_inst_1877_, v___f_1878_, v_cls_1879_, v_collapsed_boxed_1887_, v_tag_1881_, v_opts_1882_, v_clsEnabled_boxed_1888_, v_oldTraces_1884_, v_msg_1885_, v_resStartStop_1886_);
lean_dec_ref(v_opts_1882_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object* v_start_1890_, lean_object* v_a_1891_, lean_object* v_toPure_1892_, lean_object* v_stop_1893_){
_start:
{
double v___x_1894_; double v___x_1895_; double v___x_1896_; double v___x_1897_; double v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1894_ = lean_float_of_nat(v_start_1890_);
v___x_1895_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1896_ = lean_float_div(v___x_1894_, v___x_1895_);
v___x_1897_ = lean_float_of_nat(v_stop_1893_);
v___x_1898_ = lean_float_div(v___x_1897_, v___x_1895_);
v___x_1899_ = lean_box_float(v___x_1896_);
v___x_1900_ = lean_box_float(v___x_1898_);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v_a_1891_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = lean_apply_2(v_toPure_1892_, lean_box(0), v___x_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object* v_start_1904_, lean_object* v_toPure_1905_, lean_object* v_toBind_1906_, lean_object* v___x_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___f_1909_; lean_object* v___x_1910_; 
v___f_1909_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__5), 4, 3);
lean_closure_set(v___f_1909_, 0, v_start_1904_);
lean_closure_set(v___f_1909_, 1, v_a_1908_);
lean_closure_set(v___f_1909_, 2, v_toPure_1905_);
v___x_1910_ = lean_apply_4(v_toBind_1906_, lean_box(0), lean_box(0), v___x_1907_, v___f_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object* v_toPure_1911_, lean_object* v_toBind_1912_, lean_object* v___x_1913_, lean_object* v___x_1914_, lean_object* v_start_1915_){
_start:
{
lean_object* v___f_1916_; lean_object* v___x_1917_; 
lean_inc(v_toBind_1912_);
v___f_1916_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__6), 5, 4);
lean_closure_set(v___f_1916_, 0, v_start_1915_);
lean_closure_set(v___f_1916_, 1, v_toPure_1911_);
lean_closure_set(v___f_1916_, 2, v_toBind_1912_);
lean_closure_set(v___f_1916_, 3, v___x_1913_);
v___x_1917_ = lean_apply_4(v_toBind_1912_, lean_box(0), lean_box(0), v___x_1914_, v___f_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object* v_start_1918_, lean_object* v_a_1919_, lean_object* v_toPure_1920_, lean_object* v_stop_1921_){
_start:
{
double v___x_1922_; double v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1922_ = lean_float_of_nat(v_start_1918_);
v___x_1923_ = lean_float_of_nat(v_stop_1921_);
v___x_1924_ = lean_box_float(v___x_1922_);
v___x_1925_ = lean_box_float(v___x_1923_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v_a_1919_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_apply_2(v_toPure_1920_, lean_box(0), v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object* v_start_1929_, lean_object* v_toPure_1930_, lean_object* v_toBind_1931_, lean_object* v___x_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v___f_1934_; lean_object* v___x_1935_; 
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__8), 4, 3);
lean_closure_set(v___f_1934_, 0, v_start_1929_);
lean_closure_set(v___f_1934_, 1, v_a_1933_);
lean_closure_set(v___f_1934_, 2, v_toPure_1930_);
v___x_1935_ = lean_apply_4(v_toBind_1931_, lean_box(0), lean_box(0), v___x_1932_, v___f_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object* v_toPure_1936_, lean_object* v_toBind_1937_, lean_object* v___x_1938_, lean_object* v___x_1939_, lean_object* v_start_1940_){
_start:
{
lean_object* v___f_1941_; lean_object* v___x_1942_; 
lean_inc(v_toBind_1937_);
v___f_1941_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__9), 5, 4);
lean_closure_set(v___f_1941_, 0, v_start_1940_);
lean_closure_set(v___f_1941_, 1, v_toPure_1936_);
lean_closure_set(v___f_1941_, 2, v_toBind_1937_);
lean_closure_set(v___f_1941_, 3, v___x_1938_);
v___x_1942_ = lean_apply_4(v_toBind_1937_, lean_box(0), lean_box(0), v___x_1939_, v___f_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_inst_1945_, lean_object* v_inst_1946_, lean_object* v_inst_1947_, lean_object* v___f_1948_, lean_object* v_cls_1949_, uint8_t v_collapsed_1950_, lean_object* v_tag_1951_, lean_object* v_opts_1952_, uint8_t v_clsEnabled_1953_, lean_object* v_msg_1954_, lean_object* v_toBind_1955_, lean_object* v_k_1956_, lean_object* v___f_1957_, lean_object* v___f_1958_, lean_object* v___x_1959_, lean_object* v_inst_1960_, lean_object* v_toPure_1961_, lean_object* v_oldTraces_1962_){
_start:
{
lean_object* v_tryCatch_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___f_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_tryCatch_1963_ = lean_ctor_get(v_inst_1943_, 1);
lean_inc(v_tryCatch_1963_);
v___x_1964_ = lean_box(v_collapsed_1950_);
v___x_1965_ = lean_box(v_clsEnabled_1953_);
lean_inc_ref(v_opts_1952_);
v___f_1966_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3___boxed), 14, 13);
lean_closure_set(v___f_1966_, 0, v_inst_1944_);
lean_closure_set(v___f_1966_, 1, v_inst_1945_);
lean_closure_set(v___f_1966_, 2, v_inst_1946_);
lean_closure_set(v___f_1966_, 3, v_inst_1947_);
lean_closure_set(v___f_1966_, 4, v_inst_1943_);
lean_closure_set(v___f_1966_, 5, v___f_1948_);
lean_closure_set(v___f_1966_, 6, v_cls_1949_);
lean_closure_set(v___f_1966_, 7, v___x_1964_);
lean_closure_set(v___f_1966_, 8, v_tag_1951_);
lean_closure_set(v___f_1966_, 9, v_opts_1952_);
lean_closure_set(v___f_1966_, 10, v___x_1965_);
lean_closure_set(v___f_1966_, 11, v_oldTraces_1962_);
lean_closure_set(v___f_1966_, 12, v_msg_1954_);
lean_inc(v_toBind_1955_);
v___x_1967_ = lean_apply_4(v_toBind_1955_, lean_box(0), lean_box(0), v_k_1956_, v___f_1957_);
v___x_1968_ = lean_apply_3(v_tryCatch_1963_, lean_box(0), v___x_1967_, v___f_1958_);
v___x_1969_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1970_ = l_Lean_Option_get___redArg(v___x_1959_, v_opts_1952_, v___x_1969_);
lean_dec_ref(v_opts_1952_);
v___x_1971_ = lean_unbox(v___x_1970_);
lean_dec(v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___f_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1972_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1973_ = lean_apply_2(v_inst_1960_, lean_box(0), v___x_1972_);
lean_inc(v___x_1973_);
lean_inc_n(v_toBind_1955_, 2);
v___f_1974_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1974_, 0, v_toPure_1961_);
lean_closure_set(v___f_1974_, 1, v_toBind_1955_);
lean_closure_set(v___f_1974_, 2, v___x_1973_);
lean_closure_set(v___f_1974_, 3, v___x_1968_);
v___x_1975_ = lean_apply_4(v_toBind_1955_, lean_box(0), lean_box(0), v___x_1973_, v___f_1974_);
v___x_1976_ = lean_apply_4(v_toBind_1955_, lean_box(0), lean_box(0), v___x_1975_, v___f_1966_);
return v___x_1976_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___f_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1977_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1978_ = lean_apply_2(v_inst_1960_, lean_box(0), v___x_1977_);
lean_inc(v___x_1978_);
lean_inc_n(v_toBind_1955_, 2);
v___f_1979_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__10), 5, 4);
lean_closure_set(v___f_1979_, 0, v_toPure_1961_);
lean_closure_set(v___f_1979_, 1, v_toBind_1955_);
lean_closure_set(v___f_1979_, 2, v___x_1978_);
lean_closure_set(v___f_1979_, 3, v___x_1968_);
v___x_1980_ = lean_apply_4(v_toBind_1955_, lean_box(0), lean_box(0), v___x_1978_, v___f_1979_);
v___x_1981_ = lean_apply_4(v_toBind_1955_, lean_box(0), lean_box(0), v___x_1980_, v___f_1966_);
return v___x_1981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_1982_ = _args[0];
lean_object* v_inst_1983_ = _args[1];
lean_object* v_inst_1984_ = _args[2];
lean_object* v_inst_1985_ = _args[3];
lean_object* v_inst_1986_ = _args[4];
lean_object* v___f_1987_ = _args[5];
lean_object* v_cls_1988_ = _args[6];
lean_object* v_collapsed_1989_ = _args[7];
lean_object* v_tag_1990_ = _args[8];
lean_object* v_opts_1991_ = _args[9];
lean_object* v_clsEnabled_1992_ = _args[10];
lean_object* v_msg_1993_ = _args[11];
lean_object* v_toBind_1994_ = _args[12];
lean_object* v_k_1995_ = _args[13];
lean_object* v___f_1996_ = _args[14];
lean_object* v___f_1997_ = _args[15];
lean_object* v___x_1998_ = _args[16];
lean_object* v_inst_1999_ = _args[17];
lean_object* v_toPure_2000_ = _args[18];
lean_object* v_oldTraces_2001_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_2002_; uint8_t v_clsEnabled_boxed_2003_; lean_object* v_res_2004_; 
v_collapsed_boxed_2002_ = lean_unbox(v_collapsed_1989_);
v_clsEnabled_boxed_2003_ = lean_unbox(v_clsEnabled_1992_);
v_res_2004_ = l_Lean_withTraceNode_x27___redArg___lam__11(v_inst_1982_, v_inst_1983_, v_inst_1984_, v_inst_1985_, v_inst_1986_, v___f_1987_, v_cls_1988_, v_collapsed_boxed_2002_, v_tag_1990_, v_opts_1991_, v_clsEnabled_boxed_2003_, v_msg_1993_, v_toBind_1994_, v_k_1995_, v___f_1996_, v___f_1997_, v___x_1998_, v_inst_1999_, v_toPure_2000_, v_oldTraces_2001_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object* v_inst_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_inst_2009_, lean_object* v___f_2010_, lean_object* v_cls_2011_, uint8_t v_collapsed_2012_, lean_object* v_tag_2013_, lean_object* v_opts_2014_, lean_object* v_msg_2015_, lean_object* v_toBind_2016_, lean_object* v_k_2017_, lean_object* v___f_2018_, lean_object* v___f_2019_, lean_object* v___x_2020_, lean_object* v_inst_2021_, lean_object* v_toPure_2022_, uint8_t v_clsEnabled_2023_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___f_2026_; 
v___x_2024_ = lean_box(v_collapsed_2012_);
v___x_2025_ = lean_box(v_clsEnabled_2023_);
lean_inc_ref(v___x_2020_);
lean_inc(v_k_2017_);
lean_inc(v_toBind_2016_);
lean_inc_ref(v_opts_2014_);
lean_inc_ref(v_inst_2007_);
lean_inc_ref(v_inst_2006_);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__11___boxed), 20, 19);
lean_closure_set(v___f_2026_, 0, v_inst_2005_);
lean_closure_set(v___f_2026_, 1, v_inst_2006_);
lean_closure_set(v___f_2026_, 2, v_inst_2007_);
lean_closure_set(v___f_2026_, 3, v_inst_2008_);
lean_closure_set(v___f_2026_, 4, v_inst_2009_);
lean_closure_set(v___f_2026_, 5, v___f_2010_);
lean_closure_set(v___f_2026_, 6, v_cls_2011_);
lean_closure_set(v___f_2026_, 7, v___x_2024_);
lean_closure_set(v___f_2026_, 8, v_tag_2013_);
lean_closure_set(v___f_2026_, 9, v_opts_2014_);
lean_closure_set(v___f_2026_, 10, v___x_2025_);
lean_closure_set(v___f_2026_, 11, v_msg_2015_);
lean_closure_set(v___f_2026_, 12, v_toBind_2016_);
lean_closure_set(v___f_2026_, 13, v_k_2017_);
lean_closure_set(v___f_2026_, 14, v___f_2018_);
lean_closure_set(v___f_2026_, 15, v___f_2019_);
lean_closure_set(v___f_2026_, 16, v___x_2020_);
lean_closure_set(v___f_2026_, 17, v_inst_2021_);
lean_closure_set(v___f_2026_, 18, v_toPure_2022_);
if (v_clsEnabled_2023_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2030_ = l_Lean_trace_profiler;
v___x_2031_ = l_Lean_Option_get___redArg(v___x_2020_, v_opts_2014_, v___x_2030_);
lean_dec_ref(v_opts_2014_);
v___x_2032_ = lean_unbox(v___x_2031_);
lean_dec(v___x_2031_);
if (v___x_2032_ == 0)
{
lean_dec_ref(v___f_2026_);
lean_dec(v_toBind_2016_);
lean_dec_ref(v_inst_2007_);
lean_dec_ref(v_inst_2006_);
return v_k_2017_;
}
else
{
lean_dec(v_k_2017_);
goto v___jp_2027_;
}
}
else
{
lean_dec_ref(v___x_2020_);
lean_dec(v_k_2017_);
lean_dec_ref(v_opts_2014_);
goto v___jp_2027_;
}
v___jp_2027_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_2006_, v_inst_2007_);
v___x_2029_ = lean_apply_4(v_toBind_2016_, lean_box(0), lean_box(0), v___x_2028_, v___f_2026_);
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_inst_2033_ = _args[0];
lean_object* v_inst_2034_ = _args[1];
lean_object* v_inst_2035_ = _args[2];
lean_object* v_inst_2036_ = _args[3];
lean_object* v_inst_2037_ = _args[4];
lean_object* v___f_2038_ = _args[5];
lean_object* v_cls_2039_ = _args[6];
lean_object* v_collapsed_2040_ = _args[7];
lean_object* v_tag_2041_ = _args[8];
lean_object* v_opts_2042_ = _args[9];
lean_object* v_msg_2043_ = _args[10];
lean_object* v_toBind_2044_ = _args[11];
lean_object* v_k_2045_ = _args[12];
lean_object* v___f_2046_ = _args[13];
lean_object* v___f_2047_ = _args[14];
lean_object* v___x_2048_ = _args[15];
lean_object* v_inst_2049_ = _args[16];
lean_object* v_toPure_2050_ = _args[17];
lean_object* v_clsEnabled_2051_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_2052_; uint8_t v_clsEnabled_boxed_2053_; lean_object* v_res_2054_; 
v_collapsed_boxed_2052_ = lean_unbox(v_collapsed_2040_);
v_clsEnabled_boxed_2053_ = lean_unbox(v_clsEnabled_2051_);
v_res_2054_ = l_Lean_withTraceNode_x27___redArg___lam__12(v_inst_2033_, v_inst_2034_, v_inst_2035_, v_inst_2036_, v_inst_2037_, v___f_2038_, v_cls_2039_, v_collapsed_boxed_2052_, v_tag_2041_, v_opts_2042_, v_msg_2043_, v_toBind_2044_, v_k_2045_, v___f_2046_, v___f_2047_, v___x_2048_, v_inst_2049_, v_toPure_2050_, v_clsEnabled_boxed_2053_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object* v_k_2055_, lean_object* v_inst_2056_, lean_object* v_inst_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_inst_2060_, lean_object* v___f_2061_, lean_object* v_cls_2062_, uint8_t v_collapsed_2063_, lean_object* v_tag_2064_, lean_object* v_msg_2065_, lean_object* v_toBind_2066_, lean_object* v___f_2067_, lean_object* v___f_2068_, lean_object* v___x_2069_, lean_object* v_inst_2070_, lean_object* v_toPure_2071_, lean_object* v___f_2072_, lean_object* v_opts_2073_){
_start:
{
uint8_t v_hasTrace_2074_; 
v_hasTrace_2074_ = lean_ctor_get_uint8(v_opts_2073_, sizeof(void*)*1);
if (v_hasTrace_2074_ == 0)
{
lean_dec_ref(v_opts_2073_);
lean_dec(v___f_2072_);
lean_dec(v_toPure_2071_);
lean_dec(v_inst_2070_);
lean_dec_ref(v___x_2069_);
lean_dec(v___f_2068_);
lean_dec(v___f_2067_);
lean_dec(v_toBind_2066_);
lean_dec(v_msg_2065_);
lean_dec_ref(v_tag_2064_);
lean_dec(v_cls_2062_);
lean_dec_ref(v___f_2061_);
lean_dec(v_inst_2060_);
lean_dec_ref(v_inst_2059_);
lean_dec_ref(v_inst_2058_);
lean_dec_ref(v_inst_2057_);
lean_dec_ref(v_inst_2056_);
return v_k_2055_;
}
else
{
lean_object* v_getInheritedTraceOptions_2075_; lean_object* v___x_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_getInheritedTraceOptions_2075_ = lean_ctor_get(v_inst_2056_, 2);
lean_inc(v_getInheritedTraceOptions_2075_);
v___x_2076_ = lean_box(v_collapsed_2063_);
lean_inc_n(v_toBind_2066_, 2);
v___f_2077_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__12___boxed), 19, 18);
lean_closure_set(v___f_2077_, 0, v_inst_2057_);
lean_closure_set(v___f_2077_, 1, v_inst_2058_);
lean_closure_set(v___f_2077_, 2, v_inst_2056_);
lean_closure_set(v___f_2077_, 3, v_inst_2059_);
lean_closure_set(v___f_2077_, 4, v_inst_2060_);
lean_closure_set(v___f_2077_, 5, v___f_2061_);
lean_closure_set(v___f_2077_, 6, v_cls_2062_);
lean_closure_set(v___f_2077_, 7, v___x_2076_);
lean_closure_set(v___f_2077_, 8, v_tag_2064_);
lean_closure_set(v___f_2077_, 9, v_opts_2073_);
lean_closure_set(v___f_2077_, 10, v_msg_2065_);
lean_closure_set(v___f_2077_, 11, v_toBind_2066_);
lean_closure_set(v___f_2077_, 12, v_k_2055_);
lean_closure_set(v___f_2077_, 13, v___f_2067_);
lean_closure_set(v___f_2077_, 14, v___f_2068_);
lean_closure_set(v___f_2077_, 15, v___x_2069_);
lean_closure_set(v___f_2077_, 16, v_inst_2070_);
lean_closure_set(v___f_2077_, 17, v_toPure_2071_);
v___x_2078_ = lean_apply_4(v_toBind_2066_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2075_, v___f_2072_);
v___x_2079_ = lean_apply_4(v_toBind_2066_, lean_box(0), lean_box(0), v___x_2078_, v___f_2077_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_k_2080_ = _args[0];
lean_object* v_inst_2081_ = _args[1];
lean_object* v_inst_2082_ = _args[2];
lean_object* v_inst_2083_ = _args[3];
lean_object* v_inst_2084_ = _args[4];
lean_object* v_inst_2085_ = _args[5];
lean_object* v___f_2086_ = _args[6];
lean_object* v_cls_2087_ = _args[7];
lean_object* v_collapsed_2088_ = _args[8];
lean_object* v_tag_2089_ = _args[9];
lean_object* v_msg_2090_ = _args[10];
lean_object* v_toBind_2091_ = _args[11];
lean_object* v___f_2092_ = _args[12];
lean_object* v___f_2093_ = _args[13];
lean_object* v___x_2094_ = _args[14];
lean_object* v_inst_2095_ = _args[15];
lean_object* v_toPure_2096_ = _args[16];
lean_object* v___f_2097_ = _args[17];
lean_object* v_opts_2098_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_2099_; lean_object* v_res_2100_; 
v_collapsed_boxed_2099_ = lean_unbox(v_collapsed_2088_);
v_res_2100_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_k_2080_, v_inst_2081_, v_inst_2082_, v_inst_2083_, v_inst_2084_, v_inst_2085_, v___f_2086_, v_cls_2087_, v_collapsed_boxed_2099_, v_tag_2089_, v_msg_2090_, v_toBind_2091_, v___f_2092_, v___f_2093_, v___x_2094_, v_inst_2095_, v_toPure_2096_, v___f_2097_, v_opts_2098_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg(lean_object* v_inst_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_inst_2108_, lean_object* v_cls_2109_, lean_object* v_k_2110_, uint8_t v_collapsed_2111_, lean_object* v_tag_2112_){
_start:
{
lean_object* v_toApplicative_2113_; lean_object* v_toFunctor_2114_; lean_object* v_toBind_2115_; lean_object* v_toPure_2116_; lean_object* v_map_2117_; lean_object* v___f_2118_; lean_object* v_msg_2119_; lean_object* v___f_2120_; lean_object* v___f_2121_; lean_object* v___f_2122_; lean_object* v___f_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___f_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_toApplicative_2113_ = lean_ctor_get(v_inst_2102_, 0);
v_toFunctor_2114_ = lean_ctor_get(v_toApplicative_2113_, 0);
v_toBind_2115_ = lean_ctor_get(v_inst_2102_, 1);
lean_inc_n(v_toBind_2115_, 3);
v_toPure_2116_ = lean_ctor_get(v_toApplicative_2113_, 1);
lean_inc_n(v_toPure_2116_, 5);
v_map_2117_ = lean_ctor_get(v_toFunctor_2114_, 0);
lean_inc(v_map_2117_);
v___f_2118_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2119_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2119_, 0, v_toPure_2116_);
lean_inc(v_inst_2106_);
lean_inc(v_cls_2109_);
v___f_2120_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2120_, 0, v_toPure_2116_);
lean_closure_set(v___f_2120_, 1, v_cls_2109_);
lean_closure_set(v___f_2120_, 2, v_toBind_2115_);
lean_closure_set(v___f_2120_, 3, v_inst_2106_);
v___f_2121_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2121_, 0, v_toPure_2116_);
v___f_2122_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2122_, 0, v_toPure_2116_);
v___f_2123_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2124_ = l_Lean_KVMap_instValueBool;
v___x_2125_ = lean_box(v_collapsed_2111_);
v___f_2126_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 19, 18);
lean_closure_set(v___f_2126_, 0, v_k_2110_);
lean_closure_set(v___f_2126_, 1, v_inst_2103_);
lean_closure_set(v___f_2126_, 2, v_inst_2107_);
lean_closure_set(v___f_2126_, 3, v_inst_2102_);
lean_closure_set(v___f_2126_, 4, v_inst_2104_);
lean_closure_set(v___f_2126_, 5, v_inst_2105_);
lean_closure_set(v___f_2126_, 6, v___f_2123_);
lean_closure_set(v___f_2126_, 7, v_cls_2109_);
lean_closure_set(v___f_2126_, 8, v___x_2125_);
lean_closure_set(v___f_2126_, 9, v_tag_2112_);
lean_closure_set(v___f_2126_, 10, v_msg_2119_);
lean_closure_set(v___f_2126_, 11, v_toBind_2115_);
lean_closure_set(v___f_2126_, 12, v___f_2122_);
lean_closure_set(v___f_2126_, 13, v___f_2121_);
lean_closure_set(v___f_2126_, 14, v___x_2124_);
lean_closure_set(v___f_2126_, 15, v_inst_2108_);
lean_closure_set(v___f_2126_, 16, v_toPure_2116_);
lean_closure_set(v___f_2126_, 17, v___f_2120_);
v___x_2127_ = lean_apply_4(v_toBind_2115_, lean_box(0), lean_box(0), v_inst_2106_, v___f_2126_);
v___x_2128_ = lean_apply_4(v_map_2117_, lean_box(0), lean_box(0), v___f_2118_, v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_inst_2135_, lean_object* v_cls_2136_, lean_object* v_k_2137_, lean_object* v_collapsed_2138_, lean_object* v_tag_2139_){
_start:
{
uint8_t v_collapsed_boxed_2140_; lean_object* v_res_2141_; 
v_collapsed_boxed_2140_ = lean_unbox(v_collapsed_2138_);
v_res_2141_ = l_Lean_withTraceNode_x27___redArg(v_inst_2129_, v_inst_2130_, v_inst_2131_, v_inst_2132_, v_inst_2133_, v_inst_2134_, v_inst_2135_, v_cls_2136_, v_k_2137_, v_collapsed_boxed_2140_, v_tag_2139_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27(lean_object* v_00_u03b1_2142_, lean_object* v_m_2143_, lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_inst_2150_, lean_object* v_cls_2151_, lean_object* v_k_2152_, uint8_t v_collapsed_2153_, lean_object* v_tag_2154_){
_start:
{
lean_object* v_toApplicative_2155_; lean_object* v_toFunctor_2156_; lean_object* v_toBind_2157_; lean_object* v_toPure_2158_; lean_object* v_map_2159_; lean_object* v___f_2160_; lean_object* v_msg_2161_; lean_object* v___f_2162_; lean_object* v___f_2163_; lean_object* v___f_2164_; lean_object* v___f_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___f_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_toApplicative_2155_ = lean_ctor_get(v_inst_2144_, 0);
v_toFunctor_2156_ = lean_ctor_get(v_toApplicative_2155_, 0);
v_toBind_2157_ = lean_ctor_get(v_inst_2144_, 1);
lean_inc_n(v_toBind_2157_, 3);
v_toPure_2158_ = lean_ctor_get(v_toApplicative_2155_, 1);
lean_inc_n(v_toPure_2158_, 5);
v_map_2159_ = lean_ctor_get(v_toFunctor_2156_, 0);
lean_inc(v_map_2159_);
v___f_2160_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v_msg_2161_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v_msg_2161_, 0, v_toPure_2158_);
lean_inc(v_inst_2148_);
lean_inc(v_cls_2151_);
v___f_2162_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2162_, 0, v_toPure_2158_);
lean_closure_set(v___f_2162_, 1, v_cls_2151_);
lean_closure_set(v___f_2162_, 2, v_toBind_2157_);
lean_closure_set(v___f_2162_, 3, v_inst_2148_);
v___f_2163_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2163_, 0, v_toPure_2158_);
v___f_2164_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2164_, 0, v_toPure_2158_);
v___f_2165_ = ((lean_object*)(l_Lean_instExceptToTraceResult___closed__0));
v___x_2166_ = l_Lean_KVMap_instValueBool;
v___x_2167_ = lean_box(v_collapsed_2153_);
v___f_2168_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 19, 18);
lean_closure_set(v___f_2168_, 0, v_k_2152_);
lean_closure_set(v___f_2168_, 1, v_inst_2145_);
lean_closure_set(v___f_2168_, 2, v_inst_2149_);
lean_closure_set(v___f_2168_, 3, v_inst_2144_);
lean_closure_set(v___f_2168_, 4, v_inst_2146_);
lean_closure_set(v___f_2168_, 5, v_inst_2147_);
lean_closure_set(v___f_2168_, 6, v___f_2165_);
lean_closure_set(v___f_2168_, 7, v_cls_2151_);
lean_closure_set(v___f_2168_, 8, v___x_2167_);
lean_closure_set(v___f_2168_, 9, v_tag_2154_);
lean_closure_set(v___f_2168_, 10, v_msg_2161_);
lean_closure_set(v___f_2168_, 11, v_toBind_2157_);
lean_closure_set(v___f_2168_, 12, v___f_2164_);
lean_closure_set(v___f_2168_, 13, v___f_2163_);
lean_closure_set(v___f_2168_, 14, v___x_2166_);
lean_closure_set(v___f_2168_, 15, v_inst_2150_);
lean_closure_set(v___f_2168_, 16, v_toPure_2158_);
lean_closure_set(v___f_2168_, 17, v___f_2162_);
v___x_2169_ = lean_apply_4(v_toBind_2157_, lean_box(0), lean_box(0), v_inst_2148_, v___f_2168_);
v___x_2170_ = lean_apply_4(v_map_2159_, lean_box(0), lean_box(0), v___f_2160_, v___x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object* v_00_u03b1_2171_, lean_object* v_m_2172_, lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_inst_2179_, lean_object* v_cls_2180_, lean_object* v_k_2181_, lean_object* v_collapsed_2182_, lean_object* v_tag_2183_){
_start:
{
uint8_t v_collapsed_boxed_2184_; lean_object* v_res_2185_; 
v_collapsed_boxed_2184_ = lean_unbox(v_collapsed_2182_);
v_res_2185_ = l_Lean_withTraceNode_x27(v_00_u03b1_2171_, v_m_2172_, v_inst_2173_, v_inst_2174_, v_inst_2175_, v_inst_2176_, v_inst_2177_, v_inst_2178_, v_inst_2179_, v_cls_2180_, v_k_2181_, v_collapsed_boxed_2184_, v_tag_2183_);
return v_res_2185_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__4(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__3));
v___x_2195_ = l_Lean_mkAtom(v___x_2194_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__5(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__4, &l_Lean_registerTraceClass___auto__1___closed__4_once, _init_l_Lean_registerTraceClass___auto__1___closed__4);
v___x_2197_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2198_ = lean_array_push(v___x_2197_, v___x_2196_);
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__6(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2199_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__5, &l_Lean_registerTraceClass___auto__1___closed__5_once, _init_l_Lean_registerTraceClass___auto__1___closed__5);
v___x_2200_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__2));
v___x_2201_ = lean_box(2);
v___x_2202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___x_2200_);
lean_ctor_set(v___x_2202_, 2, v___x_2199_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__7(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__6, &l_Lean_registerTraceClass___auto__1___closed__6_once, _init_l_Lean_registerTraceClass___auto__1___closed__6);
v___x_2204_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_2205_ = lean_array_push(v___x_2204_, v___x_2203_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__7, &l_Lean_registerTraceClass___auto__1___closed__7_once, _init_l_Lean_registerTraceClass___auto__1___closed__7);
v___x_2207_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_2208_ = lean_box(2);
v___x_2209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2207_);
lean_ctor_set(v___x_2209_, 2, v___x_2206_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__8, &l_Lean_registerTraceClass___auto__1___closed__8_once, _init_l_Lean_registerTraceClass___auto__1___closed__8);
v___x_2211_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2212_ = lean_array_push(v___x_2211_, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2213_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__9, &l_Lean_registerTraceClass___auto__1___closed__9_once, _init_l_Lean_registerTraceClass___auto__1___closed__9);
v___x_2214_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2215_ = lean_box(2);
v___x_2216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v___x_2214_);
lean_ctor_set(v___x_2216_, 2, v___x_2213_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__11(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__10, &l_Lean_registerTraceClass___auto__1___closed__10_once, _init_l_Lean_registerTraceClass___auto__1___closed__10);
v___x_2218_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2219_ = lean_array_push(v___x_2218_, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2220_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__11, &l_Lean_registerTraceClass___auto__1___closed__11_once, _init_l_Lean_registerTraceClass___auto__1___closed__11);
v___x_2221_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_2222_ = lean_box(2);
v___x_2223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v___x_2221_);
lean_ctor_set(v___x_2223_, 2, v___x_2220_);
return v___x_2223_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__12, &l_Lean_registerTraceClass___auto__1___closed__12_once, _init_l_Lean_registerTraceClass___auto__1___closed__12);
v___x_2225_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2226_ = lean_array_push(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2227_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__13, &l_Lean_registerTraceClass___auto__1___closed__13_once, _init_l_Lean_registerTraceClass___auto__1___closed__13);
v___x_2228_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_2229_ = lean_box(2);
v___x_2230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v___x_2228_);
lean_ctor_set(v___x_2230_, 2, v___x_2227_);
return v___x_2230_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1(void){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__14, &l_Lean_registerTraceClass___auto__1___closed__14_once, _init_l_Lean_registerTraceClass___auto__1___closed__14);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2232_, lean_object* v_x_2233_){
_start:
{
if (lean_obj_tag(v_x_2233_) == 0)
{
return v_x_2232_;
}
else
{
lean_object* v_key_2234_; lean_object* v_value_2235_; lean_object* v_tail_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2262_; 
v_key_2234_ = lean_ctor_get(v_x_2233_, 0);
v_value_2235_ = lean_ctor_get(v_x_2233_, 1);
v_tail_2236_ = lean_ctor_get(v_x_2233_, 2);
v_isSharedCheck_2262_ = !lean_is_exclusive(v_x_2233_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2238_ = v_x_2233_;
v_isShared_2239_ = v_isSharedCheck_2262_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_tail_2236_);
lean_inc(v_value_2235_);
lean_inc(v_key_2234_);
lean_dec(v_x_2233_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2262_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; uint64_t v___y_2242_; 
v___x_2240_ = lean_array_get_size(v_x_2232_);
if (lean_obj_tag(v_key_2234_) == 0)
{
uint64_t v___x_2260_; 
v___x_2260_ = 1723ULL;
v___y_2242_ = v___x_2260_;
goto v___jp_2241_;
}
else
{
uint64_t v_hash_2261_; 
v_hash_2261_ = lean_ctor_get_uint64(v_key_2234_, sizeof(void*)*2);
v___y_2242_ = v_hash_2261_;
goto v___jp_2241_;
}
v___jp_2241_:
{
uint64_t v___x_2243_; uint64_t v___x_2244_; uint64_t v_fold_2245_; uint64_t v___x_2246_; uint64_t v___x_2247_; uint64_t v___x_2248_; size_t v___x_2249_; size_t v___x_2250_; size_t v___x_2251_; size_t v___x_2252_; size_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2243_ = 32ULL;
v___x_2244_ = lean_uint64_shift_right(v___y_2242_, v___x_2243_);
v_fold_2245_ = lean_uint64_xor(v___y_2242_, v___x_2244_);
v___x_2246_ = 16ULL;
v___x_2247_ = lean_uint64_shift_right(v_fold_2245_, v___x_2246_);
v___x_2248_ = lean_uint64_xor(v_fold_2245_, v___x_2247_);
v___x_2249_ = lean_uint64_to_usize(v___x_2248_);
v___x_2250_ = lean_usize_of_nat(v___x_2240_);
v___x_2251_ = ((size_t)1ULL);
v___x_2252_ = lean_usize_sub(v___x_2250_, v___x_2251_);
v___x_2253_ = lean_usize_land(v___x_2249_, v___x_2252_);
v___x_2254_ = lean_array_uget_borrowed(v_x_2232_, v___x_2253_);
lean_inc(v___x_2254_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 2, v___x_2254_);
v___x_2256_ = v___x_2238_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_key_2234_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_value_2235_);
lean_ctor_set(v_reuseFailAlloc_2259_, 2, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_array_uset(v_x_2232_, v___x_2253_, v___x_2256_);
v_x_2232_ = v___x_2257_;
v_x_2233_ = v_tail_2236_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object* v_i_2263_, lean_object* v_source_2264_, lean_object* v_target_2265_){
_start:
{
lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = lean_array_get_size(v_source_2264_);
v___x_2267_ = lean_nat_dec_lt(v_i_2263_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_dec_ref(v_source_2264_);
lean_dec(v_i_2263_);
return v_target_2265_;
}
else
{
lean_object* v_es_2268_; lean_object* v___x_2269_; lean_object* v_source_2270_; lean_object* v_target_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_es_2268_ = lean_array_fget(v_source_2264_, v_i_2263_);
v___x_2269_ = lean_box(0);
v_source_2270_ = lean_array_fset(v_source_2264_, v_i_2263_, v___x_2269_);
v_target_2271_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_2265_, v_es_2268_);
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_nat_add(v_i_2263_, v___x_2272_);
lean_dec(v_i_2263_);
v_i_2263_ = v___x_2273_;
v_source_2264_ = v_source_2270_;
v_target_2265_ = v_target_2271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object* v_data_2275_){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v_nbuckets_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2276_ = lean_array_get_size(v_data_2275_);
v___x_2277_ = lean_unsigned_to_nat(2u);
v_nbuckets_2278_ = lean_nat_mul(v___x_2276_, v___x_2277_);
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = lean_box(0);
v___x_2281_ = lean_mk_array(v_nbuckets_2278_, v___x_2280_);
v___x_2282_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_2279_, v_data_2275_, v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object* v_m_2283_, lean_object* v_a_2284_, lean_object* v_b_2285_){
_start:
{
lean_object* v_size_2286_; lean_object* v_buckets_2287_; lean_object* v___x_2288_; uint64_t v___y_2290_; 
v_size_2286_ = lean_ctor_get(v_m_2283_, 0);
v_buckets_2287_ = lean_ctor_get(v_m_2283_, 1);
v___x_2288_ = lean_array_get_size(v_buckets_2287_);
if (lean_obj_tag(v_a_2284_) == 0)
{
uint64_t v___x_2327_; 
v___x_2327_ = 1723ULL;
v___y_2290_ = v___x_2327_;
goto v___jp_2289_;
}
else
{
uint64_t v_hash_2328_; 
v_hash_2328_ = lean_ctor_get_uint64(v_a_2284_, sizeof(void*)*2);
v___y_2290_ = v_hash_2328_;
goto v___jp_2289_;
}
v___jp_2289_:
{
uint64_t v___x_2291_; uint64_t v___x_2292_; uint64_t v_fold_2293_; uint64_t v___x_2294_; uint64_t v___x_2295_; uint64_t v___x_2296_; size_t v___x_2297_; size_t v___x_2298_; size_t v___x_2299_; size_t v___x_2300_; size_t v___x_2301_; lean_object* v_bkt_2302_; uint8_t v___x_2303_; 
v___x_2291_ = 32ULL;
v___x_2292_ = lean_uint64_shift_right(v___y_2290_, v___x_2291_);
v_fold_2293_ = lean_uint64_xor(v___y_2290_, v___x_2292_);
v___x_2294_ = 16ULL;
v___x_2295_ = lean_uint64_shift_right(v_fold_2293_, v___x_2294_);
v___x_2296_ = lean_uint64_xor(v_fold_2293_, v___x_2295_);
v___x_2297_ = lean_uint64_to_usize(v___x_2296_);
v___x_2298_ = lean_usize_of_nat(v___x_2288_);
v___x_2299_ = ((size_t)1ULL);
v___x_2300_ = lean_usize_sub(v___x_2298_, v___x_2299_);
v___x_2301_ = lean_usize_land(v___x_2297_, v___x_2300_);
v_bkt_2302_ = lean_array_uget_borrowed(v_buckets_2287_, v___x_2301_);
v___x_2303_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_2284_, v_bkt_2302_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2324_; 
lean_inc_ref(v_buckets_2287_);
lean_inc(v_size_2286_);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_m_2283_);
if (v_isSharedCheck_2324_ == 0)
{
lean_object* v_unused_2325_; lean_object* v_unused_2326_; 
v_unused_2325_ = lean_ctor_get(v_m_2283_, 1);
lean_dec(v_unused_2325_);
v_unused_2326_ = lean_ctor_get(v_m_2283_, 0);
lean_dec(v_unused_2326_);
v___x_2305_ = v_m_2283_;
v_isShared_2306_ = v_isSharedCheck_2324_;
goto v_resetjp_2304_;
}
else
{
lean_dec(v_m_2283_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2324_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; lean_object* v_size_x27_2308_; lean_object* v___x_2309_; lean_object* v_buckets_x27_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2307_ = lean_unsigned_to_nat(1u);
v_size_x27_2308_ = lean_nat_add(v_size_2286_, v___x_2307_);
lean_dec(v_size_2286_);
lean_inc(v_bkt_2302_);
v___x_2309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2309_, 0, v_a_2284_);
lean_ctor_set(v___x_2309_, 1, v_b_2285_);
lean_ctor_set(v___x_2309_, 2, v_bkt_2302_);
v_buckets_x27_2310_ = lean_array_uset(v_buckets_2287_, v___x_2301_, v___x_2309_);
v___x_2311_ = lean_unsigned_to_nat(4u);
v___x_2312_ = lean_nat_mul(v_size_x27_2308_, v___x_2311_);
v___x_2313_ = lean_unsigned_to_nat(3u);
v___x_2314_ = lean_nat_div(v___x_2312_, v___x_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_array_get_size(v_buckets_x27_2310_);
v___x_2316_ = lean_nat_dec_le(v___x_2314_, v___x_2315_);
lean_dec(v___x_2314_);
if (v___x_2316_ == 0)
{
lean_object* v_val_2317_; lean_object* v___x_2319_; 
v_val_2317_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_2310_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 1, v_val_2317_);
lean_ctor_set(v___x_2305_, 0, v_size_x27_2308_);
v___x_2319_ = v___x_2305_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_size_x27_2308_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_val_2317_);
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
lean_object* v___x_2322_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 1, v_buckets_x27_2310_);
lean_ctor_set(v___x_2305_, 0, v_size_x27_2308_);
v___x_2322_ = v___x_2305_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_size_x27_2308_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_buckets_x27_2310_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
else
{
lean_dec(v_b_2285_);
lean_dec(v_a_2284_);
return v_m_2283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass(lean_object* v_traceClassName_2332_, uint8_t v_inherited_2333_, lean_object* v_ref_2334_){
_start:
{
lean_object* v___x_2336_; lean_object* v_optionName_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2336_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v_optionName_2337_ = l_Lean_Name_append(v___x_2336_, v_traceClassName_2332_);
v___x_2338_ = ((lean_object*)(l_Lean_registerTraceClass___closed__0));
v___x_2339_ = ((lean_object*)(l_Lean_registerTraceClass___closed__1));
v___x_2340_ = lean_box(0);
lean_inc_n(v_optionName_2337_, 2);
v___x_2341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2341_, 0, v_optionName_2337_);
lean_ctor_set(v___x_2341_, 1, v_ref_2334_);
lean_ctor_set(v___x_2341_, 2, v___x_2338_);
lean_ctor_set(v___x_2341_, 3, v___x_2339_);
lean_ctor_set(v___x_2341_, 4, v___x_2340_);
v___x_2342_ = lean_register_option(v_optionName_2337_, v___x_2341_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2358_; 
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v___x_2342_, 0);
lean_dec(v_unused_2359_);
v___x_2344_ = v___x_2342_;
v_isShared_2345_ = v_isSharedCheck_2358_;
goto v_resetjp_2343_;
}
else
{
lean_dec(v___x_2342_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2358_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
if (v_inherited_2333_ == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2348_; 
lean_dec(v_optionName_2337_);
v___x_2346_ = lean_box(0);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2346_);
v___x_2348_ = v___x_2344_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2350_ = l_Lean_inheritedTraceOptions;
v___x_2351_ = lean_st_ref_take(v___x_2350_);
v___x_2352_ = lean_box(0);
v___x_2353_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2351_, v_optionName_2337_, v___x_2352_);
v___x_2354_ = lean_st_ref_put(v___x_2350_, v___x_2353_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2354_);
v___x_2356_ = v___x_2344_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_dec(v_optionName_2337_);
return v___x_2342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object* v_traceClassName_2360_, lean_object* v_inherited_2361_, lean_object* v_ref_2362_, lean_object* v_a_2363_){
_start:
{
uint8_t v_inherited_boxed_2364_; lean_object* v_res_2365_; 
v_inherited_boxed_2364_ = lean_unbox(v_inherited_2361_);
v_res_2365_ = l_Lean_registerTraceClass(v_traceClassName_2360_, v_inherited_boxed_2364_, v_ref_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(lean_object* v_00_u03b2_2366_, lean_object* v_m_2367_, lean_object* v_a_2368_, lean_object* v_b_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v_m_2367_, v_a_2368_, v_b_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object* v_00_u03b2_2371_, lean_object* v_data_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_data_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2374_, lean_object* v_i_2375_, lean_object* v_source_2376_, lean_object* v_target_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_i_2375_, v_source_2376_, v_target_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2380_, v_x_2381_);
return v___x_2382_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_2393_ = l_String_toRawSubstring_x27(v___x_2392_);
return v___x_2393_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13));
v___x_2400_ = l_String_toRawSubstring_x27(v___x_2399_);
return v___x_2400_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18));
v___x_2406_ = l_String_toRawSubstring_x27(v___x_2405_);
return v___x_2406_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31(void){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Array_mkArray0(lean_box(0));
return v___x_2434_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40));
v___x_2461_ = l_String_toRawSubstring_x27(v___x_2460_);
return v___x_2461_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57));
v___x_2497_ = l_String_toRawSubstring_x27(v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object* v_id_2519_, lean_object* v_s_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v_msg_2620_; lean_object* v_quotContext_2621_; lean_object* v_currMacroScope_2622_; lean_object* v_ref_2623_; lean_object* v___y_2624_; lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
lean_inc(v_s_2520_);
v___x_2670_ = l_Lean_Syntax_getKind(v_s_2520_);
v___x_2671_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49));
v___x_2672_ = lean_name_eq(v___x_2670_, v___x_2671_);
lean_dec(v___x_2670_);
if (v___x_2672_ == 0)
{
lean_object* v_quotContext_2673_; lean_object* v_currMacroScope_2674_; lean_object* v_ref_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_quotContext_2673_ = lean_ctor_get(v_a_2521_, 1);
v_currMacroScope_2674_ = lean_ctor_get(v_a_2521_, 2);
v_ref_2675_ = lean_ctor_get(v_a_2521_, 5);
v___x_2676_ = l_Lean_SourceInfo_fromRef(v_ref_2675_, v___x_2672_);
v___x_2677_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51));
v___x_2678_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52));
v___x_2679_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
lean_inc_n(v___x_2676_, 8);
v___x_2680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2676_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2682_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2683_ = lean_box(0);
lean_inc_n(v_currMacroScope_2674_, 3);
lean_inc_n(v_quotContext_2673_, 3);
v___x_2684_ = l_Lean_addMacroScope(v_quotContext_2673_, v___x_2683_, v_currMacroScope_2674_);
v___x_2685_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55));
v___x_2686_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2676_);
lean_ctor_set(v___x_2686_, 1, v___x_2682_);
lean_ctor_set(v___x_2686_, 2, v___x_2684_);
lean_ctor_set(v___x_2686_, 3, v___x_2685_);
v___x_2687_ = l_Lean_Syntax_node1(v___x_2676_, v___x_2681_, v___x_2686_);
v___x_2688_ = l_Lean_Syntax_node2(v___x_2676_, v___x_2678_, v___x_2680_, v___x_2687_);
v___x_2689_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56));
v___x_2690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2676_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2692_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58);
v___x_2693_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59));
v___x_2694_ = l_Lean_addMacroScope(v_quotContext_2673_, v___x_2693_, v_currMacroScope_2674_);
v___x_2695_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64));
v___x_2696_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2676_);
lean_ctor_set(v___x_2696_, 1, v___x_2692_);
lean_ctor_set(v___x_2696_, 2, v___x_2694_);
lean_ctor_set(v___x_2696_, 3, v___x_2695_);
v___x_2697_ = l_Lean_Syntax_node1(v___x_2676_, v___x_2691_, v___x_2696_);
v___x_2698_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2676_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = l_Lean_Syntax_node5(v___x_2676_, v___x_2677_, v___x_2688_, v_s_2520_, v___x_2690_, v___x_2697_, v___x_2699_);
v_msg_2620_ = v___x_2700_;
v_quotContext_2621_ = v_quotContext_2673_;
v_currMacroScope_2622_ = v_currMacroScope_2674_;
v_ref_2623_ = v_ref_2675_;
v___y_2624_ = v_a_2522_;
goto v___jp_2619_;
}
else
{
lean_object* v_quotContext_2701_; lean_object* v_currMacroScope_2702_; lean_object* v_ref_2703_; uint8_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_quotContext_2701_ = lean_ctor_get(v_a_2521_, 1);
v_currMacroScope_2702_ = lean_ctor_get(v_a_2521_, 2);
v_ref_2703_ = lean_ctor_get(v_a_2521_, 5);
v___x_2704_ = 0;
v___x_2705_ = l_Lean_SourceInfo_fromRef(v_ref_2703_, v___x_2704_);
v___x_2706_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66));
v___x_2707_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67));
lean_inc(v___x_2705_);
v___x_2708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2705_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = l_Lean_Syntax_node2(v___x_2705_, v___x_2706_, v___x_2708_, v_s_2520_);
lean_inc(v_currMacroScope_2702_);
lean_inc(v_quotContext_2701_);
v_msg_2620_ = v___x_2709_;
v_quotContext_2621_ = v_quotContext_2701_;
v_currMacroScope_2622_ = v_currMacroScope_2702_;
v_ref_2623_ = v_ref_2703_;
v___y_2624_ = v_a_2522_;
goto v___jp_2619_;
}
v___jp_2523_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_inc_n(v___y_2527_, 8);
lean_inc(v___y_2529_);
lean_inc_n(v___y_2545_, 30);
v___x_2548_ = l_Lean_Syntax_node5(v___y_2545_, v___y_2529_, v___y_2526_, v___y_2527_, v___y_2527_, v___y_2546_, v___y_2547_);
lean_inc(v___y_2534_);
v___x_2549_ = l_Lean_Syntax_node1(v___y_2545_, v___y_2534_, v___x_2548_);
lean_inc(v___y_2532_);
v___x_2550_ = l_Lean_Syntax_node4(v___y_2545_, v___y_2532_, v___y_2540_, v___y_2527_, v___y_2533_, v___x_2549_);
lean_inc_n(v___y_2543_, 3);
v___x_2551_ = l_Lean_Syntax_node2(v___y_2545_, v___y_2543_, v___x_2550_, v___y_2527_);
v___x_2552_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0));
lean_inc_ref_n(v___y_2531_, 7);
lean_inc_ref_n(v___y_2544_, 7);
lean_inc_ref_n(v___y_2536_, 10);
v___x_2553_ = l_Lean_Name_mkStr4(v___y_2536_, v___y_2544_, v___y_2531_, v___x_2552_);
v___x_2554_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1));
v___x_2555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___y_2545_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2));
v___x_2557_ = l_Lean_Name_mkStr4(v___y_2536_, v___y_2544_, v___y_2531_, v___x_2556_);
v___x_2558_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3));
v___x_2559_ = l_Lean_Name_mkStr4(v___y_2536_, v___y_2544_, v___y_2531_, v___x_2558_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4));
v___x_2561_ = l_Lean_Name_mkStr4(v___y_2536_, v___y_2544_, v___y_2531_, v___x_2560_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
v___x_2563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___y_2545_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2565_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2566_ = lean_box(0);
lean_inc_n(v___y_2542_, 2);
lean_inc_n(v___y_2530_, 2);
v___x_2567_ = l_Lean_addMacroScope(v___y_2530_, v___x_2566_, v___y_2542_);
v___x_2568_ = l_Lean_Name_mkStr1(v___y_2536_);
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
lean_inc_n(v___y_2541_, 2);
v___x_2570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set(v___x_2570_, 1, v___y_2541_);
v___x_2571_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2571_, 0, v___y_2545_);
lean_ctor_set(v___x_2571_, 1, v___x_2565_);
lean_ctor_set(v___x_2571_, 2, v___x_2567_);
lean_ctor_set(v___x_2571_, 3, v___x_2570_);
v___x_2572_ = l_Lean_Syntax_node1(v___y_2545_, v___x_2564_, v___x_2571_);
v___x_2573_ = l_Lean_Syntax_node2(v___y_2545_, v___x_2561_, v___x_2563_, v___x_2572_);
v___x_2574_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9));
v___x_2575_ = l_Lean_Name_mkStr4(v___y_2536_, v___y_2544_, v___y_2531_, v___x_2574_);
v___x_2576_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10));
v___x_2577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___y_2545_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11));
v___x_2579_ = l_Lean_Name_mkStr4(v___y_2536_, v___y_2544_, v___y_2531_, v___x_2578_);
v___x_2580_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12));
v___x_2581_ = l_Lean_Name_mkStr4(v___y_2536_, v___y_2544_, v___y_2531_, v___x_2580_);
v___x_2582_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14);
v___x_2583_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2584_ = l_Lean_Name_mkStr2(v___y_2536_, v___x_2583_);
lean_inc(v___x_2584_);
v___x_2585_ = l_Lean_addMacroScope(v___y_2530_, v___x_2584_, v___y_2542_);
v___x_2586_ = lean_box(0);
v___x_2587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2584_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___y_2541_);
v___x_2589_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2589_, 0, v___y_2545_);
lean_ctor_set(v___x_2589_, 1, v___x_2582_);
lean_ctor_set(v___x_2589_, 2, v___x_2585_);
lean_ctor_set(v___x_2589_, 3, v___x_2588_);
lean_inc(v___y_2539_);
lean_inc_n(v___y_2535_, 4);
v___x_2590_ = l_Lean_Syntax_node1(v___y_2545_, v___y_2535_, v___y_2539_);
lean_inc(v___x_2581_);
v___x_2591_ = l_Lean_Syntax_node2(v___y_2545_, v___x_2581_, v___x_2589_, v___x_2590_);
lean_inc(v___x_2579_);
v___x_2592_ = l_Lean_Syntax_node1(v___y_2545_, v___x_2579_, v___x_2591_);
v___x_2593_ = l_Lean_Syntax_node2(v___y_2545_, v___x_2575_, v___x_2577_, v___x_2592_);
v___x_2594_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___y_2545_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = l_Lean_Syntax_node3(v___y_2545_, v___x_2559_, v___x_2573_, v___x_2593_, v___x_2595_);
v___x_2597_ = l_Lean_Syntax_node2(v___y_2545_, v___x_2557_, v___y_2527_, v___x_2596_);
v___x_2598_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17));
v___x_2599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___y_2545_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19);
v___x_2601_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20));
v___x_2602_ = l_Lean_Name_mkStr2(v___y_2536_, v___x_2601_);
lean_inc(v___x_2602_);
v___x_2603_ = l_Lean_addMacroScope(v___y_2530_, v___x_2602_, v___y_2542_);
v___x_2604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2586_);
v___x_2605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
lean_ctor_set(v___x_2605_, 1, v___y_2541_);
v___x_2606_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2606_, 0, v___y_2545_);
lean_ctor_set(v___x_2606_, 1, v___x_2600_);
lean_ctor_set(v___x_2606_, 2, v___x_2603_);
lean_ctor_set(v___x_2606_, 3, v___x_2605_);
v___x_2607_ = l_Lean_Syntax_node2(v___y_2545_, v___y_2535_, v___y_2539_, v___y_2537_);
v___x_2608_ = l_Lean_Syntax_node2(v___y_2545_, v___x_2581_, v___x_2606_, v___x_2607_);
v___x_2609_ = l_Lean_Syntax_node1(v___y_2545_, v___x_2579_, v___x_2608_);
v___x_2610_ = l_Lean_Syntax_node2(v___y_2545_, v___y_2543_, v___x_2609_, v___y_2527_);
v___x_2611_ = l_Lean_Syntax_node1(v___y_2545_, v___y_2535_, v___x_2610_);
lean_inc_n(v___y_2525_, 2);
v___x_2612_ = l_Lean_Syntax_node1(v___y_2545_, v___y_2525_, v___x_2611_);
v___x_2613_ = l_Lean_Syntax_node6(v___y_2545_, v___x_2553_, v___x_2555_, v___x_2597_, v___x_2599_, v___x_2612_, v___y_2527_, v___y_2527_);
v___x_2614_ = l_Lean_Syntax_node2(v___y_2545_, v___y_2543_, v___x_2613_, v___y_2527_);
v___x_2615_ = l_Lean_Syntax_node2(v___y_2545_, v___y_2535_, v___x_2551_, v___x_2614_);
v___x_2616_ = l_Lean_Syntax_node1(v___y_2545_, v___y_2525_, v___x_2615_);
lean_inc(v___y_2528_);
v___x_2617_ = l_Lean_Syntax_node2(v___y_2545_, v___y_2528_, v___y_2524_, v___x_2616_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
lean_ctor_set(v___x_2618_, 1, v___y_2538_);
return v___x_2618_;
}
v___jp_2619_:
{
uint8_t v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2625_ = 0;
v___x_2626_ = l_Lean_SourceInfo_fromRef(v_ref_2623_, v___x_2625_);
v___x_2627_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0));
v___x_2628_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1));
v___x_2629_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__0));
v___x_2630_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22));
v___x_2631_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23));
lean_inc_n(v___x_2626_, 7);
v___x_2632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2626_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25));
v___x_2634_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2635_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27));
v___x_2636_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2637_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
v___x_2638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2626_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31);
v___x_2640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2626_);
lean_ctor_set(v___x_2640_, 1, v___x_2634_);
lean_ctor_set(v___x_2640_, 2, v___x_2639_);
v___x_2641_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33));
lean_inc_ref(v___x_2640_);
v___x_2642_ = l_Lean_Syntax_node1(v___x_2626_, v___x_2641_, v___x_2640_);
v___x_2643_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35));
v___x_2644_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37));
v___x_2645_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39));
v___x_2646_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41);
v___x_2647_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42));
lean_inc(v_currMacroScope_2622_);
lean_inc(v_quotContext_2621_);
v___x_2648_ = l_Lean_addMacroScope(v_quotContext_2621_, v___x_2647_, v_currMacroScope_2622_);
v___x_2649_ = lean_box(0);
v___x_2650_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2626_);
lean_ctor_set(v___x_2650_, 1, v___x_2646_);
lean_ctor_set(v___x_2650_, 2, v___x_2648_);
lean_ctor_set(v___x_2650_, 3, v___x_2649_);
lean_inc_ref(v___x_2650_);
v___x_2651_ = l_Lean_Syntax_node1(v___x_2626_, v___x_2645_, v___x_2650_);
v___x_2652_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43));
v___x_2653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2626_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = l_Lean_Syntax_getId(v_id_2519_);
v___x_2655_ = l_Lean_Name_eraseMacroScopes(v___x_2654_);
lean_dec(v___x_2654_);
lean_inc(v___x_2655_);
v___x_2656_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2649_, v___x_2655_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_quoteNameMk(v___x_2655_);
v___y_2524_ = v___x_2632_;
v___y_2525_ = v___x_2633_;
v___y_2526_ = v___x_2651_;
v___y_2527_ = v___x_2640_;
v___y_2528_ = v___x_2630_;
v___y_2529_ = v___x_2644_;
v___y_2530_ = v_quotContext_2621_;
v___y_2531_ = v___x_2629_;
v___y_2532_ = v___x_2636_;
v___y_2533_ = v___x_2642_;
v___y_2534_ = v___x_2643_;
v___y_2535_ = v___x_2634_;
v___y_2536_ = v___x_2627_;
v___y_2537_ = v_msg_2620_;
v___y_2538_ = v___y_2624_;
v___y_2539_ = v___x_2650_;
v___y_2540_ = v___x_2638_;
v___y_2541_ = v___x_2649_;
v___y_2542_ = v_currMacroScope_2622_;
v___y_2543_ = v___x_2635_;
v___y_2544_ = v___x_2628_;
v___y_2545_ = v___x_2626_;
v___y_2546_ = v___x_2653_;
v___y_2547_ = v___x_2657_;
goto v___jp_2523_;
}
else
{
lean_object* v_val_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec(v___x_2655_);
v_val_2658_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_val_2658_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2659_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45));
v___x_2660_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46));
v___x_2661_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47));
v___x_2662_ = lean_string_intercalate(v___x_2661_, v_val_2658_);
v___x_2663_ = lean_string_append(v___x_2660_, v___x_2662_);
lean_dec_ref(v___x_2662_);
v___x_2664_ = lean_box(2);
v___x_2665_ = l_Lean_Syntax_mkNameLit(v___x_2663_, v___x_2664_);
v___x_2666_ = lean_unsigned_to_nat(1u);
v___x_2667_ = lean_mk_empty_array_with_capacity(v___x_2666_);
v___x_2668_ = lean_array_push(v___x_2667_, v___x_2665_);
v___x_2669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2664_);
lean_ctor_set(v___x_2669_, 1, v___x_2659_);
lean_ctor_set(v___x_2669_, 2, v___x_2668_);
v___y_2524_ = v___x_2632_;
v___y_2525_ = v___x_2633_;
v___y_2526_ = v___x_2651_;
v___y_2527_ = v___x_2640_;
v___y_2528_ = v___x_2630_;
v___y_2529_ = v___x_2644_;
v___y_2530_ = v_quotContext_2621_;
v___y_2531_ = v___x_2629_;
v___y_2532_ = v___x_2636_;
v___y_2533_ = v___x_2642_;
v___y_2534_ = v___x_2643_;
v___y_2535_ = v___x_2634_;
v___y_2536_ = v___x_2627_;
v___y_2537_ = v_msg_2620_;
v___y_2538_ = v___y_2624_;
v___y_2539_ = v___x_2650_;
v___y_2540_ = v___x_2638_;
v___y_2541_ = v___x_2649_;
v___y_2542_ = v_currMacroScope_2622_;
v___y_2543_ = v___x_2635_;
v___y_2544_ = v___x_2628_;
v___y_2545_ = v___x_2626_;
v___y_2546_ = v___x_2653_;
v___y_2547_ = v___x_2669_;
goto v___jp_2523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object* v_id_2710_, lean_object* v_s_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v_id_2710_, v_s_2711_, v_a_2712_, v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_id_2710_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object* v_x_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2772_ = ((lean_object*)(l_Lean_doElemTrace_x5b___x5d_____00__closed__1));
lean_inc(v_x_2769_);
v___x_2773_ = l_Lean_Syntax_isOfKind(v_x_2769_, v___x_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_dec(v_x_2769_);
v___x_2774_ = lean_box(1);
v___x_2775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v_a_2771_);
return v___x_2775_;
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v_a_2781_; lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v___x_2776_ = lean_unsigned_to_nat(1u);
v___x_2777_ = l_Lean_Syntax_getArg(v_x_2769_, v___x_2776_);
v___x_2778_ = lean_unsigned_to_nat(3u);
v___x_2779_ = l_Lean_Syntax_getArg(v_x_2769_, v___x_2778_);
lean_dec(v_x_2769_);
v___x_2780_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v___x_2777_, v___x_2779_, v_a_2770_, v_a_2771_);
lean_dec(v___x_2777_);
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_a_2782_ = lean_ctor_get(v___x_2780_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2780_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2781_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object* v_x_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(v_x_2790_, v_a_2791_, v_a_2792_);
lean_dec_ref(v_a_2791_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object* v_inst_2794_, lean_object* v_inst_2795_, lean_object* v_inst_2796_, lean_object* v_inst_2797_, lean_object* v_always_2798_, lean_object* v_inst_2799_, lean_object* v_cls_2800_, uint8_t v_collapsed_2801_, lean_object* v_tag_2802_, lean_object* v_opts_2803_, uint8_t v_clsEnabled_2804_, lean_object* v_oldTraces_2805_, lean_object* v_ref_2806_, lean_object* v_msg_2807_, lean_object* v_resStartStop_2808_){
_start:
{
lean_object* v___x_2809_; lean_object* v_toBind_2810_; lean_object* v___x_2811_; lean_object* v_snd_2812_; lean_object* v_fst_2813_; lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v___f_2816_; lean_object* v___f_2817_; lean_object* v_data_2819_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___y_2834_; double v___y_2839_; uint8_t v___x_2844_; 
v___x_2809_ = l_Lean_KVMap_instValueBool;
v_toBind_2810_ = lean_ctor_get(v_inst_2794_, 1);
lean_inc(v_toBind_2810_);
v___x_2811_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_2798_);
v_snd_2812_ = lean_ctor_get(v_resStartStop_2808_, 1);
lean_inc(v_snd_2812_);
v_fst_2813_ = lean_ctor_get(v_resStartStop_2808_, 0);
lean_inc_n(v_fst_2813_, 2);
lean_dec_ref(v_resStartStop_2808_);
v_fst_2814_ = lean_ctor_get(v_snd_2812_, 0);
lean_inc(v_fst_2814_);
v_snd_2815_ = lean_ctor_get(v_snd_2812_, 1);
lean_inc(v_snd_2815_);
lean_dec(v_snd_2812_);
lean_inc_ref(v_oldTraces_2805_);
v___f_2816_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2816_, 0, v_oldTraces_2805_);
lean_inc_ref(v_inst_2794_);
v___f_2817_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2817_, 0, v_inst_2794_);
lean_closure_set(v___f_2817_, 1, v___x_2811_);
lean_closure_set(v___f_2817_, 2, v_fst_2813_);
v___x_2822_ = l_Lean_trace_profiler;
v___x_2823_ = l_Lean_Option_get___redArg(v___x_2809_, v_opts_2803_, v___x_2822_);
v___x_2844_ = lean_unbox(v___x_2823_);
if (v___x_2844_ == 0)
{
uint8_t v___x_2845_; 
v___x_2845_ = lean_unbox(v___x_2823_);
v___y_2834_ = v___x_2845_;
goto v___jp_2833_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2846_ = l_Lean_KVMap_instValueNat;
v___x_2847_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2848_ = l_Lean_Option_get___redArg(v___x_2809_, v_opts_2803_, v___x_2847_);
v___x_2849_ = lean_unbox(v___x_2848_);
lean_dec(v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; double v___x_2852_; double v___x_2853_; double v___x_2854_; 
v___x_2850_ = l_Lean_trace_profiler_threshold;
v___x_2851_ = l_Lean_Option_get___redArg(v___x_2846_, v_opts_2803_, v___x_2850_);
v___x_2852_ = lean_float_of_nat(v___x_2851_);
v___x_2853_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_2854_ = lean_float_div(v___x_2852_, v___x_2853_);
v___y_2839_ = v___x_2854_;
goto v___jp_2838_;
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; double v___x_2857_; 
v___x_2855_ = l_Lean_trace_profiler_threshold;
v___x_2856_ = l_Lean_Option_get___redArg(v___x_2846_, v_opts_2803_, v___x_2855_);
v___x_2857_ = lean_float_of_nat(v___x_2856_);
v___y_2839_ = v___x_2857_;
goto v___jp_2838_;
}
}
v___jp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_2794_, v_inst_2795_, v_inst_2796_, v_inst_2797_, v_oldTraces_2805_, v_data_2819_, v_ref_2806_, v_msg_2807_);
v___x_2821_ = lean_apply_4(v_toBind_2810_, lean_box(0), lean_box(0), v___x_2820_, v___f_2817_);
return v___x_2821_;
}
v___jp_2824_:
{
lean_object* v_result_2825_; lean_object* v___x_2826_; double v___x_2827_; lean_object* v_data_2828_; uint8_t v___x_2829_; 
v_result_2825_ = lean_apply_1(v_inst_2799_, v_fst_2813_);
v___x_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_result_2825_);
v___x_2827_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_2802_);
lean_inc_ref(v___x_2826_);
lean_inc(v_cls_2800_);
v_data_2828_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2828_, 0, v_cls_2800_);
lean_ctor_set(v_data_2828_, 1, v___x_2826_);
lean_ctor_set(v_data_2828_, 2, v_tag_2802_);
lean_ctor_set_float(v_data_2828_, sizeof(void*)*3, v___x_2827_);
lean_ctor_set_float(v_data_2828_, sizeof(void*)*3 + 8, v___x_2827_);
lean_ctor_set_uint8(v_data_2828_, sizeof(void*)*3 + 16, v_collapsed_2801_);
v___x_2829_ = lean_unbox(v___x_2823_);
lean_dec(v___x_2823_);
if (v___x_2829_ == 0)
{
lean_dec_ref_known(v___x_2826_, 1);
lean_dec(v_snd_2815_);
lean_dec(v_fst_2814_);
lean_dec_ref(v_tag_2802_);
lean_dec(v_cls_2800_);
v_data_2819_ = v_data_2828_;
goto v___jp_2818_;
}
else
{
lean_object* v_data_2830_; double v___x_2831_; double v___x_2832_; 
lean_dec_ref_known(v_data_2828_, 3);
v_data_2830_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2830_, 0, v_cls_2800_);
lean_ctor_set(v_data_2830_, 1, v___x_2826_);
lean_ctor_set(v_data_2830_, 2, v_tag_2802_);
v___x_2831_ = lean_unbox_float(v_fst_2814_);
lean_dec(v_fst_2814_);
lean_ctor_set_float(v_data_2830_, sizeof(void*)*3, v___x_2831_);
v___x_2832_ = lean_unbox_float(v_snd_2815_);
lean_dec(v_snd_2815_);
lean_ctor_set_float(v_data_2830_, sizeof(void*)*3 + 8, v___x_2832_);
lean_ctor_set_uint8(v_data_2830_, sizeof(void*)*3 + 16, v_collapsed_2801_);
v_data_2819_ = v_data_2830_;
goto v___jp_2818_;
}
}
v___jp_2833_:
{
if (v_clsEnabled_2804_ == 0)
{
if (v___y_2834_ == 0)
{
lean_object* v_modifyTraceState_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec(v___x_2823_);
lean_dec(v_snd_2815_);
lean_dec(v_fst_2814_);
lean_dec(v_fst_2813_);
lean_dec_ref(v_msg_2807_);
lean_dec(v_ref_2806_);
lean_dec_ref(v_oldTraces_2805_);
lean_dec_ref(v_tag_2802_);
lean_dec(v_cls_2800_);
lean_dec_ref(v_inst_2799_);
lean_dec(v_inst_2797_);
lean_dec_ref(v_inst_2796_);
lean_dec_ref(v_inst_2794_);
v_modifyTraceState_2835_ = lean_ctor_get(v_inst_2795_, 0);
lean_inc(v_modifyTraceState_2835_);
lean_dec_ref(v_inst_2795_);
v___x_2836_ = lean_apply_1(v_modifyTraceState_2835_, v___f_2816_);
v___x_2837_ = lean_apply_4(v_toBind_2810_, lean_box(0), lean_box(0), v___x_2836_, v___f_2817_);
return v___x_2837_;
}
else
{
lean_dec_ref(v___f_2816_);
goto v___jp_2824_;
}
}
else
{
lean_dec_ref(v___f_2816_);
goto v___jp_2824_;
}
}
v___jp_2838_:
{
double v___x_2840_; double v___x_2841_; double v___x_2842_; uint8_t v___x_2843_; 
v___x_2840_ = lean_unbox_float(v_snd_2815_);
v___x_2841_ = lean_unbox_float(v_fst_2814_);
v___x_2842_ = lean_float_sub(v___x_2840_, v___x_2841_);
v___x_2843_ = lean_float_decLt(v___y_2839_, v___x_2842_);
v___y_2834_ = v___x_2843_;
goto v___jp_2833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object* v_inst_2858_, lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_inst_2861_, lean_object* v_always_2862_, lean_object* v_inst_2863_, lean_object* v_cls_2864_, lean_object* v_collapsed_2865_, lean_object* v_tag_2866_, lean_object* v_opts_2867_, lean_object* v_clsEnabled_2868_, lean_object* v_oldTraces_2869_, lean_object* v_ref_2870_, lean_object* v_msg_2871_, lean_object* v_resStartStop_2872_){
_start:
{
uint8_t v_collapsed_boxed_2873_; uint8_t v_clsEnabled_boxed_2874_; lean_object* v_res_2875_; 
v_collapsed_boxed_2873_ = lean_unbox(v_collapsed_2865_);
v_clsEnabled_boxed_2874_ = lean_unbox(v_clsEnabled_2868_);
v_res_2875_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2858_, v_inst_2859_, v_inst_2860_, v_inst_2861_, v_always_2862_, v_inst_2863_, v_cls_2864_, v_collapsed_boxed_2873_, v_tag_2866_, v_opts_2867_, v_clsEnabled_boxed_2874_, v_oldTraces_2869_, v_ref_2870_, v_msg_2871_, v_resStartStop_2872_);
lean_dec_ref(v_opts_2867_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object* v_00_u03b1_2876_, lean_object* v_m_2877_, lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_00_u03b5_2880_, lean_object* v_inst_2881_, lean_object* v_inst_2882_, lean_object* v_always_2883_, lean_object* v_inst_2884_, lean_object* v_cls_2885_, uint8_t v_collapsed_2886_, lean_object* v_tag_2887_, lean_object* v_opts_2888_, uint8_t v_clsEnabled_2889_, lean_object* v_oldTraces_2890_, lean_object* v_ref_2891_, lean_object* v_msg_2892_, lean_object* v_resStartStop_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2878_, v_inst_2879_, v_inst_2881_, v_inst_2882_, v_always_2883_, v_inst_2884_, v_cls_2885_, v_collapsed_2886_, v_tag_2887_, v_opts_2888_, v_clsEnabled_2889_, v_oldTraces_2890_, v_ref_2891_, v_msg_2892_, v_resStartStop_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_2895_ = _args[0];
lean_object* v_m_2896_ = _args[1];
lean_object* v_inst_2897_ = _args[2];
lean_object* v_inst_2898_ = _args[3];
lean_object* v_00_u03b5_2899_ = _args[4];
lean_object* v_inst_2900_ = _args[5];
lean_object* v_inst_2901_ = _args[6];
lean_object* v_always_2902_ = _args[7];
lean_object* v_inst_2903_ = _args[8];
lean_object* v_cls_2904_ = _args[9];
lean_object* v_collapsed_2905_ = _args[10];
lean_object* v_tag_2906_ = _args[11];
lean_object* v_opts_2907_ = _args[12];
lean_object* v_clsEnabled_2908_ = _args[13];
lean_object* v_oldTraces_2909_ = _args[14];
lean_object* v_ref_2910_ = _args[15];
lean_object* v_msg_2911_ = _args[16];
lean_object* v_resStartStop_2912_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2913_; uint8_t v_clsEnabled_boxed_2914_; lean_object* v_res_2915_; 
v_collapsed_boxed_2913_ = lean_unbox(v_collapsed_2905_);
v_clsEnabled_boxed_2914_ = lean_unbox(v_clsEnabled_2908_);
v_res_2915_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(v_00_u03b1_2895_, v_m_2896_, v_inst_2897_, v_inst_2898_, v_00_u03b5_2899_, v_inst_2900_, v_inst_2901_, v_always_2902_, v_inst_2903_, v_cls_2904_, v_collapsed_boxed_2913_, v_tag_2906_, v_opts_2907_, v_clsEnabled_boxed_2914_, v_oldTraces_2909_, v_ref_2910_, v_msg_2911_, v_resStartStop_2912_);
lean_dec_ref(v_opts_2907_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object* v_inst_2916_, lean_object* v_____do__lift_2917_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = lean_apply_1(v_inst_2916_, v_____do__lift_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object* v_inst_2919_, lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_always_2923_, lean_object* v_inst_2924_, lean_object* v_cls_2925_, uint8_t v_collapsed_2926_, lean_object* v_tag_2927_, lean_object* v_opts_2928_, uint8_t v_clsEnabled_2929_, lean_object* v_oldTraces_2930_, lean_object* v_ref_2931_, lean_object* v_msg_2932_, lean_object* v_resStartStop_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2919_, v_inst_2920_, v_inst_2921_, v_inst_2922_, v_always_2923_, v_inst_2924_, v_cls_2925_, v_collapsed_2926_, v_tag_2927_, v_opts_2928_, v_clsEnabled_2929_, v_oldTraces_2930_, v_ref_2931_, v_msg_2932_, v_resStartStop_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_inst_2938_, lean_object* v_always_2939_, lean_object* v_inst_2940_, lean_object* v_cls_2941_, lean_object* v_collapsed_2942_, lean_object* v_tag_2943_, lean_object* v_opts_2944_, lean_object* v_clsEnabled_2945_, lean_object* v_oldTraces_2946_, lean_object* v_ref_2947_, lean_object* v_msg_2948_, lean_object* v_resStartStop_2949_){
_start:
{
uint8_t v_collapsed_boxed_2950_; uint8_t v_clsEnabled_boxed_2951_; lean_object* v_res_2952_; 
v_collapsed_boxed_2950_ = lean_unbox(v_collapsed_2942_);
v_clsEnabled_boxed_2951_ = lean_unbox(v_clsEnabled_2945_);
v_res_2952_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_2935_, v_inst_2936_, v_inst_2937_, v_inst_2938_, v_always_2939_, v_inst_2940_, v_cls_2941_, v_collapsed_boxed_2950_, v_tag_2943_, v_opts_2944_, v_clsEnabled_boxed_2951_, v_oldTraces_2946_, v_ref_2947_, v_msg_2948_, v_resStartStop_2949_);
lean_dec_ref(v_opts_2944_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object* v_always_2953_, lean_object* v_inst_2954_, lean_object* v_inst_2955_, lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_cls_2959_, uint8_t v_collapsed_2960_, lean_object* v_tag_2961_, lean_object* v_opts_2962_, uint8_t v_clsEnabled_2963_, lean_object* v_oldTraces_2964_, lean_object* v_ref_2965_, lean_object* v_toPure_2966_, lean_object* v_toBind_2967_, lean_object* v_k_2968_, lean_object* v___x_2969_, lean_object* v_inst_2970_, lean_object* v_msg_2971_){
_start:
{
lean_object* v_tryCatch_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___f_2975_; lean_object* v___f_2976_; lean_object* v___f_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; uint8_t v___x_2982_; 
v_tryCatch_2972_ = lean_ctor_get(v_always_2953_, 1);
lean_inc(v_tryCatch_2972_);
v___x_2973_ = lean_box(v_collapsed_2960_);
v___x_2974_ = lean_box(v_clsEnabled_2963_);
lean_inc_ref(v_opts_2962_);
v___f_2975_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__1___boxed), 15, 14);
lean_closure_set(v___f_2975_, 0, v_inst_2954_);
lean_closure_set(v___f_2975_, 1, v_inst_2955_);
lean_closure_set(v___f_2975_, 2, v_inst_2956_);
lean_closure_set(v___f_2975_, 3, v_inst_2957_);
lean_closure_set(v___f_2975_, 4, v_always_2953_);
lean_closure_set(v___f_2975_, 5, v_inst_2958_);
lean_closure_set(v___f_2975_, 6, v_cls_2959_);
lean_closure_set(v___f_2975_, 7, v___x_2973_);
lean_closure_set(v___f_2975_, 8, v_tag_2961_);
lean_closure_set(v___f_2975_, 9, v_opts_2962_);
lean_closure_set(v___f_2975_, 10, v___x_2974_);
lean_closure_set(v___f_2975_, 11, v_oldTraces_2964_);
lean_closure_set(v___f_2975_, 12, v_ref_2965_);
lean_closure_set(v___f_2975_, 13, v_msg_2971_);
lean_inc_n(v_toPure_2966_, 2);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2976_, 0, v_toPure_2966_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2977_, 0, v_toPure_2966_);
lean_inc(v_toBind_2967_);
v___x_2978_ = lean_apply_4(v_toBind_2967_, lean_box(0), lean_box(0), v_k_2968_, v___f_2977_);
v___x_2979_ = lean_apply_3(v_tryCatch_2972_, lean_box(0), v___x_2978_, v___f_2976_);
v___x_2980_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2981_ = l_Lean_Option_get___redArg(v___x_2969_, v_opts_2962_, v___x_2980_);
lean_dec_ref(v_opts_2962_);
v___x_2982_ = lean_unbox(v___x_2981_);
lean_dec(v___x_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___f_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2983_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_2984_ = lean_apply_2(v_inst_2970_, lean_box(0), v___x_2983_);
lean_inc(v___x_2984_);
lean_inc_n(v_toBind_2967_, 2);
v___f_2985_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_2985_, 0, v_toPure_2966_);
lean_closure_set(v___f_2985_, 1, v_toBind_2967_);
lean_closure_set(v___f_2985_, 2, v___x_2984_);
lean_closure_set(v___f_2985_, 3, v___x_2979_);
v___x_2986_ = lean_apply_4(v_toBind_2967_, lean_box(0), lean_box(0), v___x_2984_, v___f_2985_);
v___x_2987_ = lean_apply_4(v_toBind_2967_, lean_box(0), lean_box(0), v___x_2986_, v___f_2975_);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2988_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_2989_ = lean_apply_2(v_inst_2970_, lean_box(0), v___x_2988_);
lean_inc(v___x_2989_);
lean_inc_n(v_toBind_2967_, 2);
v___f_2990_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_2990_, 0, v_toPure_2966_);
lean_closure_set(v___f_2990_, 1, v_toBind_2967_);
lean_closure_set(v___f_2990_, 2, v___x_2989_);
lean_closure_set(v___f_2990_, 3, v___x_2979_);
v___x_2991_ = lean_apply_4(v_toBind_2967_, lean_box(0), lean_box(0), v___x_2989_, v___f_2990_);
v___x_2992_ = lean_apply_4(v_toBind_2967_, lean_box(0), lean_box(0), v___x_2991_, v___f_2975_);
return v___x_2992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_2993_ = _args[0];
lean_object* v_inst_2994_ = _args[1];
lean_object* v_inst_2995_ = _args[2];
lean_object* v_inst_2996_ = _args[3];
lean_object* v_inst_2997_ = _args[4];
lean_object* v_inst_2998_ = _args[5];
lean_object* v_cls_2999_ = _args[6];
lean_object* v_collapsed_3000_ = _args[7];
lean_object* v_tag_3001_ = _args[8];
lean_object* v_opts_3002_ = _args[9];
lean_object* v_clsEnabled_3003_ = _args[10];
lean_object* v_oldTraces_3004_ = _args[11];
lean_object* v_ref_3005_ = _args[12];
lean_object* v_toPure_3006_ = _args[13];
lean_object* v_toBind_3007_ = _args[14];
lean_object* v_k_3008_ = _args[15];
lean_object* v___x_3009_ = _args[16];
lean_object* v_inst_3010_ = _args[17];
lean_object* v_msg_3011_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_3012_; uint8_t v_clsEnabled_boxed_3013_; lean_object* v_res_3014_; 
v_collapsed_boxed_3012_ = lean_unbox(v_collapsed_3000_);
v_clsEnabled_boxed_3013_ = lean_unbox(v_clsEnabled_3003_);
v_res_3014_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_always_2993_, v_inst_2994_, v_inst_2995_, v_inst_2996_, v_inst_2997_, v_inst_2998_, v_cls_2999_, v_collapsed_boxed_3012_, v_tag_3001_, v_opts_3002_, v_clsEnabled_boxed_3013_, v_oldTraces_3004_, v_ref_3005_, v_toPure_3006_, v_toBind_3007_, v_k_3008_, v___x_3009_, v_inst_3010_, v_msg_3011_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object* v_always_3015_, lean_object* v_inst_3016_, lean_object* v_inst_3017_, lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_inst_3020_, lean_object* v_cls_3021_, uint8_t v_collapsed_3022_, lean_object* v_tag_3023_, lean_object* v_opts_3024_, uint8_t v_clsEnabled_3025_, lean_object* v_oldTraces_3026_, lean_object* v_toPure_3027_, lean_object* v_toBind_3028_, lean_object* v_k_3029_, lean_object* v___x_3030_, lean_object* v_inst_3031_, lean_object* v_msg_3032_, lean_object* v___f_3033_, lean_object* v_withRef_3034_, lean_object* v_getRef_3035_, lean_object* v_ref_3036_){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___f_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___f_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3037_ = lean_box(v_collapsed_3022_);
v___x_3038_ = lean_box(v_clsEnabled_3025_);
lean_inc_n(v_toBind_3028_, 3);
lean_inc(v_ref_3036_);
v___f_3039_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__10___boxed), 19, 18);
lean_closure_set(v___f_3039_, 0, v_always_3015_);
lean_closure_set(v___f_3039_, 1, v_inst_3016_);
lean_closure_set(v___f_3039_, 2, v_inst_3017_);
lean_closure_set(v___f_3039_, 3, v_inst_3018_);
lean_closure_set(v___f_3039_, 4, v_inst_3019_);
lean_closure_set(v___f_3039_, 5, v_inst_3020_);
lean_closure_set(v___f_3039_, 6, v_cls_3021_);
lean_closure_set(v___f_3039_, 7, v___x_3037_);
lean_closure_set(v___f_3039_, 8, v_tag_3023_);
lean_closure_set(v___f_3039_, 9, v_opts_3024_);
lean_closure_set(v___f_3039_, 10, v___x_3038_);
lean_closure_set(v___f_3039_, 11, v_oldTraces_3026_);
lean_closure_set(v___f_3039_, 12, v_ref_3036_);
lean_closure_set(v___f_3039_, 13, v_toPure_3027_);
lean_closure_set(v___f_3039_, 14, v_toBind_3028_);
lean_closure_set(v___f_3039_, 15, v_k_3029_);
lean_closure_set(v___f_3039_, 16, v___x_3030_);
lean_closure_set(v___f_3039_, 17, v_inst_3031_);
v___x_3040_ = lean_box(0);
v___x_3041_ = lean_apply_1(v_msg_3032_, v___x_3040_);
v___x_3042_ = lean_apply_4(v_toBind_3028_, lean_box(0), lean_box(0), v___x_3041_, v___f_3033_);
v___f_3043_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3043_, 0, v_ref_3036_);
lean_closure_set(v___f_3043_, 1, v_withRef_3034_);
lean_closure_set(v___f_3043_, 2, v___x_3042_);
v___x_3044_ = lean_apply_4(v_toBind_3028_, lean_box(0), lean_box(0), v_getRef_3035_, v___f_3043_);
v___x_3045_ = lean_apply_4(v_toBind_3028_, lean_box(0), lean_box(0), v___x_3044_, v___f_3039_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_3046_ = _args[0];
lean_object* v_inst_3047_ = _args[1];
lean_object* v_inst_3048_ = _args[2];
lean_object* v_inst_3049_ = _args[3];
lean_object* v_inst_3050_ = _args[4];
lean_object* v_inst_3051_ = _args[5];
lean_object* v_cls_3052_ = _args[6];
lean_object* v_collapsed_3053_ = _args[7];
lean_object* v_tag_3054_ = _args[8];
lean_object* v_opts_3055_ = _args[9];
lean_object* v_clsEnabled_3056_ = _args[10];
lean_object* v_oldTraces_3057_ = _args[11];
lean_object* v_toPure_3058_ = _args[12];
lean_object* v_toBind_3059_ = _args[13];
lean_object* v_k_3060_ = _args[14];
lean_object* v___x_3061_ = _args[15];
lean_object* v_inst_3062_ = _args[16];
lean_object* v_msg_3063_ = _args[17];
lean_object* v___f_3064_ = _args[18];
lean_object* v_withRef_3065_ = _args[19];
lean_object* v_getRef_3066_ = _args[20];
lean_object* v_ref_3067_ = _args[21];
_start:
{
uint8_t v_collapsed_boxed_3068_; uint8_t v_clsEnabled_boxed_3069_; lean_object* v_res_3070_; 
v_collapsed_boxed_3068_ = lean_unbox(v_collapsed_3053_);
v_clsEnabled_boxed_3069_ = lean_unbox(v_clsEnabled_3056_);
v_res_3070_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_always_3046_, v_inst_3047_, v_inst_3048_, v_inst_3049_, v_inst_3050_, v_inst_3051_, v_cls_3052_, v_collapsed_boxed_3068_, v_tag_3054_, v_opts_3055_, v_clsEnabled_boxed_3069_, v_oldTraces_3057_, v_toPure_3058_, v_toBind_3059_, v_k_3060_, v___x_3061_, v_inst_3062_, v_msg_3063_, v___f_3064_, v_withRef_3065_, v_getRef_3066_, v_ref_3067_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object* v_inst_3071_, lean_object* v_always_3072_, lean_object* v_inst_3073_, lean_object* v_inst_3074_, lean_object* v_inst_3075_, lean_object* v_inst_3076_, lean_object* v_cls_3077_, uint8_t v_collapsed_3078_, lean_object* v_tag_3079_, lean_object* v_opts_3080_, uint8_t v_clsEnabled_3081_, lean_object* v_toPure_3082_, lean_object* v_toBind_3083_, lean_object* v_k_3084_, lean_object* v___x_3085_, lean_object* v_inst_3086_, lean_object* v_msg_3087_, lean_object* v___f_3088_, lean_object* v_oldTraces_3089_){
_start:
{
lean_object* v_getRef_3090_; lean_object* v_withRef_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___f_3094_; lean_object* v___x_3095_; 
v_getRef_3090_ = lean_ctor_get(v_inst_3071_, 0);
lean_inc_n(v_getRef_3090_, 2);
v_withRef_3091_ = lean_ctor_get(v_inst_3071_, 1);
lean_inc(v_withRef_3091_);
v___x_3092_ = lean_box(v_collapsed_3078_);
v___x_3093_ = lean_box(v_clsEnabled_3081_);
lean_inc(v_toBind_3083_);
v___f_3094_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__3___boxed), 22, 21);
lean_closure_set(v___f_3094_, 0, v_always_3072_);
lean_closure_set(v___f_3094_, 1, v_inst_3073_);
lean_closure_set(v___f_3094_, 2, v_inst_3074_);
lean_closure_set(v___f_3094_, 3, v_inst_3071_);
lean_closure_set(v___f_3094_, 4, v_inst_3075_);
lean_closure_set(v___f_3094_, 5, v_inst_3076_);
lean_closure_set(v___f_3094_, 6, v_cls_3077_);
lean_closure_set(v___f_3094_, 7, v___x_3092_);
lean_closure_set(v___f_3094_, 8, v_tag_3079_);
lean_closure_set(v___f_3094_, 9, v_opts_3080_);
lean_closure_set(v___f_3094_, 10, v___x_3093_);
lean_closure_set(v___f_3094_, 11, v_oldTraces_3089_);
lean_closure_set(v___f_3094_, 12, v_toPure_3082_);
lean_closure_set(v___f_3094_, 13, v_toBind_3083_);
lean_closure_set(v___f_3094_, 14, v_k_3084_);
lean_closure_set(v___f_3094_, 15, v___x_3085_);
lean_closure_set(v___f_3094_, 16, v_inst_3086_);
lean_closure_set(v___f_3094_, 17, v_msg_3087_);
lean_closure_set(v___f_3094_, 18, v___f_3088_);
lean_closure_set(v___f_3094_, 19, v_withRef_3091_);
lean_closure_set(v___f_3094_, 20, v_getRef_3090_);
v___x_3095_ = lean_apply_4(v_toBind_3083_, lean_box(0), lean_box(0), v_getRef_3090_, v___f_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_3096_ = _args[0];
lean_object* v_always_3097_ = _args[1];
lean_object* v_inst_3098_ = _args[2];
lean_object* v_inst_3099_ = _args[3];
lean_object* v_inst_3100_ = _args[4];
lean_object* v_inst_3101_ = _args[5];
lean_object* v_cls_3102_ = _args[6];
lean_object* v_collapsed_3103_ = _args[7];
lean_object* v_tag_3104_ = _args[8];
lean_object* v_opts_3105_ = _args[9];
lean_object* v_clsEnabled_3106_ = _args[10];
lean_object* v_toPure_3107_ = _args[11];
lean_object* v_toBind_3108_ = _args[12];
lean_object* v_k_3109_ = _args[13];
lean_object* v___x_3110_ = _args[14];
lean_object* v_inst_3111_ = _args[15];
lean_object* v_msg_3112_ = _args[16];
lean_object* v___f_3113_ = _args[17];
lean_object* v_oldTraces_3114_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_3115_; uint8_t v_clsEnabled_boxed_3116_; lean_object* v_res_3117_; 
v_collapsed_boxed_3115_ = lean_unbox(v_collapsed_3103_);
v_clsEnabled_boxed_3116_ = lean_unbox(v_clsEnabled_3106_);
v_res_3117_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3096_, v_always_3097_, v_inst_3098_, v_inst_3099_, v_inst_3100_, v_inst_3101_, v_cls_3102_, v_collapsed_boxed_3115_, v_tag_3104_, v_opts_3105_, v_clsEnabled_boxed_3116_, v_toPure_3107_, v_toBind_3108_, v_k_3109_, v___x_3110_, v_inst_3111_, v_msg_3112_, v___f_3113_, v_oldTraces_3114_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object* v_inst_3118_, lean_object* v_always_3119_, lean_object* v_inst_3120_, lean_object* v_inst_3121_, lean_object* v_inst_3122_, lean_object* v_inst_3123_, lean_object* v_cls_3124_, uint8_t v_collapsed_3125_, lean_object* v_tag_3126_, lean_object* v_opts_3127_, lean_object* v_toPure_3128_, lean_object* v_toBind_3129_, lean_object* v_k_3130_, lean_object* v___x_3131_, lean_object* v_inst_3132_, lean_object* v_msg_3133_, lean_object* v___f_3134_, uint8_t v_clsEnabled_3135_){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___f_3138_; 
v___x_3136_ = lean_box(v_collapsed_3125_);
v___x_3137_ = lean_box(v_clsEnabled_3135_);
lean_inc_ref(v___x_3131_);
lean_inc(v_k_3130_);
lean_inc(v_toBind_3129_);
lean_inc_ref(v_opts_3127_);
lean_inc_ref(v_inst_3121_);
lean_inc_ref(v_inst_3120_);
v___f_3138_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__2___boxed), 19, 18);
lean_closure_set(v___f_3138_, 0, v_inst_3118_);
lean_closure_set(v___f_3138_, 1, v_always_3119_);
lean_closure_set(v___f_3138_, 2, v_inst_3120_);
lean_closure_set(v___f_3138_, 3, v_inst_3121_);
lean_closure_set(v___f_3138_, 4, v_inst_3122_);
lean_closure_set(v___f_3138_, 5, v_inst_3123_);
lean_closure_set(v___f_3138_, 6, v_cls_3124_);
lean_closure_set(v___f_3138_, 7, v___x_3136_);
lean_closure_set(v___f_3138_, 8, v_tag_3126_);
lean_closure_set(v___f_3138_, 9, v_opts_3127_);
lean_closure_set(v___f_3138_, 10, v___x_3137_);
lean_closure_set(v___f_3138_, 11, v_toPure_3128_);
lean_closure_set(v___f_3138_, 12, v_toBind_3129_);
lean_closure_set(v___f_3138_, 13, v_k_3130_);
lean_closure_set(v___f_3138_, 14, v___x_3131_);
lean_closure_set(v___f_3138_, 15, v_inst_3132_);
lean_closure_set(v___f_3138_, 16, v_msg_3133_);
lean_closure_set(v___f_3138_, 17, v___f_3134_);
if (v_clsEnabled_3135_ == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v___x_3142_ = l_Lean_trace_profiler;
v___x_3143_ = l_Lean_Option_get___redArg(v___x_3131_, v_opts_3127_, v___x_3142_);
lean_dec_ref(v_opts_3127_);
v___x_3144_ = lean_unbox(v___x_3143_);
lean_dec(v___x_3143_);
if (v___x_3144_ == 0)
{
lean_dec_ref(v___f_3138_);
lean_dec(v_toBind_3129_);
lean_dec_ref(v_inst_3121_);
lean_dec_ref(v_inst_3120_);
return v_k_3130_;
}
else
{
lean_dec(v_k_3130_);
goto v___jp_3139_;
}
}
else
{
lean_dec_ref(v___x_3131_);
lean_dec(v_k_3130_);
lean_dec_ref(v_opts_3127_);
goto v___jp_3139_;
}
v___jp_3139_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3120_, v_inst_3121_);
v___x_3141_ = lean_apply_4(v_toBind_3129_, lean_box(0), lean_box(0), v___x_3140_, v___f_3138_);
return v___x_3141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_3145_ = _args[0];
lean_object* v_always_3146_ = _args[1];
lean_object* v_inst_3147_ = _args[2];
lean_object* v_inst_3148_ = _args[3];
lean_object* v_inst_3149_ = _args[4];
lean_object* v_inst_3150_ = _args[5];
lean_object* v_cls_3151_ = _args[6];
lean_object* v_collapsed_3152_ = _args[7];
lean_object* v_tag_3153_ = _args[8];
lean_object* v_opts_3154_ = _args[9];
lean_object* v_toPure_3155_ = _args[10];
lean_object* v_toBind_3156_ = _args[11];
lean_object* v_k_3157_ = _args[12];
lean_object* v___x_3158_ = _args[13];
lean_object* v_inst_3159_ = _args[14];
lean_object* v_msg_3160_ = _args[15];
lean_object* v___f_3161_ = _args[16];
lean_object* v_clsEnabled_3162_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3163_; uint8_t v_clsEnabled_boxed_3164_; lean_object* v_res_3165_; 
v_collapsed_boxed_3163_ = lean_unbox(v_collapsed_3152_);
v_clsEnabled_boxed_3164_ = lean_unbox(v_clsEnabled_3162_);
v_res_3165_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3145_, v_always_3146_, v_inst_3147_, v_inst_3148_, v_inst_3149_, v_inst_3150_, v_cls_3151_, v_collapsed_boxed_3163_, v_tag_3153_, v_opts_3154_, v_toPure_3155_, v_toBind_3156_, v_k_3157_, v___x_3158_, v_inst_3159_, v_msg_3160_, v___f_3161_, v_clsEnabled_boxed_3164_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object* v_k_3166_, lean_object* v_inst_3167_, lean_object* v_toApplicative_3168_, lean_object* v_inst_3169_, lean_object* v_always_3170_, lean_object* v_inst_3171_, lean_object* v_inst_3172_, lean_object* v_inst_3173_, lean_object* v_cls_3174_, uint8_t v_collapsed_3175_, lean_object* v_tag_3176_, lean_object* v_toBind_3177_, lean_object* v___x_3178_, lean_object* v_inst_3179_, lean_object* v_msg_3180_, lean_object* v___f_3181_, lean_object* v_inst_3182_, lean_object* v_opts_3183_){
_start:
{
uint8_t v_hasTrace_3184_; 
v_hasTrace_3184_ = lean_ctor_get_uint8(v_opts_3183_, sizeof(void*)*1);
if (v_hasTrace_3184_ == 0)
{
lean_dec_ref(v_opts_3183_);
lean_dec(v_inst_3182_);
lean_dec(v___f_3181_);
lean_dec(v_msg_3180_);
lean_dec(v_inst_3179_);
lean_dec_ref(v___x_3178_);
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
return v_k_3166_;
}
else
{
lean_object* v_getInheritedTraceOptions_3185_; lean_object* v_toPure_3186_; lean_object* v___x_3187_; lean_object* v___f_3188_; lean_object* v___f_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v_getInheritedTraceOptions_3185_ = lean_ctor_get(v_inst_3167_, 2);
lean_inc(v_getInheritedTraceOptions_3185_);
v_toPure_3186_ = lean_ctor_get(v_toApplicative_3168_, 1);
lean_inc_n(v_toPure_3186_, 2);
lean_dec_ref(v_toApplicative_3168_);
v___x_3187_ = lean_box(v_collapsed_3175_);
lean_inc_n(v_toBind_3177_, 3);
lean_inc(v_cls_3174_);
v___f_3188_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__4___boxed), 18, 17);
lean_closure_set(v___f_3188_, 0, v_inst_3169_);
lean_closure_set(v___f_3188_, 1, v_always_3170_);
lean_closure_set(v___f_3188_, 2, v_inst_3171_);
lean_closure_set(v___f_3188_, 3, v_inst_3167_);
lean_closure_set(v___f_3188_, 4, v_inst_3172_);
lean_closure_set(v___f_3188_, 5, v_inst_3173_);
lean_closure_set(v___f_3188_, 6, v_cls_3174_);
lean_closure_set(v___f_3188_, 7, v___x_3187_);
lean_closure_set(v___f_3188_, 8, v_tag_3176_);
lean_closure_set(v___f_3188_, 9, v_opts_3183_);
lean_closure_set(v___f_3188_, 10, v_toPure_3186_);
lean_closure_set(v___f_3188_, 11, v_toBind_3177_);
lean_closure_set(v___f_3188_, 12, v_k_3166_);
lean_closure_set(v___f_3188_, 13, v___x_3178_);
lean_closure_set(v___f_3188_, 14, v_inst_3179_);
lean_closure_set(v___f_3188_, 15, v_msg_3180_);
lean_closure_set(v___f_3188_, 16, v___f_3181_);
v___f_3189_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3189_, 0, v_toPure_3186_);
lean_closure_set(v___f_3189_, 1, v_cls_3174_);
lean_closure_set(v___f_3189_, 2, v_toBind_3177_);
lean_closure_set(v___f_3189_, 3, v_inst_3182_);
v___x_3190_ = lean_apply_4(v_toBind_3177_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3185_, v___f_3189_);
v___x_3191_ = lean_apply_4(v_toBind_3177_, lean_box(0), lean_box(0), v___x_3190_, v___f_3188_);
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_k_3192_ = _args[0];
lean_object* v_inst_3193_ = _args[1];
lean_object* v_toApplicative_3194_ = _args[2];
lean_object* v_inst_3195_ = _args[3];
lean_object* v_always_3196_ = _args[4];
lean_object* v_inst_3197_ = _args[5];
lean_object* v_inst_3198_ = _args[6];
lean_object* v_inst_3199_ = _args[7];
lean_object* v_cls_3200_ = _args[8];
lean_object* v_collapsed_3201_ = _args[9];
lean_object* v_tag_3202_ = _args[10];
lean_object* v_toBind_3203_ = _args[11];
lean_object* v___x_3204_ = _args[12];
lean_object* v_inst_3205_ = _args[13];
lean_object* v_msg_3206_ = _args[14];
lean_object* v___f_3207_ = _args[15];
lean_object* v_inst_3208_ = _args[16];
lean_object* v_opts_3209_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3210_; lean_object* v_res_3211_; 
v_collapsed_boxed_3210_ = lean_unbox(v_collapsed_3201_);
v_res_3211_ = l_Lean_withTraceNodeBefore___redArg___lam__7(v_k_3192_, v_inst_3193_, v_toApplicative_3194_, v_inst_3195_, v_always_3196_, v_inst_3197_, v_inst_3198_, v_inst_3199_, v_cls_3200_, v_collapsed_boxed_3210_, v_tag_3202_, v_toBind_3203_, v___x_3204_, v_inst_3205_, v_msg_3206_, v___f_3207_, v_inst_3208_, v_opts_3209_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object* v_inst_3212_, lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_always_3217_, lean_object* v_inst_3218_, lean_object* v_inst_3219_, lean_object* v_cls_3220_, lean_object* v_msg_3221_, lean_object* v_k_3222_, uint8_t v_collapsed_3223_, lean_object* v_tag_3224_){
_start:
{
lean_object* v___x_3225_; lean_object* v_toApplicative_3226_; lean_object* v_toBind_3227_; lean_object* v___f_3228_; lean_object* v___x_3229_; lean_object* v___f_3230_; lean_object* v___x_3231_; 
v___x_3225_ = l_Lean_KVMap_instValueBool;
v_toApplicative_3226_ = lean_ctor_get(v_inst_3212_, 0);
lean_inc_ref(v_toApplicative_3226_);
v_toBind_3227_ = lean_ctor_get(v_inst_3212_, 1);
lean_inc_n(v_toBind_3227_, 2);
lean_inc(v_inst_3215_);
v___f_3228_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3228_, 0, v_inst_3215_);
v___x_3229_ = lean_box(v_collapsed_3223_);
lean_inc(v_inst_3216_);
v___f_3230_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 18, 17);
lean_closure_set(v___f_3230_, 0, v_k_3222_);
lean_closure_set(v___f_3230_, 1, v_inst_3213_);
lean_closure_set(v___f_3230_, 2, v_toApplicative_3226_);
lean_closure_set(v___f_3230_, 3, v_inst_3214_);
lean_closure_set(v___f_3230_, 4, v_always_3217_);
lean_closure_set(v___f_3230_, 5, v_inst_3212_);
lean_closure_set(v___f_3230_, 6, v_inst_3215_);
lean_closure_set(v___f_3230_, 7, v_inst_3219_);
lean_closure_set(v___f_3230_, 8, v_cls_3220_);
lean_closure_set(v___f_3230_, 9, v___x_3229_);
lean_closure_set(v___f_3230_, 10, v_tag_3224_);
lean_closure_set(v___f_3230_, 11, v_toBind_3227_);
lean_closure_set(v___f_3230_, 12, v___x_3225_);
lean_closure_set(v___f_3230_, 13, v_inst_3218_);
lean_closure_set(v___f_3230_, 14, v_msg_3221_);
lean_closure_set(v___f_3230_, 15, v___f_3228_);
lean_closure_set(v___f_3230_, 16, v_inst_3216_);
v___x_3231_ = lean_apply_4(v_toBind_3227_, lean_box(0), lean_box(0), v_inst_3216_, v___f_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object* v_inst_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_inst_3236_, lean_object* v_always_3237_, lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_cls_3240_, lean_object* v_msg_3241_, lean_object* v_k_3242_, lean_object* v_collapsed_3243_, lean_object* v_tag_3244_){
_start:
{
uint8_t v_collapsed_boxed_3245_; lean_object* v_res_3246_; 
v_collapsed_boxed_3245_ = lean_unbox(v_collapsed_3243_);
v_res_3246_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3232_, v_inst_3233_, v_inst_3234_, v_inst_3235_, v_inst_3236_, v_always_3237_, v_inst_3238_, v_inst_3239_, v_cls_3240_, v_msg_3241_, v_k_3242_, v_collapsed_boxed_3245_, v_tag_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore(lean_object* v_00_u03b1_3247_, lean_object* v_m_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_00_u03b5_3251_, lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_inst_3254_, lean_object* v_always_3255_, lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_cls_3258_, lean_object* v_msg_3259_, lean_object* v_k_3260_, uint8_t v_collapsed_3261_, lean_object* v_tag_3262_){
_start:
{
lean_object* v___x_3263_; lean_object* v_toApplicative_3264_; lean_object* v_toBind_3265_; lean_object* v___f_3266_; lean_object* v___x_3267_; lean_object* v___f_3268_; lean_object* v___x_3269_; 
v___x_3263_ = l_Lean_KVMap_instValueBool;
v_toApplicative_3264_ = lean_ctor_get(v_inst_3249_, 0);
lean_inc_ref(v_toApplicative_3264_);
v_toBind_3265_ = lean_ctor_get(v_inst_3249_, 1);
lean_inc_n(v_toBind_3265_, 2);
lean_inc(v_inst_3253_);
v___f_3266_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3266_, 0, v_inst_3253_);
v___x_3267_ = lean_box(v_collapsed_3261_);
lean_inc(v_inst_3254_);
v___f_3268_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 18, 17);
lean_closure_set(v___f_3268_, 0, v_k_3260_);
lean_closure_set(v___f_3268_, 1, v_inst_3250_);
lean_closure_set(v___f_3268_, 2, v_toApplicative_3264_);
lean_closure_set(v___f_3268_, 3, v_inst_3252_);
lean_closure_set(v___f_3268_, 4, v_always_3255_);
lean_closure_set(v___f_3268_, 5, v_inst_3249_);
lean_closure_set(v___f_3268_, 6, v_inst_3253_);
lean_closure_set(v___f_3268_, 7, v_inst_3257_);
lean_closure_set(v___f_3268_, 8, v_cls_3258_);
lean_closure_set(v___f_3268_, 9, v___x_3267_);
lean_closure_set(v___f_3268_, 10, v_tag_3262_);
lean_closure_set(v___f_3268_, 11, v_toBind_3265_);
lean_closure_set(v___f_3268_, 12, v___x_3263_);
lean_closure_set(v___f_3268_, 13, v_inst_3256_);
lean_closure_set(v___f_3268_, 14, v_msg_3259_);
lean_closure_set(v___f_3268_, 15, v___f_3266_);
lean_closure_set(v___f_3268_, 16, v_inst_3254_);
v___x_3269_ = lean_apply_4(v_toBind_3265_, lean_box(0), lean_box(0), v_inst_3254_, v___f_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object* v_00_u03b1_3270_, lean_object* v_m_3271_, lean_object* v_inst_3272_, lean_object* v_inst_3273_, lean_object* v_00_u03b5_3274_, lean_object* v_inst_3275_, lean_object* v_inst_3276_, lean_object* v_inst_3277_, lean_object* v_always_3278_, lean_object* v_inst_3279_, lean_object* v_inst_3280_, lean_object* v_cls_3281_, lean_object* v_msg_3282_, lean_object* v_k_3283_, lean_object* v_collapsed_3284_, lean_object* v_tag_3285_){
_start:
{
uint8_t v_collapsed_boxed_3286_; lean_object* v_res_3287_; 
v_collapsed_boxed_3286_ = lean_unbox(v_collapsed_3284_);
v_res_3287_ = l_Lean_withTraceNodeBefore(v_00_u03b1_3270_, v_m_3271_, v_inst_3272_, v_inst_3273_, v_00_u03b5_3274_, v_inst_3275_, v_inst_3276_, v_inst_3277_, v_always_3278_, v_inst_3279_, v_inst_3280_, v_cls_3281_, v_msg_3282_, v_k_3283_, v_collapsed_boxed_3286_, v_tag_3285_);
return v_res_3287_;
}
}
LEAN_EXPORT uint8_t l_Lean_addTraceAsMessages___redArg___lam__0(lean_object* v_x_3288_, lean_object* v_x_3289_){
_start:
{
lean_object* v_fst_3290_; lean_object* v_fst_3291_; lean_object* v_fst_3292_; lean_object* v_fst_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v_fst_3290_ = lean_ctor_get(v_x_3288_, 0);
v_fst_3291_ = lean_ctor_get(v_x_3289_, 0);
v_fst_3292_ = lean_ctor_get(v_fst_3290_, 0);
v_fst_3293_ = lean_ctor_get(v_fst_3291_, 0);
v___x_3294_ = lean_unsigned_to_nat(1u);
v___x_3295_ = lean_nat_add(v_fst_3292_, v___x_3294_);
v___x_3296_ = lean_nat_dec_le(v___x_3295_, v_fst_3293_);
lean_dec(v___x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0___boxed(lean_object* v_x_3297_, lean_object* v_x_3298_){
_start:
{
uint8_t v_res_3299_; lean_object* v_r_3300_; 
v_res_3299_ = l_Lean_addTraceAsMessages___redArg___lam__0(v_x_3297_, v_x_3298_);
lean_dec_ref(v_x_3298_);
lean_dec_ref(v_x_3297_);
v_r_3300_ = lean_box(v_res_3299_);
return v_r_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1(lean_object* v_x1_3301_, lean_object* v_x2_3302_, lean_object* v_x3_3303_){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v_x2_3302_);
lean_ctor_set(v___x_3304_, 1, v_x3_3303_);
v___x_3305_ = lean_array_push(v_x1_3301_, v___x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object* v_____do__lift_3306_, lean_object* v___x_3307_, lean_object* v_fst_3308_, lean_object* v_snd_3309_, lean_object* v_logMessage_3310_, lean_object* v_toBind_3311_, lean_object* v___f_3312_, lean_object* v_____do__lift_3313_){
_start:
{
uint8_t v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3314_ = 0;
v___x_3315_ = l_Lean_Elab_mkMessageCore(v_____do__lift_3306_, v_____do__lift_3313_, v___x_3307_, v___x_3314_, v_fst_3308_, v_snd_3309_);
v___x_3316_ = lean_apply_1(v_logMessage_3310_, v___x_3315_);
v___x_3317_ = lean_apply_4(v_toBind_3311_, lean_box(0), lean_box(0), v___x_3316_, v___f_3312_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object* v_____do__lift_3318_, lean_object* v___x_3319_, lean_object* v_fst_3320_, lean_object* v_snd_3321_, lean_object* v_logMessage_3322_, lean_object* v_toBind_3323_, lean_object* v___f_3324_, lean_object* v_____do__lift_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_addTraceAsMessages___redArg___lam__4(v_____do__lift_3318_, v___x_3319_, v_fst_3320_, v_snd_3321_, v_logMessage_3322_, v_toBind_3323_, v___f_3324_, v_____do__lift_3325_);
lean_dec(v_snd_3321_);
lean_dec(v_fst_3320_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object* v___x_3327_, lean_object* v_fst_3328_, lean_object* v_snd_3329_, lean_object* v_logMessage_3330_, lean_object* v_toBind_3331_, lean_object* v___f_3332_, lean_object* v_toMonadFileMap_3333_, lean_object* v_____do__lift_3334_){
_start:
{
lean_object* v___f_3335_; lean_object* v___x_3336_; 
lean_inc(v_toBind_3331_);
v___f_3335_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_3335_, 0, v_____do__lift_3334_);
lean_closure_set(v___f_3335_, 1, v___x_3327_);
lean_closure_set(v___f_3335_, 2, v_fst_3328_);
lean_closure_set(v___f_3335_, 3, v_snd_3329_);
lean_closure_set(v___f_3335_, 4, v_logMessage_3330_);
lean_closure_set(v___f_3335_, 5, v_toBind_3331_);
lean_closure_set(v___f_3335_, 6, v___f_3332_);
v___x_3336_ = lean_apply_4(v_toBind_3331_, lean_box(0), lean_box(0), v_toMonadFileMap_3333_, v___f_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object* v___x_3337_, uint8_t v___x_3338_, lean_object* v_logMessage_3339_, lean_object* v_toBind_3340_, lean_object* v___f_3341_, lean_object* v_toMonadFileMap_3342_, lean_object* v_getFileName_3343_, lean_object* v_a_3344_, lean_object* v_x_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_fst_3347_; lean_object* v_snd_3348_; lean_object* v_fst_3349_; lean_object* v_snd_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3367_; 
v_fst_3347_ = lean_ctor_get(v_a_3344_, 0);
lean_inc(v_fst_3347_);
v_snd_3348_ = lean_ctor_get(v_a_3344_, 1);
lean_inc(v_snd_3348_);
lean_dec_ref(v_a_3344_);
v_fst_3349_ = lean_ctor_get(v_fst_3347_, 0);
v_snd_3350_ = lean_ctor_get(v_fst_3347_, 1);
v_isSharedCheck_3367_ = !lean_is_exclusive(v_fst_3347_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3352_ = v_fst_3347_;
v_isShared_3353_ = v_isSharedCheck_3367_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_snd_3350_);
lean_inc(v_fst_3349_);
lean_dec(v_fst_3347_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3367_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; double v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3354_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_3355_ = lean_box(0);
v___x_3356_ = lean_box(0);
v___x_3357_ = lean_float_of_nat(v___x_3337_);
v___x_3358_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_3359_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3359_, 0, v___x_3355_);
lean_ctor_set(v___x_3359_, 1, v___x_3356_);
lean_ctor_set(v___x_3359_, 2, v___x_3358_);
lean_ctor_set_float(v___x_3359_, sizeof(void*)*3, v___x_3357_);
lean_ctor_set_float(v___x_3359_, sizeof(void*)*3 + 8, v___x_3357_);
lean_ctor_set_uint8(v___x_3359_, sizeof(void*)*3 + 16, v___x_3338_);
v___x_3360_ = l_Lean_MessageData_nil;
v___x_3361_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3359_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
lean_ctor_set(v___x_3361_, 2, v_snd_3348_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set_tag(v___x_3352_, 8);
lean_ctor_set(v___x_3352_, 1, v___x_3361_);
lean_ctor_set(v___x_3352_, 0, v___x_3354_);
v___x_3363_ = v___x_3352_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3354_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___f_3364_; lean_object* v___x_3365_; 
lean_inc(v_toBind_3340_);
v___f_3364_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__2), 8, 7);
lean_closure_set(v___f_3364_, 0, v___x_3363_);
lean_closure_set(v___f_3364_, 1, v_fst_3349_);
lean_closure_set(v___f_3364_, 2, v_snd_3350_);
lean_closure_set(v___f_3364_, 3, v_logMessage_3339_);
lean_closure_set(v___f_3364_, 4, v_toBind_3340_);
lean_closure_set(v___f_3364_, 5, v___f_3341_);
lean_closure_set(v___f_3364_, 6, v_toMonadFileMap_3342_);
v___x_3365_ = lean_apply_4(v_toBind_3340_, lean_box(0), lean_box(0), v_getFileName_3343_, v___f_3364_);
return v___x_3365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3___boxed(lean_object* v___x_3368_, lean_object* v___x_3369_, lean_object* v_logMessage_3370_, lean_object* v_toBind_3371_, lean_object* v___f_3372_, lean_object* v_toMonadFileMap_3373_, lean_object* v_getFileName_3374_, lean_object* v_a_3375_, lean_object* v_x_3376_, lean_object* v___y_3377_){
_start:
{
uint8_t v___x_896__boxed_3378_; lean_object* v_res_3379_; 
v___x_896__boxed_3378_ = lean_unbox(v___x_3369_);
v_res_3379_ = l_Lean_addTraceAsMessages___redArg___lam__3(v___x_3368_, v___x_896__boxed_3378_, v_logMessage_3370_, v_toBind_3371_, v___f_3372_, v_toMonadFileMap_3373_, v_getFileName_3374_, v_a_3375_, v_x_3376_, v___y_3377_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object* v___x_3380_, lean_object* v___f_3381_, lean_object* v_acc_3382_, lean_object* v_l_3383_){
_start:
{
lean_object* v___x_3384_; 
v___x_3384_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_3380_, v___f_3381_, v_acc_3382_, v_l_3383_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object* v_toPure_3385_, uint8_t v___x_3386_, lean_object* v_logMessage_3387_, lean_object* v_toBind_3388_, lean_object* v_toMonadFileMap_3389_, lean_object* v_getFileName_3390_, lean_object* v_inst_3391_, lean_object* v___f_3392_, lean_object* v___f_3393_, lean_object* v___f_3394_, lean_object* v_____s_3395_){
_start:
{
lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3422_; lean_object* v_size_3429_; lean_object* v_buckets_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v_size_3429_ = lean_ctor_get(v_____s_3395_, 0);
lean_inc(v_size_3429_);
v_buckets_3430_ = lean_ctor_get(v_____s_3395_, 1);
lean_inc_ref(v_buckets_3430_);
lean_dec_ref(v_____s_3395_);
v___x_3431_ = lean_mk_empty_array_with_capacity(v_size_3429_);
lean_dec(v_size_3429_);
v___x_3432_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v___x_3433_ = lean_unsigned_to_nat(0u);
v___x_3434_ = lean_array_get_size(v_buckets_3430_);
v___x_3435_ = lean_nat_dec_lt(v___x_3433_, v___x_3434_);
if (v___x_3435_ == 0)
{
lean_dec_ref(v_buckets_3430_);
lean_dec_ref(v___f_3394_);
v___y_3422_ = v___x_3431_;
goto v___jp_3421_;
}
else
{
lean_object* v___f_3436_; size_t v___x_3437_; size_t v___x_3438_; lean_object* v___x_3439_; 
v___f_3436_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__5), 4, 2);
lean_closure_set(v___f_3436_, 0, v___x_3432_);
lean_closure_set(v___f_3436_, 1, v___f_3394_);
v___x_3437_ = ((size_t)0ULL);
v___x_3438_ = lean_usize_of_nat(v___x_3434_);
v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3432_, v___f_3436_, v_buckets_3430_, v___x_3437_, v___x_3438_, v___x_3431_);
v___y_3422_ = v___x_3439_;
goto v___jp_3421_;
}
v___jp_3396_:
{
lean_object* v___x_3399_; lean_object* v___f_3400_; lean_object* v___x_3401_; lean_object* v___f_3402_; size_t v_sz_3403_; size_t v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3399_ = lean_box(0);
v___f_3400_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3400_, 0, v___x_3399_);
lean_closure_set(v___f_3400_, 1, v_toPure_3385_);
v___x_3401_ = lean_box(v___x_3386_);
lean_inc(v_toBind_3388_);
v___f_3402_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__3___boxed), 10, 7);
lean_closure_set(v___f_3402_, 0, v___y_3397_);
lean_closure_set(v___f_3402_, 1, v___x_3401_);
lean_closure_set(v___f_3402_, 2, v_logMessage_3387_);
lean_closure_set(v___f_3402_, 3, v_toBind_3388_);
lean_closure_set(v___f_3402_, 4, v___f_3400_);
lean_closure_set(v___f_3402_, 5, v_toMonadFileMap_3389_);
lean_closure_set(v___f_3402_, 6, v_getFileName_3390_);
v_sz_3403_ = lean_array_size(v___y_3398_);
v___x_3404_ = ((size_t)0ULL);
v___x_3405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3391_, v___y_3398_, v___f_3402_, v_sz_3403_, v___x_3404_, v___x_3399_);
v___x_3406_ = lean_apply_4(v_toBind_3388_, lean_box(0), lean_box(0), v___x_3405_, v___f_3392_);
return v___x_3406_;
}
v___jp_3407_:
{
lean_object* v___x_3413_; 
v___x_3413_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_3393_, v___y_3410_, v___y_3411_, v___y_3409_, v___y_3412_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_3412_);
lean_dec(v___y_3410_);
v___y_3397_ = v___y_3408_;
v___y_3398_ = v___x_3413_;
goto v___jp_3396_;
}
v___jp_3414_:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_nat_dec_le(v___y_3419_, v___y_3416_);
if (v___x_3420_ == 0)
{
lean_dec(v___y_3416_);
lean_inc(v___y_3419_);
v___y_3408_ = v___y_3415_;
v___y_3409_ = v___y_3419_;
v___y_3410_ = v___y_3417_;
v___y_3411_ = v___y_3418_;
v___y_3412_ = v___y_3419_;
goto v___jp_3407_;
}
else
{
v___y_3408_ = v___y_3415_;
v___y_3409_ = v___y_3419_;
v___y_3410_ = v___y_3417_;
v___y_3411_ = v___y_3418_;
v___y_3412_ = v___y_3416_;
goto v___jp_3407_;
}
}
v___jp_3421_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_array_get_size(v___y_3422_);
v___x_3425_ = lean_nat_dec_eq(v___x_3424_, v___x_3423_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3426_ = lean_unsigned_to_nat(1u);
v___x_3427_ = lean_nat_sub(v___x_3424_, v___x_3426_);
v___x_3428_ = lean_nat_dec_le(v___x_3423_, v___x_3427_);
if (v___x_3428_ == 0)
{
lean_inc(v___x_3427_);
v___y_3415_ = v___x_3423_;
v___y_3416_ = v___x_3427_;
v___y_3417_ = v___x_3424_;
v___y_3418_ = v___y_3422_;
v___y_3419_ = v___x_3427_;
goto v___jp_3414_;
}
else
{
v___y_3415_ = v___x_3423_;
v___y_3416_ = v___x_3427_;
v___y_3417_ = v___x_3424_;
v___y_3418_ = v___y_3422_;
v___y_3419_ = v___x_3423_;
goto v___jp_3414_;
}
}
else
{
lean_dec_ref(v___f_3393_);
v___y_3397_ = v___x_3423_;
v___y_3398_ = v___y_3422_;
goto v___jp_3396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object* v_toPure_3440_, lean_object* v___x_3441_, lean_object* v_logMessage_3442_, lean_object* v_toBind_3443_, lean_object* v_toMonadFileMap_3444_, lean_object* v_getFileName_3445_, lean_object* v_inst_3446_, lean_object* v___f_3447_, lean_object* v___f_3448_, lean_object* v___f_3449_, lean_object* v_____s_3450_){
_start:
{
uint8_t v___x_981__boxed_3451_; lean_object* v_res_3452_; 
v___x_981__boxed_3451_ = lean_unbox(v___x_3441_);
v_res_3452_ = l_Lean_addTraceAsMessages___redArg___lam__6(v_toPure_3440_, v___x_981__boxed_3451_, v_logMessage_3442_, v_toBind_3443_, v_toMonadFileMap_3444_, v_getFileName_3445_, v_inst_3446_, v___f_3447_, v___f_3448_, v___f_3449_, v_____s_3450_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object* v_traceElem_3453_, lean_object* v___f_3454_, lean_object* v___f_3455_, lean_object* v_____s_3456_, lean_object* v_toPure_3457_, uint8_t v___x_3458_, lean_object* v_____do__lift_3459_){
_start:
{
lean_object* v_ref_3460_; lean_object* v_msg_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3485_; 
v_ref_3460_ = lean_ctor_get(v_traceElem_3453_, 0);
v_msg_3461_ = lean_ctor_get(v_traceElem_3453_, 1);
v_isSharedCheck_3485_ = !lean_is_exclusive(v_traceElem_3453_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3463_ = v_traceElem_3453_;
v_isShared_3464_ = v_isSharedCheck_3485_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_msg_3461_);
lean_inc(v_ref_3460_);
lean_dec(v_traceElem_3453_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3485_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v_ref_3477_; lean_object* v___y_3479_; lean_object* v___x_3482_; 
v_ref_3477_ = l_Lean_replaceRef(v_ref_3460_, v_____do__lift_3459_);
lean_dec(v_ref_3460_);
v___x_3482_ = l_Lean_Syntax_getPos_x3f(v_ref_3477_, v___x_3458_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v___x_3483_; 
v___x_3483_ = lean_unsigned_to_nat(0u);
v___y_3479_ = v___x_3483_;
goto v___jp_3478_;
}
else
{
lean_object* v_val_3484_; 
v_val_3484_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_val_3484_);
lean_dec_ref_known(v___x_3482_, 1);
v___y_3479_ = v_val_3484_;
goto v___jp_3478_;
}
v___jp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v___y_3467_);
lean_ctor_set(v___x_3463_, 0, v___y_3466_);
v___x_3469_ = v___x_3463_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___y_3466_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v___y_3467_);
v___x_3469_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v_pos2traces_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3470_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
lean_inc_ref(v___x_3469_);
lean_inc_ref(v___f_3455_);
lean_inc_ref(v___f_3454_);
v___x_3471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_3454_, v___f_3455_, v_____s_3456_, v___x_3469_, v___x_3470_);
v___x_3472_ = lean_array_push(v___x_3471_, v_msg_3461_);
v_pos2traces_3473_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3454_, v___f_3455_, v_____s_3456_, v___x_3469_, v___x_3472_);
v___x_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3474_, 0, v_pos2traces_3473_);
v___x_3475_ = lean_apply_2(v_toPure_3457_, lean_box(0), v___x_3474_);
return v___x_3475_;
}
}
v___jp_3478_:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_Syntax_getTailPos_x3f(v_ref_3477_, v___x_3458_);
lean_dec(v_ref_3477_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_inc(v___y_3479_);
v___y_3466_ = v___y_3479_;
v___y_3467_ = v___y_3479_;
goto v___jp_3465_;
}
else
{
lean_object* v_val_3481_; 
v_val_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_val_3481_);
lean_dec_ref_known(v___x_3480_, 1);
v___y_3466_ = v___y_3479_;
v___y_3467_ = v_val_3481_;
goto v___jp_3465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7___boxed(lean_object* v_traceElem_3486_, lean_object* v___f_3487_, lean_object* v___f_3488_, lean_object* v_____s_3489_, lean_object* v_toPure_3490_, lean_object* v___x_3491_, lean_object* v_____do__lift_3492_){
_start:
{
uint8_t v___x_1095__boxed_3493_; lean_object* v_res_3494_; 
v___x_1095__boxed_3493_ = lean_unbox(v___x_3491_);
v_res_3494_ = l_Lean_addTraceAsMessages___redArg___lam__7(v_traceElem_3486_, v___f_3487_, v___f_3488_, v_____s_3489_, v_toPure_3490_, v___x_1095__boxed_3493_, v_____do__lift_3492_);
lean_dec(v_____do__lift_3492_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object* v_inst_3495_, lean_object* v___f_3496_, lean_object* v___f_3497_, lean_object* v_toPure_3498_, uint8_t v___x_3499_, lean_object* v_toBind_3500_, lean_object* v_traceElem_3501_, lean_object* v_____s_3502_){
_start:
{
lean_object* v_getRef_3503_; lean_object* v___x_3504_; lean_object* v___f_3505_; lean_object* v___x_3506_; 
v_getRef_3503_ = lean_ctor_get(v_inst_3495_, 0);
lean_inc(v_getRef_3503_);
lean_dec_ref(v_inst_3495_);
v___x_3504_ = lean_box(v___x_3499_);
v___f_3505_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__7___boxed), 7, 6);
lean_closure_set(v___f_3505_, 0, v_traceElem_3501_);
lean_closure_set(v___f_3505_, 1, v___f_3496_);
lean_closure_set(v___f_3505_, 2, v___f_3497_);
lean_closure_set(v___f_3505_, 3, v_____s_3502_);
lean_closure_set(v___f_3505_, 4, v_toPure_3498_);
lean_closure_set(v___f_3505_, 5, v___x_3504_);
v___x_3506_ = lean_apply_4(v_toBind_3500_, lean_box(0), lean_box(0), v_getRef_3503_, v___f_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object* v_inst_3507_, lean_object* v___f_3508_, lean_object* v___f_3509_, lean_object* v_toPure_3510_, lean_object* v___x_3511_, lean_object* v_toBind_3512_, lean_object* v_traceElem_3513_, lean_object* v_____s_3514_){
_start:
{
uint8_t v___x_1155__boxed_3515_; lean_object* v_res_3516_; 
v___x_1155__boxed_3515_ = lean_unbox(v___x_3511_);
v_res_3516_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_inst_3507_, v___f_3508_, v___f_3509_, v_toPure_3510_, v___x_1155__boxed_3515_, v_toBind_3512_, v_traceElem_3513_, v_____s_3514_);
return v_res_3516_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__0(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___f_3518_; 
v___x_3517_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_3518_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3518_, 0, v___x_3517_);
return v___f_3518_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__1(void){
_start:
{
lean_object* v___f_3519_; lean_object* v___f_3520_; 
v___f_3519_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__0, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__0_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__0);
v___f_3520_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3520_, 0, v___f_3519_);
lean_closure_set(v___f_3520_, 1, v___f_3519_);
return v___f_3520_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__2(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3521_ = lean_box(0);
v___x_3522_ = lean_unsigned_to_nat(16u);
v___x_3523_ = lean_mk_array(v___x_3522_, v___x_3521_);
return v___x_3523_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__3(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v_pos2traces_3526_; 
v___x_3524_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__2, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__2_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__2);
v___x_3525_ = lean_unsigned_to_nat(0u);
v_pos2traces_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_3526_, 0, v___x_3525_);
lean_ctor_set(v_pos2traces_3526_, 1, v___x_3524_);
return v_pos2traces_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object* v_inst_3527_, lean_object* v___f_3528_, lean_object* v_toPure_3529_, lean_object* v_toBind_3530_, lean_object* v_inst_3531_, lean_object* v___f_3532_, lean_object* v_traces_3533_){
_start:
{
uint8_t v___x_3534_; 
v___x_3534_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_3533_);
if (v___x_3534_ == 0)
{
lean_object* v___f_3535_; lean_object* v___x_3536_; lean_object* v___f_3537_; lean_object* v_pos2traces_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___f_3535_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__1, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__1_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__1);
v___x_3536_ = lean_box(v___x_3534_);
lean_inc(v_toBind_3530_);
v___f_3537_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__8___boxed), 8, 6);
lean_closure_set(v___f_3537_, 0, v_inst_3527_);
lean_closure_set(v___f_3537_, 1, v___f_3535_);
lean_closure_set(v___f_3537_, 2, v___f_3528_);
lean_closure_set(v___f_3537_, 3, v_toPure_3529_);
lean_closure_set(v___f_3537_, 4, v___x_3536_);
lean_closure_set(v___f_3537_, 5, v_toBind_3530_);
v_pos2traces_3538_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__3, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__3_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__3);
v___x_3539_ = l_Lean_PersistentArray_forIn___redArg(v_inst_3531_, v_traces_3533_, v_pos2traces_3538_, v___f_3537_);
v___x_3540_ = lean_apply_4(v_toBind_3530_, lean_box(0), lean_box(0), v___x_3539_, v___f_3532_);
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
lean_dec(v___f_3532_);
lean_dec_ref(v_inst_3531_);
lean_dec(v_toBind_3530_);
lean_dec_ref(v___f_3528_);
lean_dec_ref(v_inst_3527_);
v___x_3541_ = lean_box(0);
v___x_3542_ = lean_apply_2(v_toPure_3529_, lean_box(0), v___x_3541_);
return v___x_3542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object* v_inst_3543_, lean_object* v___f_3544_, lean_object* v_toPure_3545_, lean_object* v_toBind_3546_, lean_object* v_inst_3547_, lean_object* v___f_3548_, lean_object* v_traces_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Lean_addTraceAsMessages___redArg___lam__9(v_inst_3543_, v___f_3544_, v_toPure_3545_, v_toBind_3546_, v_inst_3547_, v___f_3548_, v_traces_3549_);
lean_dec_ref(v_traces_3549_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object* v_toPure_3551_, lean_object* v_logMessage_3552_, lean_object* v_toBind_3553_, lean_object* v_toMonadFileMap_3554_, lean_object* v_getFileName_3555_, lean_object* v_inst_3556_, lean_object* v___f_3557_, lean_object* v___f_3558_, lean_object* v___f_3559_, lean_object* v_inst_3560_, lean_object* v___f_3561_, lean_object* v_inst_3562_, lean_object* v_____do__lift_3563_){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3567_ = l_Lean_KVMap_instValueBool;
v___x_3568_ = l_Lean_KVMap_instValueString;
v___x_3569_ = l_Lean_trace_profiler_output;
v___x_3570_ = l_Lean_Option_get_x3f___redArg(v___x_3568_, v_____do__lift_3563_, v___x_3569_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v___x_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; 
v___x_3571_ = l_Lean_trace_profiler_serve;
v___x_3572_ = l_Lean_Option_get___redArg(v___x_3567_, v_____do__lift_3563_, v___x_3571_);
v___x_3573_ = lean_unbox(v___x_3572_);
lean_dec(v___x_3572_);
if (v___x_3573_ == 0)
{
uint8_t v___x_3574_; lean_object* v___x_3575_; lean_object* v___f_3576_; lean_object* v___f_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3574_ = 1;
v___x_3575_ = lean_box(v___x_3574_);
lean_inc_ref_n(v_inst_3556_, 2);
lean_inc_n(v_toBind_3553_, 2);
lean_inc(v_toPure_3551_);
v___f_3576_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_3576_, 0, v_toPure_3551_);
lean_closure_set(v___f_3576_, 1, v___x_3575_);
lean_closure_set(v___f_3576_, 2, v_logMessage_3552_);
lean_closure_set(v___f_3576_, 3, v_toBind_3553_);
lean_closure_set(v___f_3576_, 4, v_toMonadFileMap_3554_);
lean_closure_set(v___f_3576_, 5, v_getFileName_3555_);
lean_closure_set(v___f_3576_, 6, v_inst_3556_);
lean_closure_set(v___f_3576_, 7, v___f_3557_);
lean_closure_set(v___f_3576_, 8, v___f_3558_);
lean_closure_set(v___f_3576_, 9, v___f_3559_);
v___f_3577_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_3577_, 0, v_inst_3560_);
lean_closure_set(v___f_3577_, 1, v___f_3561_);
lean_closure_set(v___f_3577_, 2, v_toPure_3551_);
lean_closure_set(v___f_3577_, 3, v_toBind_3553_);
lean_closure_set(v___f_3577_, 4, v_inst_3556_);
lean_closure_set(v___f_3577_, 5, v___f_3576_);
v___x_3578_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3556_, v_inst_3562_);
v___x_3579_ = lean_apply_4(v_toBind_3553_, lean_box(0), lean_box(0), v___x_3578_, v___f_3577_);
return v___x_3579_;
}
else
{
lean_dec_ref(v_inst_3562_);
lean_dec_ref(v___f_3561_);
lean_dec_ref(v_inst_3560_);
lean_dec_ref(v___f_3559_);
lean_dec_ref(v___f_3558_);
lean_dec(v___f_3557_);
lean_dec_ref(v_inst_3556_);
lean_dec(v_getFileName_3555_);
lean_dec(v_toMonadFileMap_3554_);
lean_dec(v_toBind_3553_);
lean_dec(v_logMessage_3552_);
goto v___jp_3564_;
}
}
else
{
lean_dec_ref_known(v___x_3570_, 1);
lean_dec_ref(v_inst_3562_);
lean_dec_ref(v___f_3561_);
lean_dec_ref(v_inst_3560_);
lean_dec_ref(v___f_3559_);
lean_dec_ref(v___f_3558_);
lean_dec(v___f_3557_);
lean_dec_ref(v_inst_3556_);
lean_dec(v_getFileName_3555_);
lean_dec(v_toMonadFileMap_3554_);
lean_dec(v_toBind_3553_);
lean_dec(v_logMessage_3552_);
goto v___jp_3564_;
}
v___jp_3564_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = lean_box(0);
v___x_3566_ = lean_apply_2(v_toPure_3551_, lean_box(0), v___x_3565_);
return v___x_3566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object* v_toPure_3580_, lean_object* v_logMessage_3581_, lean_object* v_toBind_3582_, lean_object* v_toMonadFileMap_3583_, lean_object* v_getFileName_3584_, lean_object* v_inst_3585_, lean_object* v___f_3586_, lean_object* v___f_3587_, lean_object* v___f_3588_, lean_object* v_inst_3589_, lean_object* v___f_3590_, lean_object* v_inst_3591_, lean_object* v_____do__lift_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_addTraceAsMessages___redArg___lam__10(v_toPure_3580_, v_logMessage_3581_, v_toBind_3582_, v_toMonadFileMap_3583_, v_getFileName_3584_, v_inst_3585_, v___f_3586_, v___f_3587_, v___f_3588_, v_inst_3589_, v___f_3590_, v_inst_3591_, v_____do__lift_3592_);
lean_dec_ref(v_____do__lift_3592_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object* v_inst_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_inst_3602_, lean_object* v_inst_3603_){
_start:
{
lean_object* v___f_3604_; lean_object* v_toApplicative_3605_; lean_object* v_toBind_3606_; lean_object* v_toPure_3607_; lean_object* v_toMonadFileMap_3608_; lean_object* v_getFileName_3609_; lean_object* v_logMessage_3610_; lean_object* v___f_3611_; lean_object* v___f_3612_; lean_object* v___f_3613_; lean_object* v___f_3614_; lean_object* v___x_3615_; 
v___f_3604_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__1));
v_toApplicative_3605_ = lean_ctor_get(v_inst_3600_, 0);
v_toBind_3606_ = lean_ctor_get(v_inst_3600_, 1);
lean_inc_n(v_toBind_3606_, 2);
v_toPure_3607_ = lean_ctor_get(v_toApplicative_3605_, 1);
lean_inc_n(v_toPure_3607_, 2);
v_toMonadFileMap_3608_ = lean_ctor_get(v_inst_3602_, 0);
lean_inc(v_toMonadFileMap_3608_);
v_getFileName_3609_ = lean_ctor_get(v_inst_3602_, 2);
lean_inc(v_getFileName_3609_);
v_logMessage_3610_ = lean_ctor_get(v_inst_3602_, 4);
lean_inc(v_logMessage_3610_);
lean_dec_ref(v_inst_3602_);
v___f_3611_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__2));
v___f_3612_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__3));
v___f_3613_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3613_, 0, v_toPure_3607_);
v___f_3614_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__10___boxed), 13, 12);
lean_closure_set(v___f_3614_, 0, v_toPure_3607_);
lean_closure_set(v___f_3614_, 1, v_logMessage_3610_);
lean_closure_set(v___f_3614_, 2, v_toBind_3606_);
lean_closure_set(v___f_3614_, 3, v_toMonadFileMap_3608_);
lean_closure_set(v___f_3614_, 4, v_getFileName_3609_);
lean_closure_set(v___f_3614_, 5, v_inst_3600_);
lean_closure_set(v___f_3614_, 6, v___f_3613_);
lean_closure_set(v___f_3614_, 7, v___f_3611_);
lean_closure_set(v___f_3614_, 8, v___f_3612_);
lean_closure_set(v___f_3614_, 9, v_inst_3601_);
lean_closure_set(v___f_3614_, 10, v___f_3604_);
lean_closure_set(v___f_3614_, 11, v_inst_3603_);
v___x_3615_ = lean_apply_4(v_toBind_3606_, lean_box(0), lean_box(0), v_inst_3599_, v___f_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object* v_m_3616_, lean_object* v_inst_3617_, lean_object* v_inst_3618_, lean_object* v_inst_3619_, lean_object* v_inst_3620_, lean_object* v_inst_3621_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Lean_addTraceAsMessages___redArg(v_inst_3617_, v_inst_3618_, v_inst_3619_, v_inst_3620_, v_inst_3621_);
return v___x_3622_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = lean_unsigned_to_nat(2826257906u);
v___x_3665_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3666_ = l_Lean_Name_num___override(v___x_3665_, v___x_3664_);
return v___x_3666_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3668_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3669_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3670_ = l_Lean_Name_str___override(v___x_3669_, v___x_3668_);
return v___x_3670_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3673_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3674_ = l_Lean_Name_str___override(v___x_3673_, v___x_3672_);
return v___x_3674_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3675_ = lean_unsigned_to_nat(2u);
v___x_3676_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3677_ = l_Lean_Name_num___override(v___x_3676_, v___x_3675_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3679_; uint8_t v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3679_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3680_ = 0;
v___x_3681_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3682_ = l_Lean_registerTraceClass(v___x_3679_, v___x_3680_, v___x_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object* v_a_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
return v_res_3684_;
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
