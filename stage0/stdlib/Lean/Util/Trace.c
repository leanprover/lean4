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
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "inheritedTraceOptions"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_value;
static const lean_string_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "get"};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__16_value),LEAN_SCALAR_PTR_LITERAL(111, 221, 127, 62, 213, 113, 62, 253)}};
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value_aux_0),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__17_value),LEAN_SCALAR_PTR_LITERAL(249, 53, 178, 254, 160, 90, 192, 243)}};
static const lean_object* l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18 = (const lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value;
static const lean_ctor_object l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__15_value),((lean_object*)&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_30_;
v_res_30_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2____boxed(lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3842689300____hygCtx___hyg_2_();
return v_res_32_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__10));
v___x_60_ = l_Lean_mkAtom(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__12);
v___x_62_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_63_ = lean_array_push(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__19));
v___x_80_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_81_ = lean_array_push(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__20);
v___x_83_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_84_ = lean_box(2);
v___x_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_83_);
lean_ctor_set(v___x_85_, 2, v___x_82_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__21);
v___x_87_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_88_ = lean_array_push(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__22);
v___x_90_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_91_ = lean_box(2);
v___x_92_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v___x_90_);
lean_ctor_set(v___x_92_, 2, v___x_89_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__23);
v___x_94_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_95_ = lean_array_push(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__24);
v___x_97_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_98_ = lean_box(2);
v___x_99_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_97_);
lean_ctor_set(v___x_99_, 2, v___x_96_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__25);
v___x_101_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_102_ = lean_array_push(v___x_101_, v___x_100_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__26);
v___x_104_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_105_ = lean_box(2);
v___x_106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
lean_ctor_set(v___x_106_, 2, v___x_103_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam(void){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__27);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg___lam__0(lean_object* v_modifyTraceState_108_, lean_object* v_inst_109_, lean_object* v_f_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_apply_1(v_modifyTraceState_108_, v_f_110_);
v___x_112_ = lean_apply_2(v_inst_109_, lean_box(0), v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object* v_inst_113_, lean_object* v_inst_114_){
_start:
{
lean_object* v_modifyTraceState_115_; lean_object* v_getTraceState_116_; lean_object* v_getInheritedTraceOptions_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_127_; 
v_modifyTraceState_115_ = lean_ctor_get(v_inst_114_, 0);
v_getTraceState_116_ = lean_ctor_get(v_inst_114_, 1);
v_getInheritedTraceOptions_117_ = lean_ctor_get(v_inst_114_, 2);
v_isSharedCheck_127_ = !lean_is_exclusive(v_inst_114_);
if (v_isSharedCheck_127_ == 0)
{
v___x_119_ = v_inst_114_;
v_isShared_120_ = v_isSharedCheck_127_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_getInheritedTraceOptions_117_);
lean_inc(v_getTraceState_116_);
lean_inc(v_modifyTraceState_115_);
lean_dec(v_inst_114_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_127_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
lean_inc_n(v_inst_113_, 2);
v___f_121_ = lean_alloc_closure((void*)(l_Lean_instMonadTraceOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_121_, 0, v_modifyTraceState_115_);
lean_closure_set(v___f_121_, 1, v_inst_113_);
v___x_122_ = lean_apply_2(v_inst_113_, lean_box(0), v_getTraceState_116_);
v___x_123_ = lean_apply_2(v_inst_113_, lean_box(0), v_getInheritedTraceOptions_117_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 2, v___x_123_);
lean_ctor_set(v___x_119_, 1, v___x_122_);
lean_ctor_set(v___x_119_, 0, v___f_121_);
v___x_125_ = v___x_119_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___f_121_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_126_, 2, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadTraceOfMonadLift(lean_object* v_m_128_, lean_object* v_n_129_, lean_object* v_inst_130_, lean_object* v_inst_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_instMonadTraceOfMonadLift___redArg(v_inst_130_, v_inst_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__0(lean_object* v_toPure_133_, lean_object* v_____s_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_2(v_toPure_133_, lean_box(0), v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__1(lean_object* v___x_137_, lean_object* v_toPure_138_, lean_object* v_r_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_137_);
v___x_141_ = lean_apply_2(v_toPure_138_, lean_box(0), v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__2(lean_object* v___f_142_, lean_object* v_inst_143_, lean_object* v_toBind_144_, lean_object* v___f_145_, lean_object* v_____do__lift_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_alloc_closure((void*)(l_IO_println___boxed), 4, 3);
lean_closure_set(v___x_147_, 0, lean_box(0));
lean_closure_set(v___x_147_, 1, v___f_142_);
lean_closure_set(v___x_147_, 2, v_____do__lift_146_);
v___x_148_ = lean_apply_2(v_inst_143_, lean_box(0), v___x_147_);
v___x_149_ = lean_apply_4(v_toBind_144_, lean_box(0), lean_box(0), v___x_148_, v___f_145_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__3(lean_object* v_inst_150_, lean_object* v_toBind_151_, lean_object* v___f_152_, lean_object* v_x_153_, lean_object* v_____s_154_){
_start:
{
lean_object* v_msg_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_msg_155_ = lean_ctor_get(v_x_153_, 1);
lean_inc_ref(v_msg_155_);
lean_dec_ref(v_x_153_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_alloc_closure((void*)(l_Lean_MessageData_format___boxed), 3, 2);
lean_closure_set(v___x_157_, 0, v_msg_155_);
lean_closure_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_alloc_closure((void*)(l_BaseIO_toIO___boxed), 3, 2);
lean_closure_set(v___x_158_, 0, lean_box(0));
lean_closure_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_apply_2(v_inst_150_, lean_box(0), v___x_158_);
v___x_160_ = lean_apply_4(v_toBind_151_, lean_box(0), lean_box(0), v___x_159_, v___f_152_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4(lean_object* v_toPure_161_, lean_object* v___f_162_, lean_object* v_inst_163_, lean_object* v_toBind_164_, lean_object* v_inst_165_, lean_object* v___f_166_, lean_object* v_____do__lift_167_){
_start:
{
lean_object* v_traces_168_; lean_object* v___x_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_traces_168_ = lean_ctor_get(v_____do__lift_167_, 0);
v___x_169_ = lean_box(0);
v___f_170_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_170_, 0, v___x_169_);
lean_closure_set(v___f_170_, 1, v_toPure_161_);
lean_inc_n(v_toBind_164_, 2);
lean_inc(v_inst_163_);
v___f_171_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_171_, 0, v___f_162_);
lean_closure_set(v___f_171_, 1, v_inst_163_);
lean_closure_set(v___f_171_, 2, v_toBind_164_);
lean_closure_set(v___f_171_, 3, v___f_170_);
v___f_172_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__3), 5, 3);
lean_closure_set(v___f_172_, 0, v_inst_163_);
lean_closure_set(v___f_172_, 1, v_toBind_164_);
lean_closure_set(v___f_172_, 2, v___f_171_);
v___x_173_ = l_Lean_PersistentArray_forIn___redArg(v_inst_165_, v_traces_168_, v___x_169_, v___f_172_);
v___x_174_ = lean_apply_4(v_toBind_164_, lean_box(0), lean_box(0), v___x_173_, v___f_166_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg___lam__4___boxed(lean_object* v_toPure_175_, lean_object* v___f_176_, lean_object* v_inst_177_, lean_object* v_toBind_178_, lean_object* v_inst_179_, lean_object* v___f_180_, lean_object* v_____do__lift_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_printTraces___redArg___lam__4(v_toPure_175_, v___f_176_, v_inst_177_, v_toBind_178_, v_inst_179_, v___f_180_, v_____do__lift_181_);
lean_dec_ref(v_____do__lift_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces___redArg(lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_inst_186_){
_start:
{
lean_object* v_toApplicative_187_; lean_object* v_toBind_188_; lean_object* v_getTraceState_189_; lean_object* v_toPure_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___f_193_; lean_object* v___x_194_; 
v_toApplicative_187_ = lean_ctor_get(v_inst_184_, 0);
v_toBind_188_ = lean_ctor_get(v_inst_184_, 1);
lean_inc_n(v_toBind_188_, 2);
v_getTraceState_189_ = lean_ctor_get(v_inst_185_, 1);
lean_inc(v_getTraceState_189_);
lean_dec_ref(v_inst_185_);
v_toPure_190_ = lean_ctor_get(v_toApplicative_187_, 1);
lean_inc_n(v_toPure_190_, 2);
v___f_191_ = ((lean_object*)(l_Lean_printTraces___redArg___closed__0));
v___f_192_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_192_, 0, v_toPure_190_);
v___f_193_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_193_, 0, v_toPure_190_);
lean_closure_set(v___f_193_, 1, v___f_191_);
lean_closure_set(v___f_193_, 2, v_inst_186_);
lean_closure_set(v___f_193_, 3, v_toBind_188_);
lean_closure_set(v___f_193_, 4, v_inst_184_);
lean_closure_set(v___f_193_, 5, v___f_192_);
v___x_194_ = lean_apply_4(v_toBind_188_, lean_box(0), lean_box(0), v_getTraceState_189_, v___f_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_printTraces(lean_object* v_m_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_printTraces___redArg(v_inst_196_, v_inst_197_, v_inst_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0(lean_object* v_x_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_unsigned_to_nat(32u);
v___x_202_ = lean_mk_empty_array_with_capacity(v___x_201_);
lean_dec_ref(v___x_202_);
v___x_203_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__2, &l_Lean_instInhabitedTraceState_default___closed__2_once, _init_l_Lean_instInhabitedTraceState_default___closed__2);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg___lam__0___boxed(lean_object* v_x_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_resetTraceState___redArg___lam__0(v_x_204_);
lean_dec_ref(v_x_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState___redArg(lean_object* v_inst_207_){
_start:
{
lean_object* v_modifyTraceState_208_; lean_object* v___f_209_; lean_object* v___x_210_; 
v_modifyTraceState_208_ = lean_ctor_get(v_inst_207_, 0);
lean_inc(v_modifyTraceState_208_);
lean_dec_ref(v_inst_207_);
v___f_209_ = ((lean_object*)(l_Lean_resetTraceState___redArg___closed__0));
v___x_210_ = lean_apply_1(v_modifyTraceState_208_, v___f_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_resetTraceState(lean_object* v_m_211_, lean_object* v_inst_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_resetTraceState___redArg(v_inst_212_);
return v___x_213_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(lean_object* v_a_214_, lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
uint8_t v___x_216_; 
v___x_216_ = 0;
return v___x_216_;
}
else
{
lean_object* v_key_217_; lean_object* v_tail_218_; uint8_t v___x_219_; 
v_key_217_ = lean_ctor_get(v_x_215_, 0);
v_tail_218_ = lean_ctor_get(v_x_215_, 2);
v___x_219_ = lean_name_eq(v_key_217_, v_a_214_);
if (v___x_219_ == 0)
{
v_x_215_ = v_tail_218_;
goto _start;
}
else
{
return v___x_219_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_214_ = stack[0].m_obj;
lean_object* v_x_215_ = stack[1].m_obj;
uint8_t v_res_221_;
v_res_221_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_214_, v_x_215_);
stack->m_num = v_res_221_;
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(lean_object* v_m_226_, lean_object* v_a_227_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_226_ = stack[0].m_obj;
lean_object* v_a_227_ = stack[1].m_obj;
uint8_t v_res_247_;
v_res_247_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_226_, v_a_227_);
stack->m_num = v_res_247_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg___boxed(lean_object* v_m_248_, lean_object* v_a_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_248_, v_a_249_);
lean_dec(v_a_249_);
lean_dec_ref(v_m_248_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object* v_inherited_252_, lean_object* v_opts_253_, lean_object* v_opt_254_){
_start:
{
lean_object* v_map_260_; lean_object* v___x_261_; 
v_map_260_ = lean_ctor_get(v_opts_253_, 0);
v___x_261_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_260_, v_opt_254_);
if (lean_obj_tag(v___x_261_) == 0)
{
goto v___jp_255_;
}
else
{
lean_object* v_val_262_; 
v_val_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_val_262_);
lean_dec_ref_known(v___x_261_, 1);
if (lean_obj_tag(v_val_262_) == 1)
{
uint8_t v_v_263_; 
v_v_263_ = lean_ctor_get_uint8(v_val_262_, 0);
lean_dec_ref_known(v_val_262_, 0);
return v_v_263_;
}
else
{
lean_dec(v_val_262_);
goto v___jp_255_;
}
}
v___jp_255_:
{
if (lean_obj_tag(v_opt_254_) == 1)
{
lean_object* v_pre_256_; uint8_t v___x_257_; 
v_pre_256_ = lean_ctor_get(v_opt_254_, 0);
v___x_257_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_inherited_252_, v_opt_254_);
if (v___x_257_ == 0)
{
return v___x_257_;
}
else
{
v_opt_254_ = v_pre_256_;
goto _start;
}
}
else
{
uint8_t v___x_259_; 
v___x_259_ = 0;
return v___x_259_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_inherited_252_ = stack[0].m_obj;
lean_object* v_opts_253_ = stack[1].m_obj;
lean_object* v_opt_254_ = stack[2].m_obj;
uint8_t v_res_264_;
v_res_264_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_252_, v_opts_253_, v_opt_254_);
stack->m_num = v_res_264_;
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(lean_object* v_00_u03b2_270_, lean_object* v_m_271_, lean_object* v_a_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___redArg(v_m_271_, v_a_272_);
return v___x_273_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_271_ = stack[1].m_obj;
lean_object* v_a_272_ = stack[2].m_obj;
uint8_t v_res_274_;
v_res_274_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(lean_box(0), v_m_271_, v_a_272_);
stack->m_num = v_res_274_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0___boxed(lean_object* v_00_u03b2_275_, lean_object* v_m_276_, lean_object* v_a_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0(v_00_u03b2_275_, v_m_276_, v_a_277_);
lean_dec(v_a_277_);
lean_dec_ref(v_m_276_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(lean_object* v_00_u03b2_280_, lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_281_, v_x_282_);
return v___x_283_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_281_ = stack[1].m_obj;
lean_object* v_x_282_ = stack[2].m_obj;
uint8_t v_res_284_;
v_res_284_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(lean_box(0), v_a_281_, v_x_282_);
stack->m_num = v_res_284_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_285_, lean_object* v_a_286_, lean_object* v_x_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0(v_00_u03b2_285_, v_a_286_, v_x_287_);
lean_dec(v_x_287_);
lean_dec(v_a_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
uint8_t l_Lean_checkTraceOption(lean_object* v_inherited_293_, lean_object* v_opts_294_, lean_object* v_cls_295_){
_start:
{
uint8_t v_hasTrace_296_; 
v_hasTrace_296_ = lean_ctor_get_uint8(v_opts_294_, sizeof(void*)*1);
if (v_hasTrace_296_ == 0)
{
lean_dec(v_cls_295_);
return v_hasTrace_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_297_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_298_ = l_Lean_Name_append(v___x_297_, v_cls_295_);
v___x_299_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inherited_293_, v_opts_294_, v___x_298_);
lean_dec(v___x_298_);
return v___x_299_;
}
}
}
LEAN_EXPORT void l_Lean_checkTraceOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_inherited_293_ = stack[0].m_obj;
lean_object* v_opts_294_ = stack[1].m_obj;
lean_object* v_cls_295_ = stack[2].m_obj;
uint8_t v_res_300_;
v_res_300_ = l_Lean_checkTraceOption(v_inherited_293_, v_opts_294_, v_cls_295_);
stack->m_num = v_res_300_;
}
LEAN_EXPORT lean_object* l_Lean_checkTraceOption___boxed(lean_object* v_inherited_301_, lean_object* v_opts_302_, lean_object* v_cls_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Lean_checkTraceOption(v_inherited_301_, v_opts_302_, v_cls_303_);
lean_dec_ref(v_opts_302_);
lean_dec_ref(v_inherited_301_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0(lean_object* v_toPure_306_, lean_object* v_cls_307_, lean_object* v_____do__lift_308_, lean_object* v_____do__lift_309_){
_start:
{
uint8_t v_hasTrace_310_; 
v_hasTrace_310_ = lean_ctor_get_uint8(v_____do__lift_309_, sizeof(void*)*1);
if (v_hasTrace_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_cls_307_);
v___x_311_ = lean_box(v_hasTrace_310_);
v___x_312_ = lean_apply_2(v_toPure_306_, lean_box(0), v___x_311_);
return v___x_312_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_313_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_314_ = l_Lean_Name_append(v___x_313_, v_cls_307_);
v___x_315_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_308_, v_____do__lift_309_, v___x_314_);
lean_dec(v___x_314_);
v___x_316_ = lean_box(v___x_315_);
v___x_317_ = lean_apply_2(v_toPure_306_, lean_box(0), v___x_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__0___boxed(lean_object* v_toPure_318_, lean_object* v_cls_319_, lean_object* v_____do__lift_320_, lean_object* v_____do__lift_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_isTracingEnabledFor___redArg___lam__0(v_toPure_318_, v_cls_319_, v_____do__lift_320_, v_____do__lift_321_);
lean_dec_ref(v_____do__lift_321_);
lean_dec_ref(v_____do__lift_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg___lam__1(lean_object* v_inst_323_, lean_object* v_toPure_324_, lean_object* v_cls_325_, lean_object* v_toBind_326_, lean_object* v_____do__lift_327_){
_start:
{
lean_object* v_getOptionsUnrestricted_328_; lean_object* v___f_329_; lean_object* v___x_330_; 
v_getOptionsUnrestricted_328_ = lean_ctor_get(v_inst_323_, 1);
lean_inc(v_getOptionsUnrestricted_328_);
lean_dec_ref(v_inst_323_);
v___f_329_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_329_, 0, v_toPure_324_);
lean_closure_set(v___f_329_, 1, v_cls_325_);
lean_closure_set(v___f_329_, 2, v_____do__lift_327_);
v___x_330_ = lean_apply_4(v_toBind_326_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_328_, v___f_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_cls_334_){
_start:
{
lean_object* v_toApplicative_335_; lean_object* v_toBind_336_; lean_object* v_getInheritedTraceOptions_337_; lean_object* v_toPure_338_; lean_object* v___f_339_; lean_object* v___x_340_; 
v_toApplicative_335_ = lean_ctor_get(v_inst_331_, 0);
lean_inc_ref(v_toApplicative_335_);
v_toBind_336_ = lean_ctor_get(v_inst_331_, 1);
lean_inc_n(v_toBind_336_, 2);
lean_dec_ref(v_inst_331_);
v_getInheritedTraceOptions_337_ = lean_ctor_get(v_inst_332_, 2);
lean_inc(v_getInheritedTraceOptions_337_);
lean_dec_ref(v_inst_332_);
v_toPure_338_ = lean_ctor_get(v_toApplicative_335_, 1);
lean_inc(v_toPure_338_);
lean_dec_ref(v_toApplicative_335_);
v___f_339_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_339_, 0, v_inst_333_);
lean_closure_set(v___f_339_, 1, v_toPure_338_);
lean_closure_set(v___f_339_, 2, v_cls_334_);
lean_closure_set(v___f_339_, 3, v_toBind_336_);
v___x_340_ = lean_apply_4(v_toBind_336_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_337_, v___f_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor(lean_object* v_m_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_cls_345_){
_start:
{
lean_object* v_toApplicative_346_; lean_object* v_toBind_347_; lean_object* v_getInheritedTraceOptions_348_; lean_object* v_toPure_349_; lean_object* v___f_350_; lean_object* v___x_351_; 
v_toApplicative_346_ = lean_ctor_get(v_inst_342_, 0);
lean_inc_ref(v_toApplicative_346_);
v_toBind_347_ = lean_ctor_get(v_inst_342_, 1);
lean_inc_n(v_toBind_347_, 2);
lean_dec_ref(v_inst_342_);
v_getInheritedTraceOptions_348_ = lean_ctor_get(v_inst_343_, 2);
lean_inc(v_getInheritedTraceOptions_348_);
lean_dec_ref(v_inst_343_);
v_toPure_349_ = lean_ctor_get(v_toApplicative_346_, 1);
lean_inc(v_toPure_349_);
lean_dec_ref(v_toApplicative_346_);
v___f_350_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_350_, 0, v_inst_344_);
lean_closure_set(v___f_350_, 1, v_toPure_349_);
lean_closure_set(v___f_350_, 2, v_cls_345_);
lean_closure_set(v___f_350_, 3, v_toBind_347_);
v___x_351_ = lean_apply_4(v_toBind_347_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_348_, v___f_350_);
return v___x_351_;
}
}
uint8_t lean_is_trace_class_enabled(lean_object* v_opts_352_, lean_object* v_cls_353_){
_start:
{
uint8_t v_hasTrace_355_; 
v_hasTrace_355_ = lean_ctor_get_uint8(v_opts_352_, sizeof(void*)*1);
if (v_hasTrace_355_ == 0)
{
lean_dec(v_cls_353_);
lean_dec_ref(v_opts_352_);
return v_hasTrace_355_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_356_ = l_Lean_inheritedTraceOptions;
v___x_357_ = lean_st_ref_get(v___x_356_);
v___x_358_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_359_ = l_Lean_Name_append(v___x_358_, v_cls_353_);
v___x_360_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_357_, v_opts_352_, v___x_359_);
lean_dec(v___x_359_);
lean_dec_ref(v_opts_352_);
lean_dec(v___x_357_);
return v___x_360_;
}
}
}
LEAN_EXPORT void lean_is_trace_class_enabled_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_352_ = stack[0].m_obj;
lean_object* v_cls_353_ = stack[1].m_obj;
uint8_t v_res_361_;
v_res_361_ = lean_is_trace_class_enabled(v_opts_352_, v_cls_353_);
stack->m_num = v_res_361_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_isTracingEnabledForExport___boxed(lean_object* v_opts_362_, lean_object* v_cls_363_, lean_object* v_a_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = lean_is_trace_class_enabled(v_opts_362_, v_cls_363_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg___lam__0(lean_object* v_toPure_367_, lean_object* v_s_368_){
_start:
{
lean_object* v_traces_369_; lean_object* v___x_370_; 
v_traces_369_ = lean_ctor_get(v_s_368_, 0);
lean_inc_ref(v_traces_369_);
lean_dec_ref(v_s_368_);
v___x_370_ = lean_apply_2(v_toPure_367_, lean_box(0), v_traces_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_getTraces___redArg(lean_object* v_inst_371_, lean_object* v_inst_372_){
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
LEAN_EXPORT lean_object* l_Lean_getTraces(lean_object* v_m_379_, lean_object* v_inst_380_, lean_object* v_inst_381_){
_start:
{
lean_object* v_toApplicative_382_; lean_object* v_toBind_383_; lean_object* v_getTraceState_384_; lean_object* v_toPure_385_; lean_object* v___f_386_; lean_object* v___x_387_; 
v_toApplicative_382_ = lean_ctor_get(v_inst_380_, 0);
lean_inc_ref(v_toApplicative_382_);
v_toBind_383_ = lean_ctor_get(v_inst_380_, 1);
lean_inc(v_toBind_383_);
lean_dec_ref(v_inst_380_);
v_getTraceState_384_ = lean_ctor_get(v_inst_381_, 1);
lean_inc(v_getTraceState_384_);
lean_dec_ref(v_inst_381_);
v_toPure_385_ = lean_ctor_get(v_toApplicative_382_, 1);
lean_inc(v_toPure_385_);
lean_dec_ref(v_toApplicative_382_);
v___f_386_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_386_, 0, v_toPure_385_);
v___x_387_ = lean_apply_4(v_toBind_383_, lean_box(0), lean_box(0), v_getTraceState_384_, v___f_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg___lam__0(lean_object* v_f_388_, lean_object* v_s_389_){
_start:
{
uint64_t v_tid_390_; lean_object* v_traces_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_399_; 
v_tid_390_ = lean_ctor_get_uint64(v_s_389_, sizeof(void*)*1);
v_traces_391_ = lean_ctor_get(v_s_389_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v_s_389_);
if (v_isSharedCheck_399_ == 0)
{
v___x_393_ = v_s_389_;
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_traces_391_);
lean_dec(v_s_389_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_apply_1(v_f_388_, v_traces_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_395_);
v___x_397_ = v___x_393_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
lean_ctor_set_uint64(v_reuseFailAlloc_398_, sizeof(void*)*1, v_tid_390_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_modifyTraces___redArg(lean_object* v_inst_400_, lean_object* v_f_401_){
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
LEAN_EXPORT lean_object* l_Lean_modifyTraces(lean_object* v_m_405_, lean_object* v_inst_406_, lean_object* v_f_407_){
_start:
{
lean_object* v_modifyTraceState_408_; lean_object* v___f_409_; lean_object* v___x_410_; 
v_modifyTraceState_408_ = lean_ctor_get(v_inst_406_, 0);
lean_inc(v_modifyTraceState_408_);
lean_dec_ref(v_inst_406_);
v___f_409_ = lean_alloc_closure((void*)(l_Lean_modifyTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_409_, 0, v_f_407_);
v___x_410_ = lean_apply_1(v_modifyTraceState_408_, v___f_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0(lean_object* v_s_411_, lean_object* v_x_412_){
_start:
{
lean_inc_ref(v_s_411_);
return v_s_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg___lam__0___boxed(lean_object* v_s_413_, lean_object* v_x_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_setTraceState___redArg___lam__0(v_s_413_, v_x_414_);
lean_dec_ref(v_x_414_);
lean_dec_ref(v_s_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_setTraceState___redArg(lean_object* v_inst_416_, lean_object* v_s_417_){
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
LEAN_EXPORT lean_object* l_Lean_setTraceState(lean_object* v_m_421_, lean_object* v_inst_422_, lean_object* v_s_423_){
_start:
{
lean_object* v_modifyTraceState_424_; lean_object* v___f_425_; lean_object* v___x_426_; 
v_modifyTraceState_424_ = lean_ctor_get(v_inst_422_, 0);
lean_inc(v_modifyTraceState_424_);
lean_dec_ref(v_inst_422_);
v___f_425_ = lean_alloc_closure((void*)(l_Lean_setTraceState___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_425_, 0, v_s_423_);
v___x_426_ = lean_apply_1(v_modifyTraceState_424_, v___f_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__0(lean_object* v_s_427_){
_start:
{
uint64_t v_tid_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_438_; 
v_tid_428_ = lean_ctor_get_uint64(v_s_427_, sizeof(void*)*1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_s_427_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v_s_427_, 0);
lean_dec(v_unused_439_);
v___x_430_ = v_s_427_;
v_isShared_431_ = v_isSharedCheck_438_;
goto v_resetjp_429_;
}
else
{
lean_dec(v_s_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_438_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_432_ = lean_unsigned_to_nat(32u);
v___x_433_ = lean_mk_empty_array_with_capacity(v___x_432_);
lean_dec_ref(v___x_433_);
v___x_434_ = lean_obj_once(&l_Lean_instInhabitedTraceState_default___closed__1, &l_Lean_instInhabitedTraceState_default___closed__1_once, _init_l_Lean_instInhabitedTraceState_default___closed__1);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_434_);
v___x_436_ = v___x_430_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
lean_ctor_set_uint64(v_reuseFailAlloc_437_, sizeof(void*)*1, v_tid_428_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1(lean_object* v_toPure_440_, lean_object* v_oldTraces_441_, lean_object* v_____r_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = lean_apply_2(v_toPure_440_, lean_box(0), v_oldTraces_441_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2(lean_object* v_toPure_444_, lean_object* v_modifyTraceState_445_, lean_object* v___f_446_, lean_object* v_toBind_447_, lean_object* v_oldTraces_448_){
_start:
{
lean_object* v___f_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___f_449_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_449_, 0, v_toPure_444_);
lean_closure_set(v___f_449_, 1, v_oldTraces_448_);
v___x_450_ = lean_apply_1(v_modifyTraceState_445_, v___f_446_);
v___x_451_ = lean_apply_4(v_toBind_447_, lean_box(0), lean_box(0), v___x_450_, v___f_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(lean_object* v_inst_453_, lean_object* v_inst_454_){
_start:
{
lean_object* v_toApplicative_455_; lean_object* v_toBind_456_; lean_object* v_modifyTraceState_457_; lean_object* v_getTraceState_458_; lean_object* v_toPure_459_; lean_object* v___f_460_; lean_object* v___f_461_; lean_object* v___f_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_toApplicative_455_ = lean_ctor_get(v_inst_453_, 0);
lean_inc_ref(v_toApplicative_455_);
v_toBind_456_ = lean_ctor_get(v_inst_453_, 1);
lean_inc_n(v_toBind_456_, 3);
lean_dec_ref(v_inst_453_);
v_modifyTraceState_457_ = lean_ctor_get(v_inst_454_, 0);
lean_inc(v_modifyTraceState_457_);
v_getTraceState_458_ = lean_ctor_get(v_inst_454_, 1);
lean_inc(v_getTraceState_458_);
lean_dec_ref(v_inst_454_);
v_toPure_459_ = lean_ctor_get(v_toApplicative_455_, 1);
lean_inc_n(v_toPure_459_, 2);
lean_dec_ref(v_toApplicative_455_);
v___f_460_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___closed__0));
v___f_461_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg___lam__2), 5, 4);
lean_closure_set(v___f_461_, 0, v_toPure_459_);
lean_closure_set(v___f_461_, 1, v_modifyTraceState_457_);
lean_closure_set(v___f_461_, 2, v___f_460_);
lean_closure_set(v___f_461_, 3, v_toBind_456_);
v___f_462_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_462_, 0, v_toPure_459_);
v___x_463_ = lean_apply_4(v_toBind_456_, lean_box(0), lean_box(0), v_getTraceState_458_, v___f_462_);
v___x_464_ = lean_apply_4(v_toBind_456_, lean_box(0), lean_box(0), v___x_463_, v___f_461_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object* v_m_465_, lean_object* v_inst_466_, lean_object* v_inst_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_466_, v_inst_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__0(lean_object* v_ref_469_, lean_object* v_msg_470_, lean_object* v_s_471_){
_start:
{
uint64_t v_tid_472_; lean_object* v_traces_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_482_; 
v_tid_472_ = lean_ctor_get_uint64(v_s_471_, sizeof(void*)*1);
v_traces_473_ = lean_ctor_get(v_s_471_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v_s_471_);
if (v_isSharedCheck_482_ == 0)
{
v___x_475_ = v_s_471_;
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_traces_473_);
lean_dec(v_s_471_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v_ref_469_);
lean_ctor_set(v___x_477_, 1, v_msg_470_);
v___x_478_ = l_Lean_PersistentArray_push___redArg(v_traces_473_, v___x_477_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_478_);
v___x_480_ = v___x_475_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
lean_ctor_set_uint64(v_reuseFailAlloc_481_, sizeof(void*)*1, v_tid_472_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__1(lean_object* v_inst_483_, lean_object* v_ref_484_, lean_object* v_msg_485_){
_start:
{
lean_object* v_modifyTraceState_486_; lean_object* v___f_487_; lean_object* v___x_488_; 
v_modifyTraceState_486_ = lean_ctor_get(v_inst_483_, 0);
lean_inc(v_modifyTraceState_486_);
lean_dec_ref(v_inst_483_);
v___f_487_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__0), 3, 2);
lean_closure_set(v___f_487_, 0, v_ref_484_);
lean_closure_set(v___f_487_, 1, v_msg_485_);
v___x_488_ = lean_apply_1(v_modifyTraceState_486_, v___f_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg___lam__2(lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_msg_491_, lean_object* v_toBind_492_, lean_object* v_ref_493_){
_start:
{
lean_object* v___f_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___f_494_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__1), 3, 2);
lean_closure_set(v___f_494_, 0, v_inst_489_);
lean_closure_set(v___f_494_, 1, v_ref_493_);
v___x_495_ = lean_apply_1(v_inst_490_, v_msg_491_);
v___x_496_ = lean_apply_4(v_toBind_492_, lean_box(0), lean_box(0), v___x_495_, v___f_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace___redArg(lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_msg_501_){
_start:
{
lean_object* v_toBind_502_; lean_object* v_getRef_503_; lean_object* v___f_504_; lean_object* v___x_505_; 
v_toBind_502_ = lean_ctor_get(v_inst_497_, 1);
lean_inc_n(v_toBind_502_, 2);
lean_dec_ref(v_inst_497_);
v_getRef_503_ = lean_ctor_get(v_inst_499_, 0);
lean_inc(v_getRef_503_);
lean_dec_ref(v_inst_499_);
v___f_504_ = lean_alloc_closure((void*)(l_Lean_addRawTrace___redArg___lam__2), 5, 4);
lean_closure_set(v___f_504_, 0, v_inst_498_);
lean_closure_set(v___f_504_, 1, v_inst_500_);
lean_closure_set(v___f_504_, 2, v_msg_501_);
lean_closure_set(v___f_504_, 3, v_toBind_502_);
v___x_505_ = lean_apply_4(v_toBind_502_, lean_box(0), lean_box(0), v_getRef_503_, v___f_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addRawTrace(lean_object* v_m_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_msg_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_addRawTrace___redArg(v_inst_507_, v_inst_508_, v_inst_509_, v_inst_510_, v_msg_511_);
return v___x_512_;
}
}
static double _init_l_Lean_addTrace___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_513_; double v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_float_of_nat(v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__0(lean_object* v_cls_518_, lean_object* v_msg_519_, lean_object* v_ref_520_, lean_object* v_s_521_){
_start:
{
uint64_t v_tid_522_; lean_object* v_traces_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_539_; 
v_tid_522_ = lean_ctor_get_uint64(v_s_521_, sizeof(void*)*1);
v_traces_523_ = lean_ctor_get(v_s_521_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v_s_521_);
if (v_isSharedCheck_539_ == 0)
{
v___x_525_ = v_s_521_;
v_isShared_526_ = v_isSharedCheck_539_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_traces_523_);
lean_dec(v_s_521_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_539_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; double v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_527_ = lean_box(0);
v___x_528_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
v___x_529_ = 0;
v___x_530_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_531_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_531_, 0, v_cls_518_);
lean_ctor_set(v___x_531_, 1, v___x_527_);
lean_ctor_set(v___x_531_, 2, v___x_530_);
lean_ctor_set_float(v___x_531_, sizeof(void*)*3, v___x_528_);
lean_ctor_set_float(v___x_531_, sizeof(void*)*3 + 8, v___x_528_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*3 + 16, v___x_529_);
v___x_532_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
v___x_533_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v_msg_519_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v_ref_520_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = l_Lean_PersistentArray_push___redArg(v_traces_523_, v___x_534_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_535_);
v___x_537_ = v___x_525_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
lean_ctor_set_uint64(v_reuseFailAlloc_538_, sizeof(void*)*1, v_tid_522_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__1(lean_object* v_inst_540_, lean_object* v_cls_541_, lean_object* v_ref_542_, lean_object* v_msg_543_){
_start:
{
lean_object* v_modifyTraceState_544_; lean_object* v___f_545_; lean_object* v___x_546_; 
v_modifyTraceState_544_ = lean_ctor_get(v_inst_540_, 0);
lean_inc(v_modifyTraceState_544_);
lean_dec_ref(v_inst_540_);
v___f_545_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__0), 4, 3);
lean_closure_set(v___f_545_, 0, v_cls_541_);
lean_closure_set(v___f_545_, 1, v_msg_543_);
lean_closure_set(v___f_545_, 2, v_ref_542_);
v___x_546_ = lean_apply_1(v_modifyTraceState_544_, v___f_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg___lam__2(lean_object* v_inst_547_, lean_object* v_cls_548_, lean_object* v_inst_549_, lean_object* v_msg_550_, lean_object* v_toBind_551_, lean_object* v_ref_552_){
_start:
{
lean_object* v___f_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___f_553_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__1), 4, 3);
lean_closure_set(v___f_553_, 0, v_inst_547_);
lean_closure_set(v___f_553_, 1, v_cls_548_);
lean_closure_set(v___f_553_, 2, v_ref_552_);
v___x_554_ = lean_apply_1(v_inst_549_, v_msg_550_);
v___x_555_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_554_, v___f_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___redArg(lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_cls_560_, lean_object* v_msg_561_){
_start:
{
lean_object* v_toBind_562_; lean_object* v_getRef_563_; lean_object* v___f_564_; lean_object* v___x_565_; 
v_toBind_562_ = lean_ctor_get(v_inst_556_, 1);
lean_inc_n(v_toBind_562_, 2);
lean_dec_ref(v_inst_556_);
v_getRef_563_ = lean_ctor_get(v_inst_558_, 0);
lean_inc(v_getRef_563_);
lean_dec_ref(v_inst_558_);
v___f_564_ = lean_alloc_closure((void*)(l_Lean_addTrace___redArg___lam__2), 6, 5);
lean_closure_set(v___f_564_, 0, v_inst_557_);
lean_closure_set(v___f_564_, 1, v_cls_560_);
lean_closure_set(v___f_564_, 2, v_inst_559_);
lean_closure_set(v___f_564_, 3, v_msg_561_);
lean_closure_set(v___f_564_, 4, v_toBind_562_);
v___x_565_ = lean_apply_4(v_toBind_562_, lean_box(0), lean_box(0), v_getRef_563_, v___f_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace(lean_object* v_m_566_, lean_object* v_inst_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_inst_570_, lean_object* v_cls_571_, lean_object* v_msg_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_addTrace___redArg(v_inst_567_, v_inst_568_, v_inst_569_, v_inst_570_, v_cls_571_, v_msg_572_);
return v___x_573_;
}
}
lean_object* l_Lean_trace___redArg___lam__0(lean_object* v_toPure_574_, lean_object* v_msg_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_cls_580_, uint8_t v_____do__lift_581_){
_start:
{
if (v_____do__lift_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_cls_580_);
lean_dec(v_inst_579_);
lean_dec_ref(v_inst_578_);
lean_dec_ref(v_inst_577_);
lean_dec_ref(v_inst_576_);
lean_dec_ref(v_msg_575_);
v___x_582_ = lean_box(0);
v___x_583_ = lean_apply_2(v_toPure_574_, lean_box(0), v___x_582_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec(v_toPure_574_);
v___x_584_ = lean_box(0);
v___x_585_ = lean_apply_1(v_msg_575_, v___x_584_);
v___x_586_ = l_Lean_addTrace___redArg(v_inst_576_, v_inst_577_, v_inst_578_, v_inst_579_, v_cls_580_, v___x_585_);
return v___x_586_;
}
}
}
LEAN_EXPORT void l_Lean_trace___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_574_ = stack[0].m_obj;
lean_object* v_msg_575_ = stack[1].m_obj;
lean_object* v_inst_576_ = stack[2].m_obj;
lean_object* v_inst_577_ = stack[3].m_obj;
lean_object* v_inst_578_ = stack[4].m_obj;
lean_object* v_inst_579_ = stack[5].m_obj;
lean_object* v_cls_580_ = stack[6].m_obj;
uint8_t v_____do__lift_581_ = stack[7].m_num;
lean_object* v_res_587_;
v_res_587_ = l_Lean_trace___redArg___lam__0(v_toPure_574_, v_msg_575_, v_inst_576_, v_inst_577_, v_inst_578_, v_inst_579_, v_cls_580_, v_____do__lift_581_);
stack->m_obj
 = v_res_587_;
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg___lam__0___boxed(lean_object* v_toPure_588_, lean_object* v_msg_589_, lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_cls_594_, lean_object* v_____do__lift_595_){
_start:
{
uint8_t v_____do__lift_126__boxed_596_; lean_object* v_res_597_; 
v_____do__lift_126__boxed_596_ = lean_unbox(v_____do__lift_595_);
v_res_597_ = l_Lean_trace___redArg___lam__0(v_toPure_588_, v_msg_589_, v_inst_590_, v_inst_591_, v_inst_592_, v_inst_593_, v_cls_594_, v_____do__lift_126__boxed_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace___redArg(lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_cls_603_, lean_object* v_msg_604_){
_start:
{
lean_object* v_toApplicative_605_; lean_object* v_toBind_606_; lean_object* v_getInheritedTraceOptions_607_; lean_object* v_toPure_608_; lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_toApplicative_605_ = lean_ctor_get(v_inst_598_, 0);
v_toBind_606_ = lean_ctor_get(v_inst_598_, 1);
lean_inc_n(v_toBind_606_, 3);
v_getInheritedTraceOptions_607_ = lean_ctor_get(v_inst_599_, 2);
lean_inc(v_getInheritedTraceOptions_607_);
v_toPure_608_ = lean_ctor_get(v_toApplicative_605_, 1);
lean_inc_n(v_toPure_608_, 2);
lean_inc(v_cls_603_);
v___f_609_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_609_, 0, v_toPure_608_);
lean_closure_set(v___f_609_, 1, v_msg_604_);
lean_closure_set(v___f_609_, 2, v_inst_598_);
lean_closure_set(v___f_609_, 3, v_inst_599_);
lean_closure_set(v___f_609_, 4, v_inst_600_);
lean_closure_set(v___f_609_, 5, v_inst_601_);
lean_closure_set(v___f_609_, 6, v_cls_603_);
v___f_610_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_610_, 0, v_inst_602_);
lean_closure_set(v___f_610_, 1, v_toPure_608_);
lean_closure_set(v___f_610_, 2, v_cls_603_);
lean_closure_set(v___f_610_, 3, v_toBind_606_);
v___x_611_ = lean_apply_4(v_toBind_606_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_607_, v___f_610_);
v___x_612_ = lean_apply_4(v_toBind_606_, lean_box(0), lean_box(0), v___x_611_, v___f_609_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_trace(lean_object* v_m_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_cls_619_, lean_object* v_msg_620_){
_start:
{
lean_object* v_toApplicative_621_; lean_object* v_toBind_622_; lean_object* v_getInheritedTraceOptions_623_; lean_object* v_toPure_624_; lean_object* v___f_625_; lean_object* v___f_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_toApplicative_621_ = lean_ctor_get(v_inst_614_, 0);
v_toBind_622_ = lean_ctor_get(v_inst_614_, 1);
lean_inc_n(v_toBind_622_, 3);
v_getInheritedTraceOptions_623_ = lean_ctor_get(v_inst_615_, 2);
lean_inc(v_getInheritedTraceOptions_623_);
v_toPure_624_ = lean_ctor_get(v_toApplicative_621_, 1);
lean_inc_n(v_toPure_624_, 2);
lean_inc(v_cls_619_);
v___f_625_ = lean_alloc_closure((void*)(l_Lean_trace___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_625_, 0, v_toPure_624_);
lean_closure_set(v___f_625_, 1, v_msg_620_);
lean_closure_set(v___f_625_, 2, v_inst_614_);
lean_closure_set(v___f_625_, 3, v_inst_615_);
lean_closure_set(v___f_625_, 4, v_inst_616_);
lean_closure_set(v___f_625_, 5, v_inst_617_);
lean_closure_set(v___f_625_, 6, v_cls_619_);
v___f_626_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_626_, 0, v_inst_618_);
lean_closure_set(v___f_626_, 1, v_toPure_624_);
lean_closure_set(v___f_626_, 2, v_cls_619_);
lean_closure_set(v___f_626_, 3, v_toBind_622_);
v___x_627_ = lean_apply_4(v_toBind_622_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_623_, v___f_626_);
v___x_628_ = lean_apply_4(v_toBind_622_, lean_box(0), lean_box(0), v___x_627_, v___f_625_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__0(lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_cls_633_, lean_object* v_msg_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_addTrace___redArg(v_inst_629_, v_inst_630_, v_inst_631_, v_inst_632_, v_cls_633_, v_msg_634_);
return v___x_635_;
}
}
lean_object* l_Lean_traceM___redArg___lam__1(lean_object* v_toPure_636_, lean_object* v_toBind_637_, lean_object* v_mkMsg_638_, lean_object* v___f_639_, uint8_t v_____do__lift_640_){
_start:
{
if (v_____do__lift_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec(v___f_639_);
lean_dec(v_mkMsg_638_);
lean_dec(v_toBind_637_);
v___x_641_ = lean_box(0);
v___x_642_ = lean_apply_2(v_toPure_636_, lean_box(0), v___x_641_);
return v___x_642_;
}
else
{
lean_object* v___x_643_; 
lean_dec(v_toPure_636_);
v___x_643_ = lean_apply_4(v_toBind_637_, lean_box(0), lean_box(0), v_mkMsg_638_, v___f_639_);
return v___x_643_;
}
}
}
LEAN_EXPORT void l_Lean_traceM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_636_ = stack[0].m_obj;
lean_object* v_toBind_637_ = stack[1].m_obj;
lean_object* v_mkMsg_638_ = stack[2].m_obj;
lean_object* v___f_639_ = stack[3].m_obj;
uint8_t v_____do__lift_640_ = stack[4].m_num;
lean_object* v_res_644_;
v_res_644_ = l_Lean_traceM___redArg___lam__1(v_toPure_636_, v_toBind_637_, v_mkMsg_638_, v___f_639_, v_____do__lift_640_);
stack->m_obj
 = v_res_644_;
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg___lam__1___boxed(lean_object* v_toPure_645_, lean_object* v_toBind_646_, lean_object* v_mkMsg_647_, lean_object* v___f_648_, lean_object* v_____do__lift_649_){
_start:
{
uint8_t v_____do__lift_137__boxed_650_; lean_object* v_res_651_; 
v_____do__lift_137__boxed_650_ = lean_unbox(v_____do__lift_649_);
v_res_651_ = l_Lean_traceM___redArg___lam__1(v_toPure_645_, v_toBind_646_, v_mkMsg_647_, v___f_648_, v_____do__lift_137__boxed_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM___redArg(lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_cls_657_, lean_object* v_mkMsg_658_){
_start:
{
lean_object* v_toApplicative_659_; lean_object* v_toBind_660_; lean_object* v_getInheritedTraceOptions_661_; lean_object* v_toPure_662_; lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___f_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_toApplicative_659_ = lean_ctor_get(v_inst_652_, 0);
v_toBind_660_ = lean_ctor_get(v_inst_652_, 1);
lean_inc_n(v_toBind_660_, 4);
v_getInheritedTraceOptions_661_ = lean_ctor_get(v_inst_653_, 2);
lean_inc(v_getInheritedTraceOptions_661_);
v_toPure_662_ = lean_ctor_get(v_toApplicative_659_, 1);
lean_inc_n(v_toPure_662_, 2);
lean_inc(v_cls_657_);
v___f_663_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_663_, 0, v_inst_652_);
lean_closure_set(v___f_663_, 1, v_inst_653_);
lean_closure_set(v___f_663_, 2, v_inst_654_);
lean_closure_set(v___f_663_, 3, v_inst_655_);
lean_closure_set(v___f_663_, 4, v_cls_657_);
v___f_664_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_664_, 0, v_toPure_662_);
lean_closure_set(v___f_664_, 1, v_toBind_660_);
lean_closure_set(v___f_664_, 2, v_mkMsg_658_);
lean_closure_set(v___f_664_, 3, v___f_663_);
v___f_665_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_665_, 0, v_inst_656_);
lean_closure_set(v___f_665_, 1, v_toPure_662_);
lean_closure_set(v___f_665_, 2, v_cls_657_);
lean_closure_set(v___f_665_, 3, v_toBind_660_);
v___x_666_ = lean_apply_4(v_toBind_660_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_661_, v___f_665_);
v___x_667_ = lean_apply_4(v_toBind_660_, lean_box(0), lean_box(0), v___x_666_, v___f_664_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_traceM(lean_object* v_m_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_cls_674_, lean_object* v_mkMsg_675_){
_start:
{
lean_object* v_toApplicative_676_; lean_object* v_toBind_677_; lean_object* v_getInheritedTraceOptions_678_; lean_object* v_toPure_679_; lean_object* v___f_680_; lean_object* v___f_681_; lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_toApplicative_676_ = lean_ctor_get(v_inst_669_, 0);
v_toBind_677_ = lean_ctor_get(v_inst_669_, 1);
lean_inc_n(v_toBind_677_, 4);
v_getInheritedTraceOptions_678_ = lean_ctor_get(v_inst_670_, 2);
lean_inc(v_getInheritedTraceOptions_678_);
v_toPure_679_ = lean_ctor_get(v_toApplicative_676_, 1);
lean_inc_n(v_toPure_679_, 2);
lean_inc(v_cls_674_);
v___f_680_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_680_, 0, v_inst_669_);
lean_closure_set(v___f_680_, 1, v_inst_670_);
lean_closure_set(v___f_680_, 2, v_inst_671_);
lean_closure_set(v___f_680_, 3, v_inst_672_);
lean_closure_set(v___f_680_, 4, v_cls_674_);
v___f_681_ = lean_alloc_closure((void*)(l_Lean_traceM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_681_, 0, v_toPure_679_);
lean_closure_set(v___f_681_, 1, v_toBind_677_);
lean_closure_set(v___f_681_, 2, v_mkMsg_675_);
lean_closure_set(v___f_681_, 3, v___f_680_);
v___f_682_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__1), 5, 4);
lean_closure_set(v___f_682_, 0, v_inst_673_);
lean_closure_set(v___f_682_, 1, v_toPure_679_);
lean_closure_set(v___f_682_, 2, v_cls_674_);
lean_closure_set(v___f_682_, 3, v_toBind_677_);
v___x_683_ = lean_apply_4(v_toBind_677_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_678_, v___f_682_);
v___x_684_ = lean_apply_4(v_toBind_677_, lean_box(0), lean_box(0), v___x_683_, v___f_681_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(lean_object* v_x_685_){
_start:
{
lean_object* v_msg_686_; 
v_msg_686_ = lean_ctor_get(v_x_685_, 1);
lean_inc_ref(v_msg_686_);
return v_msg_686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1___boxed(lean_object* v_x_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__1(v_x_687_);
lean_dec_ref(v_x_687_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0(lean_object* v_ref_689_, lean_object* v_msg_690_, lean_object* v_oldTraces_691_, lean_object* v_s_692_){
_start:
{
uint64_t v_tid_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_702_; 
v_tid_693_ = lean_ctor_get_uint64(v_s_692_, sizeof(void*)*1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_s_692_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v_s_692_, 0);
lean_dec(v_unused_703_);
v___x_695_ = v_s_692_;
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
else
{
lean_dec(v_s_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v_ref_689_);
lean_ctor_set(v___x_697_, 1, v_msg_690_);
v___x_698_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_691_, v___x_697_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_698_);
v___x_700_ = v___x_695_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
lean_ctor_set_uint64(v_reuseFailAlloc_701_, sizeof(void*)*1, v_tid_693_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2(lean_object* v_ref_704_, lean_object* v_oldTraces_705_, lean_object* v_modifyTraceState_706_, lean_object* v_msg_707_){
_start:
{
lean_object* v___f_708_; lean_object* v___x_709_; 
v___f_708_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__0), 4, 3);
lean_closure_set(v___f_708_, 0, v_ref_704_);
lean_closure_set(v___f_708_, 1, v_msg_707_);
lean_closure_set(v___f_708_, 2, v_oldTraces_705_);
v___x_709_ = lean_apply_1(v_modifyTraceState_706_, v___f_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(lean_object* v___f_729_, lean_object* v_data_730_, lean_object* v_msg_731_, lean_object* v_inst_732_, lean_object* v_toBind_733_, lean_object* v___f_734_, lean_object* v_____do__lift_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; size_t v_sz_738_; size_t v___x_739_; lean_object* v___x_740_; lean_object* v_msg_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_736_ = l_Lean_PersistentArray_toArray___redArg(v_____do__lift_735_);
v___x_737_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v_sz_738_ = lean_array_size(v___x_736_);
v___x_739_ = ((size_t)0ULL);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_737_, v___f_729_, v_sz_738_, v___x_739_, v___x_736_);
v_msg_741_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_741_, 0, v_data_730_);
lean_ctor_set(v_msg_741_, 1, v_msg_731_);
lean_ctor_set(v_msg_741_, 2, v___x_740_);
v___x_742_ = lean_apply_1(v_inst_732_, v_msg_741_);
v___x_743_ = lean_apply_4(v_toBind_733_, lean_box(0), lean_box(0), v___x_742_, v___f_734_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed(lean_object* v___f_744_, lean_object* v_data_745_, lean_object* v_msg_746_, lean_object* v_inst_747_, lean_object* v_toBind_748_, lean_object* v___f_749_, lean_object* v_____do__lift_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3(v___f_744_, v_data_745_, v_msg_746_, v_inst_747_, v_toBind_748_, v___f_749_, v_____do__lift_750_);
lean_dec_ref(v_____do__lift_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(lean_object* v_ref_752_, lean_object* v_withRef_753_, lean_object* v___x_754_, lean_object* v_oldRef_755_){
_start:
{
lean_object* v_ref_756_; lean_object* v___x_757_; 
v_ref_756_ = l_Lean_replaceRef(v_ref_752_, v_oldRef_755_);
v___x_757_ = lean_apply_3(v_withRef_753_, lean_box(0), v_ref_756_, v___x_754_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed(lean_object* v_ref_758_, lean_object* v_withRef_759_, lean_object* v___x_760_, lean_object* v_oldRef_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4(v_ref_758_, v_withRef_759_, v___x_760_, v_oldRef_761_);
lean_dec(v_oldRef_761_);
lean_dec(v_ref_758_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_oldTraces_768_, lean_object* v_data_769_, lean_object* v_ref_770_, lean_object* v_msg_771_){
_start:
{
lean_object* v_toApplicative_772_; lean_object* v_toBind_773_; lean_object* v_modifyTraceState_774_; lean_object* v_getTraceState_775_; lean_object* v_toPure_776_; lean_object* v_getRef_777_; lean_object* v_withRef_778_; lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___f_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___x_784_; lean_object* v___f_785_; lean_object* v___x_786_; 
v_toApplicative_772_ = lean_ctor_get(v_inst_764_, 0);
lean_inc_ref(v_toApplicative_772_);
v_toBind_773_ = lean_ctor_get(v_inst_764_, 1);
lean_inc_n(v_toBind_773_, 4);
lean_dec_ref(v_inst_764_);
v_modifyTraceState_774_ = lean_ctor_get(v_inst_765_, 0);
lean_inc(v_modifyTraceState_774_);
v_getTraceState_775_ = lean_ctor_get(v_inst_765_, 1);
lean_inc(v_getTraceState_775_);
lean_dec_ref(v_inst_765_);
v_toPure_776_ = lean_ctor_get(v_toApplicative_772_, 1);
lean_inc(v_toPure_776_);
lean_dec_ref(v_toApplicative_772_);
v_getRef_777_ = lean_ctor_get(v_inst_766_, 0);
lean_inc(v_getRef_777_);
v_withRef_778_ = lean_ctor_get(v_inst_766_, 1);
lean_inc(v_withRef_778_);
lean_dec_ref(v_inst_766_);
v___f_779_ = lean_alloc_closure((void*)(l_Lean_getTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_779_, 0, v_toPure_776_);
v___x_780_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v_getTraceState_775_, v___f_779_);
v___f_781_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___closed__0));
lean_inc(v_ref_770_);
v___f_782_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__2), 4, 3);
lean_closure_set(v___f_782_, 0, v_ref_770_);
lean_closure_set(v___f_782_, 1, v_oldTraces_768_);
lean_closure_set(v___f_782_, 2, v_modifyTraceState_774_);
v___f_783_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_783_, 0, v___f_781_);
lean_closure_set(v___f_783_, 1, v_data_769_);
lean_closure_set(v___f_783_, 2, v_msg_771_);
lean_closure_set(v___f_783_, 3, v_inst_767_);
lean_closure_set(v___f_783_, 4, v_toBind_773_);
lean_closure_set(v___f_783_, 5, v___f_782_);
v___x_784_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_780_, v___f_783_);
v___f_785_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_785_, 0, v_ref_770_);
lean_closure_set(v___f_785_, 1, v_withRef_778_);
lean_closure_set(v___f_785_, 2, v___x_784_);
v___x_786_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v_getRef_777_, v___f_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode(lean_object* v_m_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_oldTraces_792_, lean_object* v_data_793_, lean_object* v_ref_794_, lean_object* v_msg_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_788_, v_inst_789_, v_inst_790_, v_inst_791_, v_oldTraces_792_, v_data_793_, v_ref_794_, v_msg_795_);
return v___x_796_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(lean_object* v_name_797_, lean_object* v_decl_798_, lean_object* v_ref_799_){
_start:
{
lean_object* v_defValue_801_; lean_object* v_descr_802_; lean_object* v_deprecation_x3f_803_; lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_defValue_801_ = lean_ctor_get(v_decl_798_, 0);
v_descr_802_ = lean_ctor_get(v_decl_798_, 1);
v_deprecation_x3f_803_ = lean_ctor_get(v_decl_798_, 2);
v___x_804_ = lean_alloc_ctor(1, 0, 1);
v___x_805_ = lean_unbox(v_defValue_801_);
lean_ctor_set_uint8(v___x_804_, 0, v___x_805_);
lean_inc(v_deprecation_x3f_803_);
lean_inc_ref(v_descr_802_);
lean_inc_n(v_name_797_, 2);
v___x_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_806_, 0, v_name_797_);
lean_ctor_set(v___x_806_, 1, v_ref_799_);
lean_ctor_set(v___x_806_, 2, v___x_804_);
lean_ctor_set(v___x_806_, 3, v_descr_802_);
lean_ctor_set(v___x_806_, 4, v_deprecation_x3f_803_);
v___x_807_ = lean_register_option(v_name_797_, v___x_806_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_815_; 
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v___x_807_, 0);
lean_dec(v_unused_816_);
v___x_809_ = v___x_807_;
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
else
{
lean_dec(v___x_807_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_815_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
lean_inc(v_defValue_801_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_name_797_);
lean_ctor_set(v___x_811_, 1, v_defValue_801_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_811_);
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_name_797_);
v_a_817_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_807_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_807_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_797_ = stack[0].m_obj;
lean_object* v_decl_798_ = stack[1].m_obj;
lean_object* v_ref_799_ = stack[2].m_obj;
lean_object* v_res_825_;
v_res_825_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_797_, v_decl_798_, v_ref_799_);
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_826_, lean_object* v_decl_827_, lean_object* v_ref_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v_name_826_, v_decl_827_, v_ref_828_);
lean_dec_ref(v_decl_827_);
return v_res_830_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_846_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_847_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_848_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_));
v___x_849_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_846_, v___x_847_, v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_850_;
v_res_850_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
stack->m_obj
 = v_res_850_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4____boxed(lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4_();
return v_res_852_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(lean_object* v_name_853_, lean_object* v_decl_854_, lean_object* v_ref_855_){
_start:
{
lean_object* v_defValue_857_; lean_object* v_descr_858_; lean_object* v_deprecation_x3f_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_defValue_857_ = lean_ctor_get(v_decl_854_, 0);
v_descr_858_ = lean_ctor_get(v_decl_854_, 1);
v_deprecation_x3f_859_ = lean_ctor_get(v_decl_854_, 2);
lean_inc(v_defValue_857_);
v___x_860_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_860_, 0, v_defValue_857_);
lean_inc(v_deprecation_x3f_859_);
lean_inc_ref(v_descr_858_);
lean_inc_n(v_name_853_, 2);
v___x_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_861_, 0, v_name_853_);
lean_ctor_set(v___x_861_, 1, v_ref_855_);
lean_ctor_set(v___x_861_, 2, v___x_860_);
lean_ctor_set(v___x_861_, 3, v_descr_858_);
lean_ctor_set(v___x_861_, 4, v_deprecation_x3f_859_);
v___x_862_ = lean_register_option(v_name_853_, v___x_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_870_; 
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v___x_862_, 0);
lean_dec(v_unused_871_);
v___x_864_ = v___x_862_;
v_isShared_865_ = v_isSharedCheck_870_;
goto v_resetjp_863_;
}
else
{
lean_dec(v___x_862_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_870_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_868_; 
lean_inc(v_defValue_857_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v_name_853_);
lean_ctor_set(v___x_866_, 1, v_defValue_857_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_866_);
v___x_868_ = v___x_864_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_name_853_);
v_a_872_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_862_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_862_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_853_ = stack[0].m_obj;
lean_object* v_decl_854_ = stack[1].m_obj;
lean_object* v_ref_855_ = stack[2].m_obj;
lean_object* v_res_880_;
v_res_880_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_853_, v_decl_854_, v_ref_855_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_881_, lean_object* v_decl_882_, lean_object* v_ref_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v_name_881_, v_decl_882_, v_ref_883_);
lean_dec_ref(v_decl_882_);
return v_res_885_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_903_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_904_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_));
v___x_905_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__spec__0(v___x_902_, v___x_903_, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_906_;
v_res_906_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
stack->m_obj
 = v_res_906_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4____boxed(lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2834694386____hygCtx___hyg_4_();
return v_res_908_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_926_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_927_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_928_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_));
v___x_929_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_926_, v___x_927_, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_930_;
v_res_930_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
stack->m_obj
 = v_res_930_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4____boxed(lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_3737982518____hygCtx___hyg_4_();
return v_res_932_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(lean_object* v_name_933_, lean_object* v_decl_934_, lean_object* v_ref_935_){
_start:
{
lean_object* v_defValue_937_; lean_object* v_descr_938_; lean_object* v_deprecation_x3f_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v_defValue_937_ = lean_ctor_get(v_decl_934_, 0);
v_descr_938_ = lean_ctor_get(v_decl_934_, 1);
v_deprecation_x3f_939_ = lean_ctor_get(v_decl_934_, 2);
lean_inc(v_defValue_937_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_defValue_937_);
lean_inc(v_deprecation_x3f_939_);
lean_inc_ref(v_descr_938_);
lean_inc_n(v_name_933_, 2);
v___x_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_941_, 0, v_name_933_);
lean_ctor_set(v___x_941_, 1, v_ref_935_);
lean_ctor_set(v___x_941_, 2, v___x_940_);
lean_ctor_set(v___x_941_, 3, v_descr_938_);
lean_ctor_set(v___x_941_, 4, v_deprecation_x3f_939_);
v___x_942_ = lean_register_option(v_name_933_, v___x_941_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_950_; 
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v___x_942_, 0);
lean_dec(v_unused_951_);
v___x_944_ = v___x_942_;
v_isShared_945_ = v_isSharedCheck_950_;
goto v_resetjp_943_;
}
else
{
lean_dec(v___x_942_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_950_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
lean_inc(v_defValue_937_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_name_933_);
lean_ctor_set(v___x_946_, 1, v_defValue_937_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_name_933_);
v_a_952_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_942_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_942_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_933_ = stack[0].m_obj;
lean_object* v_decl_934_ = stack[1].m_obj;
lean_object* v_ref_935_ = stack[2].m_obj;
lean_object* v_res_960_;
v_res_960_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_933_, v_decl_934_, v_ref_935_);
stack->m_obj
 = v_res_960_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_961_, lean_object* v_decl_962_, lean_object* v_ref_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v_name_961_, v_decl_962_, v_ref_963_);
lean_dec_ref(v_decl_962_);
return v_res_965_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_982_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_983_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_984_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_));
v___x_985_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__spec__0(v___x_982_, v___x_983_, v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_986_;
v_res_986_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4____boxed(lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_545552135____hygCtx___hyg_4_();
return v_res_988_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1006_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_1007_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_1008_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_));
v___x_1009_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_1006_, v___x_1007_, v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1010_;
v_res_1010_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
stack->m_obj
 = v_res_1010_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4____boxed(lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1925802394____hygCtx___hyg_4_();
return v_res_1012_;
}
}
uint8_t l_Lean_trace_profiler_isExporting(lean_object* v_opts_1013_){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1014_ = l_Lean_KVMap_instValueBool;
v___x_1015_ = l_Lean_KVMap_instValueString;
v___x_1016_ = l_Lean_trace_profiler_output;
v___x_1017_ = l_Lean_Option_get_x3f___redArg(v___x_1015_, v_opts_1013_, v___x_1016_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1018_ = l_Lean_trace_profiler_serve;
v___x_1019_ = l_Lean_Option_get___redArg(v___x_1014_, v_opts_1013_, v___x_1018_);
v___x_1020_ = lean_unbox(v___x_1019_);
lean_dec(v___x_1019_);
return v___x_1020_;
}
else
{
uint8_t v___x_1021_; 
lean_dec_ref_known(v___x_1017_, 1);
v___x_1021_ = 1;
return v___x_1021_;
}
}
}
LEAN_EXPORT void l_Lean_trace_profiler_isExporting_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1013_ = stack[0].m_obj;
uint8_t v_res_1022_;
v_res_1022_ = l_Lean_trace_profiler_isExporting(v_opts_1013_);
stack->m_num = v_res_1022_;
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_isExporting___boxed(lean_object* v_opts_1023_){
_start:
{
uint8_t v_res_1024_; lean_object* v_r_1025_; 
v_res_1024_ = l_Lean_trace_profiler_isExporting(v_opts_1023_);
lean_dec_ref(v_opts_1023_);
v_r_1025_ = lean_box(v_res_1024_);
return v_r_1025_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1045_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1046_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__3_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1047_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__4_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_));
v___x_1048_ = l_Lean_Option_register___at___00__private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_1728529786____hygCtx___hyg_4__spec__0(v___x_1045_, v___x_1046_, v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1049_;
v_res_1049_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
stack->m_obj
 = v_res_1049_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4____boxed(lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_4169215340____hygCtx___hyg_4_();
return v_res_1051_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1052_; double v___x_1053_; 
v___x_1052_ = lean_unsigned_to_nat(1000000000u);
v___x_1053_ = lean_float_of_nat(v___x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0(lean_object* v_start_1054_, lean_object* v_a_1055_, lean_object* v_toPure_1056_, lean_object* v_stop_1057_){
_start:
{
double v___x_1058_; double v___x_1059_; double v___x_1060_; double v___x_1061_; double v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1058_ = lean_float_of_nat(v_start_1054_);
v___x_1059_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1060_ = lean_float_div(v___x_1058_, v___x_1059_);
v___x_1061_ = lean_float_of_nat(v_stop_1057_);
v___x_1062_ = lean_float_div(v___x_1061_, v___x_1059_);
v___x_1063_ = lean_box_float(v___x_1060_);
v___x_1064_ = lean_box_float(v___x_1062_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_a_1055_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_apply_2(v_toPure_1056_, lean_box(0), v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1(lean_object* v_start_1068_, lean_object* v_toPure_1069_, lean_object* v_toBind_1070_, lean_object* v___x_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___f_1073_; lean_object* v___x_1074_; 
v___f_1073_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1073_, 0, v_start_1068_);
lean_closure_set(v___f_1073_, 1, v_a_1072_);
lean_closure_set(v___f_1073_, 2, v_toPure_1069_);
v___x_1074_ = lean_apply_4(v_toBind_1070_, lean_box(0), lean_box(0), v___x_1071_, v___f_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2(lean_object* v_toPure_1075_, lean_object* v_toBind_1076_, lean_object* v___x_1077_, lean_object* v_act_1078_, lean_object* v_start_1079_){
_start:
{
lean_object* v___f_1080_; lean_object* v___x_1081_; 
lean_inc(v_toBind_1076_);
v___f_1080_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1080_, 0, v_start_1079_);
lean_closure_set(v___f_1080_, 1, v_toPure_1075_);
lean_closure_set(v___f_1080_, 2, v_toBind_1076_);
lean_closure_set(v___f_1080_, 3, v___x_1077_);
v___x_1081_ = lean_apply_4(v_toBind_1076_, lean_box(0), lean_box(0), v_act_1078_, v___f_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3(lean_object* v_start_1082_, lean_object* v_a_1083_, lean_object* v_toPure_1084_, lean_object* v_stop_1085_){
_start:
{
double v___x_1086_; double v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1086_ = lean_float_of_nat(v_start_1082_);
v___x_1087_ = lean_float_of_nat(v_stop_1085_);
v___x_1088_ = lean_box_float(v___x_1086_);
v___x_1089_ = lean_box_float(v___x_1087_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_a_1083_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_apply_2(v_toPure_1084_, lean_box(0), v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4(lean_object* v_start_1093_, lean_object* v_toPure_1094_, lean_object* v_toBind_1095_, lean_object* v___x_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v___f_1098_; lean_object* v___x_1099_; 
v___f_1098_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1098_, 0, v_start_1093_);
lean_closure_set(v___f_1098_, 1, v_a_1097_);
lean_closure_set(v___f_1098_, 2, v_toPure_1094_);
v___x_1099_ = lean_apply_4(v_toBind_1095_, lean_box(0), lean_box(0), v___x_1096_, v___f_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5(lean_object* v_toPure_1100_, lean_object* v_toBind_1101_, lean_object* v___x_1102_, lean_object* v_act_1103_, lean_object* v_start_1104_){
_start:
{
lean_object* v___f_1105_; lean_object* v___x_1106_; 
lean_inc(v_toBind_1101_);
v___f_1105_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1105_, 0, v_start_1104_);
lean_closure_set(v___f_1105_, 1, v_toPure_1100_);
lean_closure_set(v___f_1105_, 2, v_toBind_1101_);
lean_closure_set(v___f_1105_, 3, v___x_1102_);
v___x_1106_ = lean_apply_4(v_toBind_1101_, lean_box(0), lean_box(0), v_act_1103_, v___f_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_opts_1111_, lean_object* v_act_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v_toApplicative_1114_; lean_object* v_toBind_1115_; lean_object* v_toPure_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1113_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1114_ = lean_ctor_get(v_inst_1109_, 0);
lean_inc_ref(v_toApplicative_1114_);
v_toBind_1115_ = lean_ctor_get(v_inst_1109_, 1);
lean_inc(v_toBind_1115_);
lean_dec_ref(v_inst_1109_);
v_toPure_1116_ = lean_ctor_get(v_toApplicative_1114_, 1);
lean_inc(v_toPure_1116_);
lean_dec_ref(v_toApplicative_1114_);
v___x_1117_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1118_ = l_Lean_Option_get___redArg(v___x_1113_, v_opts_1111_, v___x_1117_);
v___x_1119_ = lean_unbox(v___x_1118_);
lean_dec(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; 
v___x_1120_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1121_ = lean_apply_2(v_inst_1110_, lean_box(0), v___x_1120_);
lean_inc(v___x_1121_);
lean_inc(v_toBind_1115_);
v___f_1122_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1122_, 0, v_toPure_1116_);
lean_closure_set(v___f_1122_, 1, v_toBind_1115_);
lean_closure_set(v___f_1122_, 2, v___x_1121_);
lean_closure_set(v___f_1122_, 3, v_act_1112_);
v___x_1123_ = lean_apply_4(v_toBind_1115_, lean_box(0), lean_box(0), v___x_1121_, v___f_1122_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; 
v___x_1124_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1125_ = lean_apply_2(v_inst_1110_, lean_box(0), v___x_1124_);
lean_inc(v___x_1125_);
lean_inc(v_toBind_1115_);
v___f_1126_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1126_, 0, v_toPure_1116_);
lean_closure_set(v___f_1126_, 1, v_toBind_1115_);
lean_closure_set(v___f_1126_, 2, v___x_1125_);
lean_closure_set(v___f_1126_, 3, v_act_1112_);
v___x_1127_ = lean_apply_4(v_toBind_1115_, lean_box(0), lean_box(0), v___x_1125_, v___f_1126_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___boxed(lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_opts_1130_, lean_object* v_act_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg(v_inst_1128_, v_inst_1129_, v_opts_1130_, v_act_1131_);
lean_dec_ref(v_opts_1130_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop(lean_object* v_00_u03b1_1133_, lean_object* v_m_1134_, lean_object* v_inst_1135_, lean_object* v_inst_1136_, lean_object* v_opts_1137_, lean_object* v_act_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v_toApplicative_1140_; lean_object* v_toBind_1141_; lean_object* v_toPure_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1139_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1140_ = lean_ctor_get(v_inst_1135_, 0);
lean_inc_ref(v_toApplicative_1140_);
v_toBind_1141_ = lean_ctor_get(v_inst_1135_, 1);
lean_inc(v_toBind_1141_);
lean_dec_ref(v_inst_1135_);
v_toPure_1142_ = lean_ctor_get(v_toApplicative_1140_, 1);
lean_inc(v_toPure_1142_);
lean_dec_ref(v_toApplicative_1140_);
v___x_1143_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1144_ = l_Lean_Option_get___redArg(v___x_1139_, v_opts_1137_, v___x_1143_);
v___x_1145_ = lean_unbox(v___x_1144_);
lean_dec(v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1147_ = lean_apply_2(v_inst_1136_, lean_box(0), v___x_1146_);
lean_inc(v___x_1147_);
lean_inc(v_toBind_1141_);
v___f_1148_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1148_, 0, v_toPure_1142_);
lean_closure_set(v___f_1148_, 1, v_toBind_1141_);
lean_closure_set(v___f_1148_, 2, v___x_1147_);
lean_closure_set(v___f_1148_, 3, v_act_1138_);
v___x_1149_ = lean_apply_4(v_toBind_1141_, lean_box(0), lean_box(0), v___x_1147_, v___f_1148_);
return v___x_1149_;
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___f_1152_; lean_object* v___x_1153_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1151_ = lean_apply_2(v_inst_1136_, lean_box(0), v___x_1150_);
lean_inc(v___x_1151_);
lean_inc(v_toBind_1141_);
v___f_1152_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1152_, 0, v_toPure_1142_);
lean_closure_set(v___f_1152_, 1, v_toBind_1141_);
lean_closure_set(v___f_1152_, 2, v___x_1151_);
lean_closure_set(v___f_1152_, 3, v_act_1138_);
v___x_1153_ = lean_apply_4(v_toBind_1141_, lean_box(0), lean_box(0), v___x_1151_, v___f_1152_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withStartStop___boxed(lean_object* v_00_u03b1_1154_, lean_object* v_m_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_opts_1158_, lean_object* v_act_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l___private_Lean_Util_Trace_0__Lean_withStartStop(v_00_u03b1_1154_, v_m_1155_, v_inst_1156_, v_inst_1157_, v_opts_1158_, v_act_1159_);
lean_dec_ref(v_opts_1158_);
return v_res_1160_;
}
}
static double _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0(void){
_start:
{
lean_object* v___x_1161_; double v___x_1162_; 
v___x_1161_ = lean_unsigned_to_nat(1000u);
v___x_1162_ = lean_float_of_nat(v___x_1161_);
return v___x_1162_;
}
}
double l_Lean_trace_profiler_threshold_unitAdjusted(lean_object* v_o_1163_){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1164_ = l_Lean_KVMap_instValueBool;
v___x_1165_ = l_Lean_KVMap_instValueNat;
v___x_1166_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1167_ = l_Lean_Option_get___redArg(v___x_1164_, v_o_1163_, v___x_1166_);
v___x_1168_ = lean_unbox(v___x_1167_);
lean_dec(v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; double v___x_1171_; double v___x_1172_; double v___x_1173_; 
v___x_1169_ = l_Lean_trace_profiler_threshold;
v___x_1170_ = l_Lean_Option_get___redArg(v___x_1165_, v_o_1163_, v___x_1169_);
v___x_1171_ = lean_float_of_nat(v___x_1170_);
v___x_1172_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1173_ = lean_float_div(v___x_1171_, v___x_1172_);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; double v___x_1176_; 
v___x_1174_ = l_Lean_trace_profiler_threshold;
v___x_1175_ = l_Lean_Option_get___redArg(v___x_1165_, v_o_1163_, v___x_1174_);
v___x_1176_ = lean_float_of_nat(v___x_1175_);
return v___x_1176_;
}
}
}
LEAN_EXPORT void l_Lean_trace_profiler_threshold_unitAdjusted_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1163_ = stack[0].m_obj;
double v_res_1177_;
v_res_1177_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1163_);
stack->m_float
 = v_res_1177_;
}
LEAN_EXPORT lean_object* l_Lean_trace_profiler_threshold_unitAdjusted___boxed(lean_object* v_o_1178_){
_start:
{
double v_res_1179_; lean_object* v_r_1180_; 
v_res_1179_ = l_Lean_trace_profiler_threshold_unitAdjusted(v_o_1178_);
lean_dec_ref(v_o_1178_);
v_r_1180_ = lean_box_float(v_res_1179_);
return v_r_1180_;
}
}
static lean_object* _init_l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0(void){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_instMonadExceptOfEIO___redArg();
return v___x_1181_;
}
}
lean_object* l_Lean_instMonadAlwaysExceptEIO___redArg(){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0, &l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0);
return v___x_1183_;
}
}
LEAN_EXPORT void l_Lean_instMonadAlwaysExceptEIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1184_;
v_res_1184_ = l_Lean_instMonadAlwaysExceptEIO___redArg();
stack->m_obj
 = v_res_1184_;
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO___redArg___boxed(lean_object* v___dummy_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_instMonadAlwaysExceptEIO___redArg();
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptEIO(lean_object* v_00_u03b5_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_obj_once(&l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0, &l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0_once, _init_l_Lean_instMonadAlwaysExceptEIO___redArg___closed__0);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT___redArg(lean_object* v_inst_1189_, lean_object* v_always_1190_){
_start:
{
lean_object* v___f_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; 
lean_inc_ref(v_always_1190_);
v___f_1191_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1191_, 0, v_always_1190_);
lean_closure_set(v___f_1191_, 1, v_inst_1189_);
v___f_1192_ = lean_alloc_closure((void*)(l_StateT_instMonadExceptOf___redArg___lam__3), 5, 1);
lean_closure_set(v___f_1192_, 0, v_always_1190_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___f_1191_);
lean_ctor_set(v___x_1193_, 1, v___f_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateT(lean_object* v_m_1194_, lean_object* v_inst_1195_, lean_object* v_00_u03b5_1196_, lean_object* v_00_u03c3_1197_, lean_object* v_always_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_instMonadAlwaysExceptStateT___redArg(v_inst_1195_, v_always_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object* v_always_1200_){
_start:
{
lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; 
lean_inc_ref(v_always_1200_);
v___f_1201_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1201_, 0, v_always_1200_);
v___f_1202_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1202_, 0, v_always_1200_);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___f_1201_);
lean_ctor_set(v___x_1203_, 1, v___f_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27(lean_object* v_m_1204_, lean_object* v_00_u03b5_1205_, lean_object* v_00_u03c9_1206_, lean_object* v_00_u03c3_1207_, lean_object* v_always_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v_always_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object* v_always_1210_){
_start:
{
lean_object* v___f_1211_; lean_object* v___f_1212_; lean_object* v___x_1213_; 
lean_inc_ref(v_always_1210_);
v___f_1211_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1211_, 0, v_always_1210_);
v___f_1212_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1212_, 0, v_always_1210_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___f_1211_);
lean_ctor_set(v___x_1213_, 1, v___f_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptReaderT(lean_object* v_m_1214_, lean_object* v_00_u03b5_1215_, lean_object* v_00_u03c1_1216_, lean_object* v_always_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v_always_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT___redArg(lean_object* v_always_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1220_, v_inst_1221_, v_inst_1222_, v_always_1219_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadAlwaysExceptMonadCacheT(lean_object* v_00_u03b1_1224_, lean_object* v_m_1225_, lean_object* v_00_u03b5_1226_, lean_object* v_00_u03c9_1227_, lean_object* v_00_u03b2_1228_, lean_object* v_always_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_MonadCacheT_instMonadExceptOf___redArg(v_inst_1230_, v_inst_1231_, v_inst_1232_, v_always_1229_);
return v___x_1233_;
}
}
uint8_t l_Lean_instExceptToTraceResultBool___redArg___lam__0(lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 0)
{
uint8_t v___x_1241_; 
v___x_1241_ = 2;
return v___x_1241_;
}
else
{
lean_object* v_a_1242_; uint8_t v___x_1243_; 
v_a_1242_ = lean_ctor_get(v_x_1240_, 0);
v___x_1243_ = lean_unbox(v_a_1242_);
if (v___x_1243_ == 0)
{
uint8_t v___x_1244_; 
v___x_1244_ = 1;
return v___x_1244_;
}
else
{
uint8_t v___x_1245_; 
v___x_1245_ = 0;
return v___x_1245_;
}
}
}
}
LEAN_EXPORT void l_Lean_instExceptToTraceResultBool___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1240_ = stack[0].m_obj;
uint8_t v_res_1246_;
v_res_1246_ = l_Lean_instExceptToTraceResultBool___redArg___lam__0(v_x_1240_);
stack->m_num = v_res_1246_;
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___redArg___lam__0___boxed(lean_object* v_x_1247_){
_start:
{
uint8_t v_res_1248_; lean_object* v_r_1249_; 
v_res_1248_ = l_Lean_instExceptToTraceResultBool___redArg___lam__0(v_x_1247_);
lean_dec_ref(v_x_1247_);
v_r_1249_ = lean_box(v_res_1248_);
return v_r_1249_;
}
}
lean_object* l_Lean_instExceptToTraceResultBool___redArg(){
_start:
{
lean_object* v___f_1252_; 
v___f_1252_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___redArg___closed__0));
return v___f_1252_;
}
}
LEAN_EXPORT void l_Lean_instExceptToTraceResultBool___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1253_;
v_res_1253_ = l_Lean_instExceptToTraceResultBool___redArg();
stack->m_obj
 = v_res_1253_;
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool___redArg___boxed(lean_object* v___dummy_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_instExceptToTraceResultBool___redArg();
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultBool(lean_object* v_00_u03b5_1256_){
_start:
{
lean_object* v___f_1257_; 
v___f_1257_ = ((lean_object*)(l_Lean_instExceptToTraceResultBool___redArg___closed__0));
return v___f_1257_;
}
}
uint8_t l_Lean_instExceptToTraceResultOption___redArg___lam__0(lean_object* v_x_1258_){
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
lean_object* v_a_1260_; 
v_a_1260_ = lean_ctor_get(v_x_1258_, 0);
if (lean_obj_tag(v_a_1260_) == 0)
{
uint8_t v___x_1261_; 
v___x_1261_ = 1;
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
}
LEAN_EXPORT void l_Lean_instExceptToTraceResultOption___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1258_ = stack[0].m_obj;
uint8_t v_res_1263_;
v_res_1263_ = l_Lean_instExceptToTraceResultOption___redArg___lam__0(v_x_1258_);
stack->m_num = v_res_1263_;
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___redArg___lam__0___boxed(lean_object* v_x_1264_){
_start:
{
uint8_t v_res_1265_; lean_object* v_r_1266_; 
v_res_1265_ = l_Lean_instExceptToTraceResultOption___redArg___lam__0(v_x_1264_);
lean_dec_ref(v_x_1264_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
lean_object* l_Lean_instExceptToTraceResultOption___redArg(){
_start:
{
lean_object* v___f_1269_; 
v___f_1269_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___redArg___closed__0));
return v___f_1269_;
}
}
LEAN_EXPORT void l_Lean_instExceptToTraceResultOption___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1270_;
v_res_1270_ = l_Lean_instExceptToTraceResultOption___redArg();
stack->m_obj
 = v_res_1270_;
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption___redArg___boxed(lean_object* v___dummy_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_instExceptToTraceResultOption___redArg();
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultOption(lean_object* v_00_u03b1_1273_, lean_object* v_00_u03b5_1274_){
_start:
{
lean_object* v___f_1275_; 
v___f_1275_ = ((lean_object*)(l_Lean_instExceptToTraceResultOption___redArg___closed__0));
return v___f_1275_;
}
}
uint8_t l_Lean_instExceptToTraceResultExpr___redArg___lam__0(lean_object* v_x_1276_){
_start:
{
if (lean_obj_tag(v_x_1276_) == 0)
{
uint8_t v___x_1277_; 
v___x_1277_ = 2;
return v___x_1277_;
}
else
{
lean_object* v_a_1278_; uint8_t v___x_1279_; 
v_a_1278_ = lean_ctor_get(v_x_1276_, 0);
v___x_1279_ = l_Lean_Expr_hasSyntheticSorry(v_a_1278_);
if (v___x_1279_ == 0)
{
uint8_t v___x_1280_; 
v___x_1280_ = 0;
return v___x_1280_;
}
else
{
uint8_t v___x_1281_; 
v___x_1281_ = 1;
return v___x_1281_;
}
}
}
}
LEAN_EXPORT void l_Lean_instExceptToTraceResultExpr___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1276_ = stack[0].m_obj;
uint8_t v_res_1282_;
v_res_1282_ = l_Lean_instExceptToTraceResultExpr___redArg___lam__0(v_x_1276_);
stack->m_num = v_res_1282_;
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___redArg___lam__0___boxed(lean_object* v_x_1283_){
_start:
{
uint8_t v_res_1284_; lean_object* v_r_1285_; 
v_res_1284_ = l_Lean_instExceptToTraceResultExpr___redArg___lam__0(v_x_1283_);
lean_dec_ref(v_x_1283_);
v_r_1285_ = lean_box(v_res_1284_);
return v_r_1285_;
}
}
lean_object* l_Lean_instExceptToTraceResultExpr___redArg(){
_start:
{
lean_object* v___f_1288_; 
v___f_1288_ = ((lean_object*)(l_Lean_instExceptToTraceResultExpr___redArg___closed__0));
return v___f_1288_;
}
}
LEAN_EXPORT void l_Lean_instExceptToTraceResultExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1289_;
v_res_1289_ = l_Lean_instExceptToTraceResultExpr___redArg();
stack->m_obj
 = v_res_1289_;
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr___redArg___boxed(lean_object* v___dummy_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_instExceptToTraceResultExpr___redArg();
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResultExpr(lean_object* v_00_u03b5_1292_){
_start:
{
lean_object* v___f_1293_; 
v___f_1293_ = ((lean_object*)(l_Lean_instExceptToTraceResultExpr___redArg___closed__0));
return v___f_1293_;
}
}
uint8_t l_Lean_instExceptToTraceResult___redArg___lam__0(lean_object* v_x_1294_){
_start:
{
if (lean_obj_tag(v_x_1294_) == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = 2;
return v___x_1295_;
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = 0;
return v___x_1296_;
}
}
}
LEAN_EXPORT void l_Lean_instExceptToTraceResult___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1294_ = stack[0].m_obj;
uint8_t v_res_1297_;
v_res_1297_ = l_Lean_instExceptToTraceResult___redArg___lam__0(v_x_1294_);
stack->m_num = v_res_1297_;
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___redArg___lam__0___boxed(lean_object* v_x_1298_){
_start:
{
uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_res_1299_ = l_Lean_instExceptToTraceResult___redArg___lam__0(v_x_1298_);
lean_dec_ref(v_x_1298_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
lean_object* l_Lean_instExceptToTraceResult___redArg(){
_start:
{
lean_object* v___f_1303_; 
v___f_1303_ = ((lean_object*)(l_Lean_instExceptToTraceResult___redArg___closed__0));
return v___f_1303_;
}
}
LEAN_EXPORT void l_Lean_instExceptToTraceResult___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1304_;
v_res_1304_ = l_Lean_instExceptToTraceResult___redArg();
stack->m_obj
 = v_res_1304_;
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult___redArg___boxed(lean_object* v___dummy_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_instExceptToTraceResult___redArg();
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instExceptToTraceResult(lean_object* v_00_u03b1_1307_, lean_object* v_00_u03b5_1308_){
_start:
{
lean_object* v___f_1309_; 
v___f_1309_ = ((lean_object*)(l_Lean_instExceptToTraceResult___redArg___closed__0));
return v___f_1309_;
}
}
uint8_t l_Lean_Except_toTraceResult___redArg(lean_object* v_inst_1310_, lean_object* v_e_1311_){
_start:
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = lean_apply_1(v_inst_1310_, v_e_1311_);
v___x_1313_ = lean_unbox(v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1310_ = stack[0].m_obj;
lean_object* v_e_1311_ = stack[1].m_obj;
uint8_t v_res_1314_;
v_res_1314_ = l_Lean_Except_toTraceResult___redArg(v_inst_1310_, v_e_1311_);
stack->m_num = v_res_1314_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___redArg___boxed(lean_object* v_inst_1315_, lean_object* v_e_1316_){
_start:
{
uint8_t v_res_1317_; lean_object* v_r_1318_; 
v_res_1317_ = l_Lean_Except_toTraceResult___redArg(v_inst_1315_, v_e_1316_);
v_r_1318_ = lean_box(v_res_1317_);
return v_r_1318_;
}
}
uint8_t l_Lean_Except_toTraceResult(lean_object* v_00_u03b1_1319_, lean_object* v_00_u03b5_1320_, lean_object* v_inst_1321_, lean_object* v_e_1322_){
_start:
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = lean_apply_1(v_inst_1321_, v_e_1322_);
v___x_1324_ = lean_unbox(v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1321_ = stack[2].m_obj;
lean_object* v_e_1322_ = stack[3].m_obj;
uint8_t v_res_1325_;
v_res_1325_ = l_Lean_Except_toTraceResult(lean_box(0), lean_box(0), v_inst_1321_, v_e_1322_);
stack->m_num = v_res_1325_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_00_u03b5_1327_, lean_object* v_inst_1328_, lean_object* v_e_1329_){
_start:
{
uint8_t v_res_1330_; lean_object* v_r_1331_; 
v_res_1330_ = l_Lean_Except_toTraceResult(v_00_u03b1_1326_, v_00_u03b5_1327_, v_inst_1328_, v_e_1329_);
v_r_1331_ = lean_box(v_res_1330_);
return v_r_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0(lean_object* v_oldTraces_1332_, lean_object* v_s_1333_){
_start:
{
uint64_t v_tid_1334_; lean_object* v_traces_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
v_tid_1334_ = lean_ctor_get_uint64(v_s_1333_, sizeof(void*)*1);
v_traces_1335_ = lean_ctor_get(v_s_1333_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_s_1333_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1337_ = v_s_1333_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_traces_1335_);
lean_dec(v_s_1333_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1332_, v_traces_1335_);
lean_dec_ref(v_traces_1335_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
lean_ctor_set_uint64(v_reuseFailAlloc_1342_, sizeof(void*)*1, v_tid_1334_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__0));
v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(lean_object* v_toPure_1347_, lean_object* v_x_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___closed__1);
v___x_1350_ = lean_apply_2(v_toPure_1347_, lean_box(0), v___x_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___boxed(lean_object* v_toPure_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1(v_toPure_1351_, v_x_1352_);
lean_dec(v_x_1352_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2(lean_object* v_inst_1354_, lean_object* v___x_1355_, lean_object* v_fst_1356_, lean_object* v_____r_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_MonadExcept_ofExcept___redArg(v_inst_1354_, v___x_1355_, v_fst_1356_);
return v___x_1358_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_inst_1362_, lean_object* v_oldTraces_1363_, lean_object* v_ref_1364_, lean_object* v_toBind_1365_, lean_object* v___f_1366_, lean_object* v_inst_1367_, lean_object* v_fst_1368_, lean_object* v_cls_1369_, uint8_t v_collapsed_1370_, lean_object* v_tag_1371_, lean_object* v___x_1372_, double v_fst_1373_, double v_snd_1374_, lean_object* v_m_1375_){
_start:
{
lean_object* v_data_1377_; lean_object* v_result_1380_; lean_object* v___x_1381_; double v___x_1382_; lean_object* v_data_1383_; uint8_t v___x_1384_; 
v_result_1380_ = lean_apply_1(v_inst_1367_, v_fst_1368_);
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_result_1380_);
v___x_1382_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_1371_);
lean_inc_ref(v___x_1381_);
lean_inc(v_cls_1369_);
v_data_1383_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1383_, 0, v_cls_1369_);
lean_ctor_set(v_data_1383_, 1, v___x_1381_);
lean_ctor_set(v_data_1383_, 2, v_tag_1371_);
lean_ctor_set_float(v_data_1383_, sizeof(void*)*3, v___x_1382_);
lean_ctor_set_float(v_data_1383_, sizeof(void*)*3 + 8, v___x_1382_);
lean_ctor_set_uint8(v_data_1383_, sizeof(void*)*3 + 16, v_collapsed_1370_);
v___x_1384_ = lean_unbox(v___x_1372_);
if (v___x_1384_ == 0)
{
lean_dec_ref_known(v___x_1381_, 1);
lean_dec_ref(v_tag_1371_);
lean_dec(v_cls_1369_);
v_data_1377_ = v_data_1383_;
goto v___jp_1376_;
}
else
{
lean_object* v_data_1385_; 
lean_dec_ref_known(v_data_1383_, 3);
v_data_1385_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1385_, 0, v_cls_1369_);
lean_ctor_set(v_data_1385_, 1, v___x_1381_);
lean_ctor_set(v_data_1385_, 2, v_tag_1371_);
lean_ctor_set_float(v_data_1385_, sizeof(void*)*3, v_fst_1373_);
lean_ctor_set_float(v_data_1385_, sizeof(void*)*3 + 8, v_snd_1374_);
lean_ctor_set_uint8(v_data_1385_, sizeof(void*)*3 + 16, v_collapsed_1370_);
v_data_1377_ = v_data_1385_;
goto v___jp_1376_;
}
v___jp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_1359_, v_inst_1360_, v_inst_1361_, v_inst_1362_, v_oldTraces_1363_, v_data_1377_, v_ref_1364_, v_m_1375_);
v___x_1379_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1378_, v___f_1366_);
return v___x_1379_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1359_ = stack[0].m_obj;
lean_object* v_inst_1360_ = stack[1].m_obj;
lean_object* v_inst_1361_ = stack[2].m_obj;
lean_object* v_inst_1362_ = stack[3].m_obj;
lean_object* v_oldTraces_1363_ = stack[4].m_obj;
lean_object* v_ref_1364_ = stack[5].m_obj;
lean_object* v_toBind_1365_ = stack[6].m_obj;
lean_object* v___f_1366_ = stack[7].m_obj;
lean_object* v_inst_1367_ = stack[8].m_obj;
lean_object* v_fst_1368_ = stack[9].m_obj;
lean_object* v_cls_1369_ = stack[10].m_obj;
uint8_t v_collapsed_1370_ = stack[11].m_num;
lean_object* v_tag_1371_ = stack[12].m_obj;
lean_object* v___x_1372_ = stack[13].m_obj;
double v_fst_1373_ = stack[14].m_float;
double v_snd_1374_ = stack[15].m_float;
lean_object* v_m_1375_ = stack[16].m_obj;
lean_object* v_res_1386_;
v_res_1386_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1359_, v_inst_1360_, v_inst_1361_, v_inst_1362_, v_oldTraces_1363_, v_ref_1364_, v_toBind_1365_, v___f_1366_, v_inst_1367_, v_fst_1368_, v_cls_1369_, v_collapsed_1370_, v_tag_1371_, v___x_1372_, v_fst_1373_, v_snd_1374_, v_m_1375_);
stack->m_obj
 = v_res_1386_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_1387_ = _args[0];
lean_object* v_inst_1388_ = _args[1];
lean_object* v_inst_1389_ = _args[2];
lean_object* v_inst_1390_ = _args[3];
lean_object* v_oldTraces_1391_ = _args[4];
lean_object* v_ref_1392_ = _args[5];
lean_object* v_toBind_1393_ = _args[6];
lean_object* v___f_1394_ = _args[7];
lean_object* v_inst_1395_ = _args[8];
lean_object* v_fst_1396_ = _args[9];
lean_object* v_cls_1397_ = _args[10];
lean_object* v_collapsed_1398_ = _args[11];
lean_object* v_tag_1399_ = _args[12];
lean_object* v___x_1400_ = _args[13];
lean_object* v_fst_1401_ = _args[14];
lean_object* v_snd_1402_ = _args[15];
lean_object* v_m_1403_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1404_; double v_fst_473__boxed_1405_; double v_snd_474__boxed_1406_; lean_object* v_res_1407_; 
v_collapsed_boxed_1404_ = lean_unbox(v_collapsed_1398_);
v_fst_473__boxed_1405_ = lean_unbox_float(v_fst_1401_);
lean_dec_ref(v_fst_1401_);
v_snd_474__boxed_1406_ = lean_unbox_float(v_snd_1402_);
lean_dec_ref(v_snd_1402_);
v_res_1407_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4(v_inst_1387_, v_inst_1388_, v_inst_1389_, v_inst_1390_, v_oldTraces_1391_, v_ref_1392_, v_toBind_1393_, v___f_1394_, v_inst_1395_, v_fst_1396_, v_cls_1397_, v_collapsed_boxed_1404_, v_tag_1399_, v___x_1400_, v_fst_473__boxed_1405_, v_snd_474__boxed_1406_, v_m_1403_);
lean_dec(v___x_1400_);
return v_res_1407_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(lean_object* v_always_1408_, lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_oldTraces_1413_, lean_object* v_toBind_1414_, lean_object* v___f_1415_, lean_object* v_inst_1416_, lean_object* v_fst_1417_, lean_object* v_cls_1418_, uint8_t v_collapsed_1419_, lean_object* v_tag_1420_, lean_object* v___x_1421_, double v_fst_1422_, double v_snd_1423_, lean_object* v_msg_1424_, lean_object* v___f_1425_, lean_object* v_ref_1426_){
_start:
{
lean_object* v_tryCatch_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___f_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_tryCatch_1427_ = lean_ctor_get(v_always_1408_, 1);
lean_inc(v_tryCatch_1427_);
lean_dec_ref(v_always_1408_);
v___x_1428_ = lean_box(v_collapsed_1419_);
v___x_1429_ = lean_box_float(v_fst_1422_);
v___x_1430_ = lean_box_float(v_snd_1423_);
lean_inc_ref(v_fst_1417_);
lean_inc(v_toBind_1414_);
v___f_1431_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__4___boxed), 17, 16);
lean_closure_set(v___f_1431_, 0, v_inst_1409_);
lean_closure_set(v___f_1431_, 1, v_inst_1410_);
lean_closure_set(v___f_1431_, 2, v_inst_1411_);
lean_closure_set(v___f_1431_, 3, v_inst_1412_);
lean_closure_set(v___f_1431_, 4, v_oldTraces_1413_);
lean_closure_set(v___f_1431_, 5, v_ref_1426_);
lean_closure_set(v___f_1431_, 6, v_toBind_1414_);
lean_closure_set(v___f_1431_, 7, v___f_1415_);
lean_closure_set(v___f_1431_, 8, v_inst_1416_);
lean_closure_set(v___f_1431_, 9, v_fst_1417_);
lean_closure_set(v___f_1431_, 10, v_cls_1418_);
lean_closure_set(v___f_1431_, 11, v___x_1428_);
lean_closure_set(v___f_1431_, 12, v_tag_1420_);
lean_closure_set(v___f_1431_, 13, v___x_1421_);
lean_closure_set(v___f_1431_, 14, v___x_1429_);
lean_closure_set(v___f_1431_, 15, v___x_1430_);
v___x_1432_ = lean_apply_1(v_msg_1424_, v_fst_1417_);
v___x_1433_ = lean_apply_3(v_tryCatch_1427_, lean_box(0), v___x_1432_, v___f_1425_);
v___x_1434_ = lean_apply_4(v_toBind_1414_, lean_box(0), lean_box(0), v___x_1433_, v___f_1431_);
return v___x_1434_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_always_1408_ = stack[0].m_obj;
lean_object* v_inst_1409_ = stack[1].m_obj;
lean_object* v_inst_1410_ = stack[2].m_obj;
lean_object* v_inst_1411_ = stack[3].m_obj;
lean_object* v_inst_1412_ = stack[4].m_obj;
lean_object* v_oldTraces_1413_ = stack[5].m_obj;
lean_object* v_toBind_1414_ = stack[6].m_obj;
lean_object* v___f_1415_ = stack[7].m_obj;
lean_object* v_inst_1416_ = stack[8].m_obj;
lean_object* v_fst_1417_ = stack[9].m_obj;
lean_object* v_cls_1418_ = stack[10].m_obj;
uint8_t v_collapsed_1419_ = stack[11].m_num;
lean_object* v_tag_1420_ = stack[12].m_obj;
lean_object* v___x_1421_ = stack[13].m_obj;
double v_fst_1422_ = stack[14].m_float;
double v_snd_1423_ = stack[15].m_float;
lean_object* v_msg_1424_ = stack[16].m_obj;
lean_object* v___f_1425_ = stack[17].m_obj;
lean_object* v_ref_1426_ = stack[18].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(v_always_1408_, v_inst_1409_, v_inst_1410_, v_inst_1411_, v_inst_1412_, v_oldTraces_1413_, v_toBind_1414_, v___f_1415_, v_inst_1416_, v_fst_1417_, v_cls_1418_, v_collapsed_1419_, v_tag_1420_, v___x_1421_, v_fst_1422_, v_snd_1423_, v_msg_1424_, v___f_1425_, v_ref_1426_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_1436_ = _args[0];
lean_object* v_inst_1437_ = _args[1];
lean_object* v_inst_1438_ = _args[2];
lean_object* v_inst_1439_ = _args[3];
lean_object* v_inst_1440_ = _args[4];
lean_object* v_oldTraces_1441_ = _args[5];
lean_object* v_toBind_1442_ = _args[6];
lean_object* v___f_1443_ = _args[7];
lean_object* v_inst_1444_ = _args[8];
lean_object* v_fst_1445_ = _args[9];
lean_object* v_cls_1446_ = _args[10];
lean_object* v_collapsed_1447_ = _args[11];
lean_object* v_tag_1448_ = _args[12];
lean_object* v___x_1449_ = _args[13];
lean_object* v_fst_1450_ = _args[14];
lean_object* v_snd_1451_ = _args[15];
lean_object* v_msg_1452_ = _args[16];
lean_object* v___f_1453_ = _args[17];
lean_object* v_ref_1454_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_1455_; double v_fst_542__boxed_1456_; double v_snd_543__boxed_1457_; lean_object* v_res_1458_; 
v_collapsed_boxed_1455_ = lean_unbox(v_collapsed_1447_);
v_fst_542__boxed_1456_ = lean_unbox_float(v_fst_1450_);
lean_dec_ref(v_fst_1450_);
v_snd_543__boxed_1457_ = lean_unbox_float(v_snd_1451_);
lean_dec_ref(v_snd_1451_);
v_res_1458_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3(v_always_1436_, v_inst_1437_, v_inst_1438_, v_inst_1439_, v_inst_1440_, v_oldTraces_1441_, v_toBind_1442_, v___f_1443_, v_inst_1444_, v_fst_1445_, v_cls_1446_, v_collapsed_boxed_1455_, v_tag_1448_, v___x_1449_, v_fst_542__boxed_1456_, v_snd_543__boxed_1457_, v_msg_1452_, v___f_1453_, v_ref_1454_);
return v_res_1458_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(lean_object* v_inst_1459_, lean_object* v_inst_1460_, lean_object* v_inst_1461_, lean_object* v_inst_1462_, lean_object* v_always_1463_, lean_object* v_inst_1464_, lean_object* v_cls_1465_, uint8_t v_collapsed_1466_, lean_object* v_tag_1467_, lean_object* v_opts_1468_, uint8_t v_clsEnabled_1469_, lean_object* v_oldTraces_1470_, lean_object* v_msg_1471_, lean_object* v_resStartStop_1472_){
_start:
{
lean_object* v___x_1473_; lean_object* v_toApplicative_1474_; lean_object* v_toBind_1475_; lean_object* v___x_1476_; lean_object* v_snd_1477_; lean_object* v_toPure_1478_; lean_object* v_fst_1479_; lean_object* v_fst_1480_; lean_object* v_snd_1481_; lean_object* v___f_1482_; lean_object* v___f_1483_; lean_object* v___f_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___f_1488_; uint8_t v___y_1493_; double v___y_1498_; uint8_t v___x_1503_; 
v___x_1473_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1474_ = lean_ctor_get(v_inst_1459_, 0);
v_toBind_1475_ = lean_ctor_get(v_inst_1459_, 1);
lean_inc_n(v_toBind_1475_, 2);
lean_inc_ref(v_always_1463_);
v___x_1476_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_1463_);
v_snd_1477_ = lean_ctor_get(v_resStartStop_1472_, 1);
lean_inc(v_snd_1477_);
v_toPure_1478_ = lean_ctor_get(v_toApplicative_1474_, 1);
v_fst_1479_ = lean_ctor_get(v_resStartStop_1472_, 0);
lean_inc_n(v_fst_1479_, 2);
lean_dec_ref(v_resStartStop_1472_);
v_fst_1480_ = lean_ctor_get(v_snd_1477_, 0);
lean_inc_n(v_fst_1480_, 2);
v_snd_1481_ = lean_ctor_get(v_snd_1477_, 1);
lean_inc_n(v_snd_1481_, 2);
lean_dec(v_snd_1477_);
lean_inc_ref(v_oldTraces_1470_);
v___f_1482_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1482_, 0, v_oldTraces_1470_);
lean_inc(v_toPure_1478_);
v___f_1483_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1483_, 0, v_toPure_1478_);
lean_inc_ref(v_inst_1459_);
v___f_1484_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1484_, 0, v_inst_1459_);
lean_closure_set(v___f_1484_, 1, v___x_1476_);
lean_closure_set(v___f_1484_, 2, v_fst_1479_);
v___x_1485_ = l_Lean_trace_profiler;
v___x_1486_ = l_Lean_Option_get___redArg(v___x_1473_, v_opts_1468_, v___x_1485_);
v___x_1487_ = lean_box(v_collapsed_1466_);
lean_inc(v___x_1486_);
lean_inc_ref(v___f_1484_);
lean_inc_ref(v_inst_1461_);
lean_inc_ref(v_inst_1460_);
v___f_1488_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__3___boxed), 19, 18);
lean_closure_set(v___f_1488_, 0, v_always_1463_);
lean_closure_set(v___f_1488_, 1, v_inst_1459_);
lean_closure_set(v___f_1488_, 2, v_inst_1460_);
lean_closure_set(v___f_1488_, 3, v_inst_1461_);
lean_closure_set(v___f_1488_, 4, v_inst_1462_);
lean_closure_set(v___f_1488_, 5, v_oldTraces_1470_);
lean_closure_set(v___f_1488_, 6, v_toBind_1475_);
lean_closure_set(v___f_1488_, 7, v___f_1484_);
lean_closure_set(v___f_1488_, 8, v_inst_1464_);
lean_closure_set(v___f_1488_, 9, v_fst_1479_);
lean_closure_set(v___f_1488_, 10, v_cls_1465_);
lean_closure_set(v___f_1488_, 11, v___x_1487_);
lean_closure_set(v___f_1488_, 12, v_tag_1467_);
lean_closure_set(v___f_1488_, 13, v___x_1486_);
lean_closure_set(v___f_1488_, 14, v_fst_1480_);
lean_closure_set(v___f_1488_, 15, v_snd_1481_);
lean_closure_set(v___f_1488_, 16, v_msg_1471_);
lean_closure_set(v___f_1488_, 17, v___f_1483_);
v___x_1503_ = lean_unbox(v___x_1486_);
if (v___x_1503_ == 0)
{
uint8_t v___x_1504_; 
lean_dec(v_snd_1481_);
lean_dec(v_fst_1480_);
v___x_1504_ = lean_unbox(v___x_1486_);
lean_dec(v___x_1486_);
v___y_1493_ = v___x_1504_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
lean_dec(v___x_1486_);
v___x_1505_ = l_Lean_KVMap_instValueNat;
v___x_1506_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1507_ = l_Lean_Option_get___redArg(v___x_1473_, v_opts_1468_, v___x_1506_);
v___x_1508_ = lean_unbox(v___x_1507_);
lean_dec(v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; double v___x_1511_; double v___x_1512_; double v___x_1513_; 
v___x_1509_ = l_Lean_trace_profiler_threshold;
v___x_1510_ = l_Lean_Option_get___redArg(v___x_1505_, v_opts_1468_, v___x_1509_);
v___x_1511_ = lean_float_of_nat(v___x_1510_);
v___x_1512_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_1513_ = lean_float_div(v___x_1511_, v___x_1512_);
v___y_1498_ = v___x_1513_;
goto v___jp_1497_;
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; double v___x_1516_; 
v___x_1514_ = l_Lean_trace_profiler_threshold;
v___x_1515_ = l_Lean_Option_get___redArg(v___x_1505_, v_opts_1468_, v___x_1514_);
v___x_1516_ = lean_float_of_nat(v___x_1515_);
v___y_1498_ = v___x_1516_;
goto v___jp_1497_;
}
}
v___jp_1489_:
{
lean_object* v_getRef_1490_; lean_object* v___x_1491_; 
v_getRef_1490_ = lean_ctor_get(v_inst_1461_, 0);
lean_inc(v_getRef_1490_);
lean_dec_ref(v_inst_1461_);
v___x_1491_ = lean_apply_4(v_toBind_1475_, lean_box(0), lean_box(0), v_getRef_1490_, v___f_1488_);
return v___x_1491_;
}
v___jp_1492_:
{
if (v_clsEnabled_1469_ == 0)
{
if (v___y_1493_ == 0)
{
lean_object* v_modifyTraceState_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec_ref(v___f_1488_);
lean_dec_ref(v_inst_1461_);
v_modifyTraceState_1494_ = lean_ctor_get(v_inst_1460_, 0);
lean_inc(v_modifyTraceState_1494_);
lean_dec_ref(v_inst_1460_);
v___x_1495_ = lean_apply_1(v_modifyTraceState_1494_, v___f_1482_);
v___x_1496_ = lean_apply_4(v_toBind_1475_, lean_box(0), lean_box(0), v___x_1495_, v___f_1484_);
return v___x_1496_;
}
else
{
lean_dec_ref(v___f_1484_);
lean_dec_ref(v___f_1482_);
lean_dec_ref(v_inst_1460_);
goto v___jp_1489_;
}
}
else
{
lean_dec_ref(v___f_1484_);
lean_dec_ref(v___f_1482_);
lean_dec_ref(v_inst_1460_);
goto v___jp_1489_;
}
}
v___jp_1497_:
{
double v___x_1499_; double v___x_1500_; double v___x_1501_; uint8_t v___x_1502_; 
v___x_1499_ = lean_unbox_float(v_snd_1481_);
lean_dec(v_snd_1481_);
v___x_1500_ = lean_unbox_float(v_fst_1480_);
lean_dec(v_fst_1480_);
v___x_1501_ = lean_float_sub(v___x_1499_, v___x_1500_);
v___x_1502_ = lean_float_decLt(v___y_1498_, v___x_1501_);
v___y_1493_ = v___x_1502_;
goto v___jp_1492_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1459_ = stack[0].m_obj;
lean_object* v_inst_1460_ = stack[1].m_obj;
lean_object* v_inst_1461_ = stack[2].m_obj;
lean_object* v_inst_1462_ = stack[3].m_obj;
lean_object* v_always_1463_ = stack[4].m_obj;
lean_object* v_inst_1464_ = stack[5].m_obj;
lean_object* v_cls_1465_ = stack[6].m_obj;
uint8_t v_collapsed_1466_ = stack[7].m_num;
lean_object* v_tag_1467_ = stack[8].m_obj;
lean_object* v_opts_1468_ = stack[9].m_obj;
uint8_t v_clsEnabled_1469_ = stack[10].m_num;
lean_object* v_oldTraces_1470_ = stack[11].m_obj;
lean_object* v_msg_1471_ = stack[12].m_obj;
lean_object* v_resStartStop_1472_ = stack[13].m_obj;
lean_object* v_res_1517_;
v_res_1517_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1459_, v_inst_1460_, v_inst_1461_, v_inst_1462_, v_always_1463_, v_inst_1464_, v_cls_1465_, v_collapsed_1466_, v_tag_1467_, v_opts_1468_, v_clsEnabled_1469_, v_oldTraces_1470_, v_msg_1471_, v_resStartStop_1472_);
stack->m_obj
 = v_res_1517_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___boxed(lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_always_1522_, lean_object* v_inst_1523_, lean_object* v_cls_1524_, lean_object* v_collapsed_1525_, lean_object* v_tag_1526_, lean_object* v_opts_1527_, lean_object* v_clsEnabled_1528_, lean_object* v_oldTraces_1529_, lean_object* v_msg_1530_, lean_object* v_resStartStop_1531_){
_start:
{
uint8_t v_collapsed_boxed_1532_; uint8_t v_clsEnabled_boxed_1533_; lean_object* v_res_1534_; 
v_collapsed_boxed_1532_ = lean_unbox(v_collapsed_1525_);
v_clsEnabled_boxed_1533_ = lean_unbox(v_clsEnabled_1528_);
v_res_1534_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1518_, v_inst_1519_, v_inst_1520_, v_inst_1521_, v_always_1522_, v_inst_1523_, v_cls_1524_, v_collapsed_boxed_1532_, v_tag_1526_, v_opts_1527_, v_clsEnabled_boxed_1533_, v_oldTraces_1529_, v_msg_1530_, v_resStartStop_1531_);
lean_dec_ref(v_opts_1527_);
return v_res_1534_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object* v_00_u03b1_1535_, lean_object* v_m_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_00_u03b5_1541_, lean_object* v_always_1542_, lean_object* v_inst_1543_, lean_object* v_cls_1544_, uint8_t v_collapsed_1545_, lean_object* v_tag_1546_, lean_object* v_opts_1547_, uint8_t v_clsEnabled_1548_, lean_object* v_oldTraces_1549_, lean_object* v_msg_1550_, lean_object* v_resStartStop_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1537_, v_inst_1538_, v_inst_1539_, v_inst_1540_, v_always_1542_, v_inst_1543_, v_cls_1544_, v_collapsed_1545_, v_tag_1546_, v_opts_1547_, v_clsEnabled_1548_, v_oldTraces_1549_, v_msg_1550_, v_resStartStop_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1537_ = stack[2].m_obj;
lean_object* v_inst_1538_ = stack[3].m_obj;
lean_object* v_inst_1539_ = stack[4].m_obj;
lean_object* v_inst_1540_ = stack[5].m_obj;
lean_object* v_always_1542_ = stack[7].m_obj;
lean_object* v_inst_1543_ = stack[8].m_obj;
lean_object* v_cls_1544_ = stack[9].m_obj;
uint8_t v_collapsed_1545_ = stack[10].m_num;
lean_object* v_tag_1546_ = stack[11].m_obj;
lean_object* v_opts_1547_ = stack[12].m_obj;
uint8_t v_clsEnabled_1548_ = stack[13].m_num;
lean_object* v_oldTraces_1549_ = stack[14].m_obj;
lean_object* v_msg_1550_ = stack[15].m_obj;
lean_object* v_resStartStop_1551_ = stack[16].m_obj;
lean_object* v_res_1553_;
v_res_1553_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v_inst_1537_, v_inst_1538_, v_inst_1539_, v_inst_1540_, lean_box(0), v_always_1542_, v_inst_1543_, v_cls_1544_, v_collapsed_1545_, v_tag_1546_, v_opts_1547_, v_clsEnabled_1548_, v_oldTraces_1549_, v_msg_1550_, v_resStartStop_1551_);
stack->m_obj
 = v_res_1553_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_1554_ = _args[0];
lean_object* v_m_1555_ = _args[1];
lean_object* v_inst_1556_ = _args[2];
lean_object* v_inst_1557_ = _args[3];
lean_object* v_inst_1558_ = _args[4];
lean_object* v_inst_1559_ = _args[5];
lean_object* v_00_u03b5_1560_ = _args[6];
lean_object* v_always_1561_ = _args[7];
lean_object* v_inst_1562_ = _args[8];
lean_object* v_cls_1563_ = _args[9];
lean_object* v_collapsed_1564_ = _args[10];
lean_object* v_tag_1565_ = _args[11];
lean_object* v_opts_1566_ = _args[12];
lean_object* v_clsEnabled_1567_ = _args[13];
lean_object* v_oldTraces_1568_ = _args[14];
lean_object* v_msg_1569_ = _args[15];
lean_object* v_resStartStop_1570_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1571_; uint8_t v_clsEnabled_boxed_1572_; lean_object* v_res_1573_; 
v_collapsed_boxed_1571_ = lean_unbox(v_collapsed_1564_);
v_clsEnabled_boxed_1572_ = lean_unbox(v_clsEnabled_1567_);
v_res_1573_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(v_00_u03b1_1554_, v_m_1555_, v_inst_1556_, v_inst_1557_, v_inst_1558_, v_inst_1559_, v_00_u03b5_1560_, v_always_1561_, v_inst_1562_, v_cls_1563_, v_collapsed_boxed_1571_, v_tag_1565_, v_opts_1566_, v_clsEnabled_boxed_1572_, v_oldTraces_1568_, v_msg_1569_, v_resStartStop_1570_);
lean_dec_ref(v_opts_1566_);
return v_res_1573_;
}
}
lean_object* l_Lean_withTraceNode___redArg___lam__0(lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_always_1578_, lean_object* v_inst_1579_, lean_object* v_cls_1580_, uint8_t v_collapsed_1581_, lean_object* v_tag_1582_, lean_object* v_opts_1583_, uint8_t v_clsEnabled_1584_, lean_object* v_oldTraces_1585_, lean_object* v_msg_1586_, lean_object* v_resStartStop_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1574_, v_inst_1575_, v_inst_1576_, v_inst_1577_, v_always_1578_, v_inst_1579_, v_cls_1580_, v_collapsed_1581_, v_tag_1582_, v_opts_1583_, v_clsEnabled_1584_, v_oldTraces_1585_, v_msg_1586_, v_resStartStop_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT void l_Lean_withTraceNode___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1574_ = stack[0].m_obj;
lean_object* v_inst_1575_ = stack[1].m_obj;
lean_object* v_inst_1576_ = stack[2].m_obj;
lean_object* v_inst_1577_ = stack[3].m_obj;
lean_object* v_always_1578_ = stack[4].m_obj;
lean_object* v_inst_1579_ = stack[5].m_obj;
lean_object* v_cls_1580_ = stack[6].m_obj;
uint8_t v_collapsed_1581_ = stack[7].m_num;
lean_object* v_tag_1582_ = stack[8].m_obj;
lean_object* v_opts_1583_ = stack[9].m_obj;
uint8_t v_clsEnabled_1584_ = stack[10].m_num;
lean_object* v_oldTraces_1585_ = stack[11].m_obj;
lean_object* v_msg_1586_ = stack[12].m_obj;
lean_object* v_resStartStop_1587_ = stack[13].m_obj;
lean_object* v_res_1589_;
v_res_1589_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1574_, v_inst_1575_, v_inst_1576_, v_inst_1577_, v_always_1578_, v_inst_1579_, v_cls_1580_, v_collapsed_1581_, v_tag_1582_, v_opts_1583_, v_clsEnabled_1584_, v_oldTraces_1585_, v_msg_1586_, v_resStartStop_1587_);
stack->m_obj
 = v_res_1589_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__0___boxed(lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_always_1594_, lean_object* v_inst_1595_, lean_object* v_cls_1596_, lean_object* v_collapsed_1597_, lean_object* v_tag_1598_, lean_object* v_opts_1599_, lean_object* v_clsEnabled_1600_, lean_object* v_oldTraces_1601_, lean_object* v_msg_1602_, lean_object* v_resStartStop_1603_){
_start:
{
uint8_t v_collapsed_boxed_1604_; uint8_t v_clsEnabled_boxed_1605_; lean_object* v_res_1606_; 
v_collapsed_boxed_1604_ = lean_unbox(v_collapsed_1597_);
v_clsEnabled_boxed_1605_ = lean_unbox(v_clsEnabled_1600_);
v_res_1606_ = l_Lean_withTraceNode___redArg___lam__0(v_inst_1590_, v_inst_1591_, v_inst_1592_, v_inst_1593_, v_always_1594_, v_inst_1595_, v_cls_1596_, v_collapsed_boxed_1604_, v_tag_1598_, v_opts_1599_, v_clsEnabled_boxed_1605_, v_oldTraces_1601_, v_msg_1602_, v_resStartStop_1603_);
lean_dec_ref(v_opts_1599_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__1(lean_object* v_toPure_1607_, lean_object* v_ex_1608_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_ex_1608_);
v___x_1610_ = lean_apply_2(v_toPure_1607_, lean_box(0), v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__2(lean_object* v_toPure_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1613_, 0, v_a_1612_);
v___x_1614_ = lean_apply_2(v_toPure_1611_, lean_box(0), v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__3(lean_object* v_start_1615_, lean_object* v_a_1616_, lean_object* v_toPure_1617_, lean_object* v_stop_1618_){
_start:
{
double v___x_1619_; double v___x_1620_; double v___x_1621_; double v___x_1622_; double v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1619_ = lean_float_of_nat(v_start_1615_);
v___x_1620_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1621_ = lean_float_div(v___x_1619_, v___x_1620_);
v___x_1622_ = lean_float_of_nat(v_stop_1618_);
v___x_1623_ = lean_float_div(v___x_1622_, v___x_1620_);
v___x_1624_ = lean_box_float(v___x_1621_);
v___x_1625_ = lean_box_float(v___x_1623_);
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v_a_1616_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = lean_apply_2(v_toPure_1617_, lean_box(0), v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__4(lean_object* v_start_1629_, lean_object* v_toPure_1630_, lean_object* v_toBind_1631_, lean_object* v___x_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___f_1634_; lean_object* v___x_1635_; 
v___f_1634_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1634_, 0, v_start_1629_);
lean_closure_set(v___f_1634_, 1, v_a_1633_);
lean_closure_set(v___f_1634_, 2, v_toPure_1630_);
v___x_1635_ = lean_apply_4(v_toBind_1631_, lean_box(0), lean_box(0), v___x_1632_, v___f_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__5(lean_object* v_toPure_1636_, lean_object* v_toBind_1637_, lean_object* v___x_1638_, lean_object* v___x_1639_, lean_object* v_start_1640_){
_start:
{
lean_object* v___f_1641_; lean_object* v___x_1642_; 
lean_inc(v_toBind_1637_);
v___f_1641_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1641_, 0, v_start_1640_);
lean_closure_set(v___f_1641_, 1, v_toPure_1636_);
lean_closure_set(v___f_1641_, 2, v_toBind_1637_);
lean_closure_set(v___f_1641_, 3, v___x_1638_);
v___x_1642_ = lean_apply_4(v_toBind_1637_, lean_box(0), lean_box(0), v___x_1639_, v___f_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__6(lean_object* v_start_1643_, lean_object* v_a_1644_, lean_object* v_toPure_1645_, lean_object* v_stop_1646_){
_start:
{
double v___x_1647_; double v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1647_ = lean_float_of_nat(v_start_1643_);
v___x_1648_ = lean_float_of_nat(v_stop_1646_);
v___x_1649_ = lean_box_float(v___x_1647_);
v___x_1650_ = lean_box_float(v___x_1648_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v_a_1644_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_apply_2(v_toPure_1645_, lean_box(0), v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__7(lean_object* v_start_1654_, lean_object* v_toPure_1655_, lean_object* v_toBind_1656_, lean_object* v___x_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___f_1659_; lean_object* v___x_1660_; 
v___f_1659_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__6), 4, 3);
lean_closure_set(v___f_1659_, 0, v_start_1654_);
lean_closure_set(v___f_1659_, 1, v_a_1658_);
lean_closure_set(v___f_1659_, 2, v_toPure_1655_);
v___x_1660_ = lean_apply_4(v_toBind_1656_, lean_box(0), lean_box(0), v___x_1657_, v___f_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__8(lean_object* v_toPure_1661_, lean_object* v_toBind_1662_, lean_object* v___x_1663_, lean_object* v___x_1664_, lean_object* v_start_1665_){
_start:
{
lean_object* v___f_1666_; lean_object* v___x_1667_; 
lean_inc(v_toBind_1662_);
v___f_1666_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__7), 5, 4);
lean_closure_set(v___f_1666_, 0, v_start_1665_);
lean_closure_set(v___f_1666_, 1, v_toPure_1661_);
lean_closure_set(v___f_1666_, 2, v_toBind_1662_);
lean_closure_set(v___f_1666_, 3, v___x_1663_);
v___x_1667_ = lean_apply_4(v_toBind_1662_, lean_box(0), lean_box(0), v___x_1664_, v___f_1666_);
return v___x_1667_;
}
}
lean_object* l_Lean_withTraceNode___redArg___lam__9(lean_object* v_always_1668_, lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_cls_1674_, uint8_t v_collapsed_1675_, lean_object* v_tag_1676_, lean_object* v_opts_1677_, uint8_t v_clsEnabled_1678_, lean_object* v_msg_1679_, lean_object* v_toPure_1680_, lean_object* v_toBind_1681_, lean_object* v_k_1682_, lean_object* v___x_1683_, lean_object* v_inst_1684_, lean_object* v_oldTraces_1685_){
_start:
{
lean_object* v_tryCatch_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v_tryCatch_1686_ = lean_ctor_get(v_always_1668_, 1);
lean_inc(v_tryCatch_1686_);
v___x_1687_ = lean_box(v_collapsed_1675_);
v___x_1688_ = lean_box(v_clsEnabled_1678_);
lean_inc_ref(v_opts_1677_);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__0___boxed), 14, 13);
lean_closure_set(v___f_1689_, 0, v_inst_1669_);
lean_closure_set(v___f_1689_, 1, v_inst_1670_);
lean_closure_set(v___f_1689_, 2, v_inst_1671_);
lean_closure_set(v___f_1689_, 3, v_inst_1672_);
lean_closure_set(v___f_1689_, 4, v_always_1668_);
lean_closure_set(v___f_1689_, 5, v_inst_1673_);
lean_closure_set(v___f_1689_, 6, v_cls_1674_);
lean_closure_set(v___f_1689_, 7, v___x_1687_);
lean_closure_set(v___f_1689_, 8, v_tag_1676_);
lean_closure_set(v___f_1689_, 9, v_opts_1677_);
lean_closure_set(v___f_1689_, 10, v___x_1688_);
lean_closure_set(v___f_1689_, 11, v_oldTraces_1685_);
lean_closure_set(v___f_1689_, 12, v_msg_1679_);
lean_inc_n(v_toPure_1680_, 2);
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1690_, 0, v_toPure_1680_);
v___f_1691_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1691_, 0, v_toPure_1680_);
lean_inc(v_toBind_1681_);
v___x_1692_ = lean_apply_4(v_toBind_1681_, lean_box(0), lean_box(0), v_k_1682_, v___f_1691_);
v___x_1693_ = lean_apply_3(v_tryCatch_1686_, lean_box(0), v___x_1692_, v___f_1690_);
v___x_1694_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1695_ = l_Lean_Option_get___redArg(v___x_1683_, v_opts_1677_, v___x_1694_);
lean_dec_ref(v_opts_1677_);
v___x_1696_ = lean_unbox(v___x_1695_);
lean_dec(v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___f_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1697_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_1698_ = lean_apply_2(v_inst_1684_, lean_box(0), v___x_1697_);
lean_inc(v___x_1698_);
lean_inc_n(v_toBind_1681_, 2);
v___f_1699_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1699_, 0, v_toPure_1680_);
lean_closure_set(v___f_1699_, 1, v_toBind_1681_);
lean_closure_set(v___f_1699_, 2, v___x_1698_);
lean_closure_set(v___f_1699_, 3, v___x_1693_);
v___x_1700_ = lean_apply_4(v_toBind_1681_, lean_box(0), lean_box(0), v___x_1698_, v___f_1699_);
v___x_1701_ = lean_apply_4(v_toBind_1681_, lean_box(0), lean_box(0), v___x_1700_, v___f_1689_);
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1702_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_1703_ = lean_apply_2(v_inst_1684_, lean_box(0), v___x_1702_);
lean_inc(v___x_1703_);
lean_inc_n(v_toBind_1681_, 2);
v___f_1704_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_1704_, 0, v_toPure_1680_);
lean_closure_set(v___f_1704_, 1, v_toBind_1681_);
lean_closure_set(v___f_1704_, 2, v___x_1703_);
lean_closure_set(v___f_1704_, 3, v___x_1693_);
v___x_1705_ = lean_apply_4(v_toBind_1681_, lean_box(0), lean_box(0), v___x_1703_, v___f_1704_);
v___x_1706_ = lean_apply_4(v_toBind_1681_, lean_box(0), lean_box(0), v___x_1705_, v___f_1689_);
return v___x_1706_;
}
}
}
LEAN_EXPORT void l_Lean_withTraceNode___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_always_1668_ = stack[0].m_obj;
lean_object* v_inst_1669_ = stack[1].m_obj;
lean_object* v_inst_1670_ = stack[2].m_obj;
lean_object* v_inst_1671_ = stack[3].m_obj;
lean_object* v_inst_1672_ = stack[4].m_obj;
lean_object* v_inst_1673_ = stack[5].m_obj;
lean_object* v_cls_1674_ = stack[6].m_obj;
uint8_t v_collapsed_1675_ = stack[7].m_num;
lean_object* v_tag_1676_ = stack[8].m_obj;
lean_object* v_opts_1677_ = stack[9].m_obj;
uint8_t v_clsEnabled_1678_ = stack[10].m_num;
lean_object* v_msg_1679_ = stack[11].m_obj;
lean_object* v_toPure_1680_ = stack[12].m_obj;
lean_object* v_toBind_1681_ = stack[13].m_obj;
lean_object* v_k_1682_ = stack[14].m_obj;
lean_object* v___x_1683_ = stack[15].m_obj;
lean_object* v_inst_1684_ = stack[16].m_obj;
lean_object* v_oldTraces_1685_ = stack[17].m_obj;
lean_object* v_res_1707_;
v_res_1707_ = l_Lean_withTraceNode___redArg___lam__9(v_always_1668_, v_inst_1669_, v_inst_1670_, v_inst_1671_, v_inst_1672_, v_inst_1673_, v_cls_1674_, v_collapsed_1675_, v_tag_1676_, v_opts_1677_, v_clsEnabled_1678_, v_msg_1679_, v_toPure_1680_, v_toBind_1681_, v_k_1682_, v___x_1683_, v_inst_1684_, v_oldTraces_1685_);
stack->m_obj
 = v_res_1707_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_always_1708_ = _args[0];
lean_object* v_inst_1709_ = _args[1];
lean_object* v_inst_1710_ = _args[2];
lean_object* v_inst_1711_ = _args[3];
lean_object* v_inst_1712_ = _args[4];
lean_object* v_inst_1713_ = _args[5];
lean_object* v_cls_1714_ = _args[6];
lean_object* v_collapsed_1715_ = _args[7];
lean_object* v_tag_1716_ = _args[8];
lean_object* v_opts_1717_ = _args[9];
lean_object* v_clsEnabled_1718_ = _args[10];
lean_object* v_msg_1719_ = _args[11];
lean_object* v_toPure_1720_ = _args[12];
lean_object* v_toBind_1721_ = _args[13];
lean_object* v_k_1722_ = _args[14];
lean_object* v___x_1723_ = _args[15];
lean_object* v_inst_1724_ = _args[16];
lean_object* v_oldTraces_1725_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_1726_; uint8_t v_clsEnabled_boxed_1727_; lean_object* v_res_1728_; 
v_collapsed_boxed_1726_ = lean_unbox(v_collapsed_1715_);
v_clsEnabled_boxed_1727_ = lean_unbox(v_clsEnabled_1718_);
v_res_1728_ = l_Lean_withTraceNode___redArg___lam__9(v_always_1708_, v_inst_1709_, v_inst_1710_, v_inst_1711_, v_inst_1712_, v_inst_1713_, v_cls_1714_, v_collapsed_boxed_1726_, v_tag_1716_, v_opts_1717_, v_clsEnabled_boxed_1727_, v_msg_1719_, v_toPure_1720_, v_toBind_1721_, v_k_1722_, v___x_1723_, v_inst_1724_, v_oldTraces_1725_);
return v_res_1728_;
}
}
lean_object* l_Lean_withTraceNode___redArg___lam__10(lean_object* v_always_1729_, lean_object* v_inst_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_cls_1735_, uint8_t v_collapsed_1736_, lean_object* v_tag_1737_, lean_object* v_opts_1738_, lean_object* v_msg_1739_, lean_object* v_toPure_1740_, lean_object* v_toBind_1741_, lean_object* v_k_1742_, lean_object* v___x_1743_, lean_object* v_inst_1744_, uint8_t v_clsEnabled_1745_){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___f_1748_; 
v___x_1746_ = lean_box(v_collapsed_1736_);
v___x_1747_ = lean_box(v_clsEnabled_1745_);
lean_inc_ref(v___x_1743_);
lean_inc(v_k_1742_);
lean_inc(v_toBind_1741_);
lean_inc_ref(v_opts_1738_);
lean_inc_ref(v_inst_1731_);
lean_inc_ref(v_inst_1730_);
v___f_1748_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__9___boxed), 18, 17);
lean_closure_set(v___f_1748_, 0, v_always_1729_);
lean_closure_set(v___f_1748_, 1, v_inst_1730_);
lean_closure_set(v___f_1748_, 2, v_inst_1731_);
lean_closure_set(v___f_1748_, 3, v_inst_1732_);
lean_closure_set(v___f_1748_, 4, v_inst_1733_);
lean_closure_set(v___f_1748_, 5, v_inst_1734_);
lean_closure_set(v___f_1748_, 6, v_cls_1735_);
lean_closure_set(v___f_1748_, 7, v___x_1746_);
lean_closure_set(v___f_1748_, 8, v_tag_1737_);
lean_closure_set(v___f_1748_, 9, v_opts_1738_);
lean_closure_set(v___f_1748_, 10, v___x_1747_);
lean_closure_set(v___f_1748_, 11, v_msg_1739_);
lean_closure_set(v___f_1748_, 12, v_toPure_1740_);
lean_closure_set(v___f_1748_, 13, v_toBind_1741_);
lean_closure_set(v___f_1748_, 14, v_k_1742_);
lean_closure_set(v___f_1748_, 15, v___x_1743_);
lean_closure_set(v___f_1748_, 16, v_inst_1744_);
if (v_clsEnabled_1745_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1752_ = l_Lean_trace_profiler;
v___x_1753_ = l_Lean_Option_get___redArg(v___x_1743_, v_opts_1738_, v___x_1752_);
lean_dec_ref(v_opts_1738_);
v___x_1754_ = lean_unbox(v___x_1753_);
lean_dec(v___x_1753_);
if (v___x_1754_ == 0)
{
lean_dec_ref(v___f_1748_);
lean_dec(v_toBind_1741_);
lean_dec_ref(v_inst_1731_);
lean_dec_ref(v_inst_1730_);
return v_k_1742_;
}
else
{
lean_dec(v_k_1742_);
goto v___jp_1749_;
}
}
else
{
lean_dec_ref(v___x_1743_);
lean_dec(v_k_1742_);
lean_dec_ref(v_opts_1738_);
goto v___jp_1749_;
}
v___jp_1749_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_1730_, v_inst_1731_);
v___x_1751_ = lean_apply_4(v_toBind_1741_, lean_box(0), lean_box(0), v___x_1750_, v___f_1748_);
return v___x_1751_;
}
}
}
LEAN_EXPORT void l_Lean_withTraceNode___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_always_1729_ = stack[0].m_obj;
lean_object* v_inst_1730_ = stack[1].m_obj;
lean_object* v_inst_1731_ = stack[2].m_obj;
lean_object* v_inst_1732_ = stack[3].m_obj;
lean_object* v_inst_1733_ = stack[4].m_obj;
lean_object* v_inst_1734_ = stack[5].m_obj;
lean_object* v_cls_1735_ = stack[6].m_obj;
uint8_t v_collapsed_1736_ = stack[7].m_num;
lean_object* v_tag_1737_ = stack[8].m_obj;
lean_object* v_opts_1738_ = stack[9].m_obj;
lean_object* v_msg_1739_ = stack[10].m_obj;
lean_object* v_toPure_1740_ = stack[11].m_obj;
lean_object* v_toBind_1741_ = stack[12].m_obj;
lean_object* v_k_1742_ = stack[13].m_obj;
lean_object* v___x_1743_ = stack[14].m_obj;
lean_object* v_inst_1744_ = stack[15].m_obj;
uint8_t v_clsEnabled_1745_ = stack[16].m_num;
lean_object* v_res_1755_;
v_res_1755_ = l_Lean_withTraceNode___redArg___lam__10(v_always_1729_, v_inst_1730_, v_inst_1731_, v_inst_1732_, v_inst_1733_, v_inst_1734_, v_cls_1735_, v_collapsed_1736_, v_tag_1737_, v_opts_1738_, v_msg_1739_, v_toPure_1740_, v_toBind_1741_, v_k_1742_, v___x_1743_, v_inst_1744_, v_clsEnabled_1745_);
stack->m_obj
 = v_res_1755_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_1756_ = _args[0];
lean_object* v_inst_1757_ = _args[1];
lean_object* v_inst_1758_ = _args[2];
lean_object* v_inst_1759_ = _args[3];
lean_object* v_inst_1760_ = _args[4];
lean_object* v_inst_1761_ = _args[5];
lean_object* v_cls_1762_ = _args[6];
lean_object* v_collapsed_1763_ = _args[7];
lean_object* v_tag_1764_ = _args[8];
lean_object* v_opts_1765_ = _args[9];
lean_object* v_msg_1766_ = _args[10];
lean_object* v_toPure_1767_ = _args[11];
lean_object* v_toBind_1768_ = _args[12];
lean_object* v_k_1769_ = _args[13];
lean_object* v___x_1770_ = _args[14];
lean_object* v_inst_1771_ = _args[15];
lean_object* v_clsEnabled_1772_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1773_; uint8_t v_clsEnabled_boxed_1774_; lean_object* v_res_1775_; 
v_collapsed_boxed_1773_ = lean_unbox(v_collapsed_1763_);
v_clsEnabled_boxed_1774_ = lean_unbox(v_clsEnabled_1772_);
v_res_1775_ = l_Lean_withTraceNode___redArg___lam__10(v_always_1756_, v_inst_1757_, v_inst_1758_, v_inst_1759_, v_inst_1760_, v_inst_1761_, v_cls_1762_, v_collapsed_boxed_1773_, v_tag_1764_, v_opts_1765_, v_msg_1766_, v_toPure_1767_, v_toBind_1768_, v_k_1769_, v___x_1770_, v_inst_1771_, v_clsEnabled_boxed_1774_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__12(lean_object* v_toPure_1776_, lean_object* v_cls_1777_, lean_object* v_toBind_1778_, lean_object* v_getOptionsUnrestricted_1779_, lean_object* v_____do__lift_1780_){
_start:
{
lean_object* v___f_1781_; lean_object* v___x_1782_; 
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_isTracingEnabledFor___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1781_, 0, v_toPure_1776_);
lean_closure_set(v___f_1781_, 1, v_cls_1777_);
lean_closure_set(v___f_1781_, 2, v_____do__lift_1780_);
v___x_1782_ = lean_apply_4(v_toBind_1778_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_1779_, v___f_1781_);
return v___x_1782_;
}
}
lean_object* l_Lean_withTraceNode___redArg___lam__11(lean_object* v_k_1783_, lean_object* v_inst_1784_, lean_object* v_toApplicative_1785_, lean_object* v_always_1786_, lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_cls_1791_, uint8_t v_collapsed_1792_, lean_object* v_tag_1793_, lean_object* v_msg_1794_, lean_object* v_toBind_1795_, lean_object* v___x_1796_, lean_object* v_inst_1797_, lean_object* v_getOptionsUnrestricted_1798_, lean_object* v_opts_1799_){
_start:
{
uint8_t v_hasTrace_1800_; 
v_hasTrace_1800_ = lean_ctor_get_uint8(v_opts_1799_, sizeof(void*)*1);
if (v_hasTrace_1800_ == 0)
{
lean_dec_ref(v_opts_1799_);
lean_dec(v_getOptionsUnrestricted_1798_);
lean_dec(v_inst_1797_);
lean_dec_ref(v___x_1796_);
lean_dec(v_toBind_1795_);
lean_dec(v_msg_1794_);
lean_dec_ref(v_tag_1793_);
lean_dec(v_cls_1791_);
lean_dec_ref(v_inst_1790_);
lean_dec(v_inst_1789_);
lean_dec_ref(v_inst_1788_);
lean_dec_ref(v_inst_1787_);
lean_dec_ref(v_always_1786_);
lean_dec_ref(v_toApplicative_1785_);
lean_dec_ref(v_inst_1784_);
return v_k_1783_;
}
else
{
lean_object* v_getInheritedTraceOptions_1801_; lean_object* v_toPure_1802_; lean_object* v___x_1803_; lean_object* v___f_1804_; lean_object* v___f_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v_getInheritedTraceOptions_1801_ = lean_ctor_get(v_inst_1784_, 2);
lean_inc(v_getInheritedTraceOptions_1801_);
v_toPure_1802_ = lean_ctor_get(v_toApplicative_1785_, 1);
lean_inc_n(v_toPure_1802_, 2);
lean_dec_ref(v_toApplicative_1785_);
v___x_1803_ = lean_box(v_collapsed_1792_);
lean_inc_n(v_toBind_1795_, 3);
lean_inc(v_cls_1791_);
v___f_1804_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__10___boxed), 17, 16);
lean_closure_set(v___f_1804_, 0, v_always_1786_);
lean_closure_set(v___f_1804_, 1, v_inst_1787_);
lean_closure_set(v___f_1804_, 2, v_inst_1784_);
lean_closure_set(v___f_1804_, 3, v_inst_1788_);
lean_closure_set(v___f_1804_, 4, v_inst_1789_);
lean_closure_set(v___f_1804_, 5, v_inst_1790_);
lean_closure_set(v___f_1804_, 6, v_cls_1791_);
lean_closure_set(v___f_1804_, 7, v___x_1803_);
lean_closure_set(v___f_1804_, 8, v_tag_1793_);
lean_closure_set(v___f_1804_, 9, v_opts_1799_);
lean_closure_set(v___f_1804_, 10, v_msg_1794_);
lean_closure_set(v___f_1804_, 11, v_toPure_1802_);
lean_closure_set(v___f_1804_, 12, v_toBind_1795_);
lean_closure_set(v___f_1804_, 13, v_k_1783_);
lean_closure_set(v___f_1804_, 14, v___x_1796_);
lean_closure_set(v___f_1804_, 15, v_inst_1797_);
v___f_1805_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__12), 5, 4);
lean_closure_set(v___f_1805_, 0, v_toPure_1802_);
lean_closure_set(v___f_1805_, 1, v_cls_1791_);
lean_closure_set(v___f_1805_, 2, v_toBind_1795_);
lean_closure_set(v___f_1805_, 3, v_getOptionsUnrestricted_1798_);
v___x_1806_ = lean_apply_4(v_toBind_1795_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_1801_, v___f_1805_);
v___x_1807_ = lean_apply_4(v_toBind_1795_, lean_box(0), lean_box(0), v___x_1806_, v___f_1804_);
return v___x_1807_;
}
}
}
LEAN_EXPORT void l_Lean_withTraceNode___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1783_ = stack[0].m_obj;
lean_object* v_inst_1784_ = stack[1].m_obj;
lean_object* v_toApplicative_1785_ = stack[2].m_obj;
lean_object* v_always_1786_ = stack[3].m_obj;
lean_object* v_inst_1787_ = stack[4].m_obj;
lean_object* v_inst_1788_ = stack[5].m_obj;
lean_object* v_inst_1789_ = stack[6].m_obj;
lean_object* v_inst_1790_ = stack[7].m_obj;
lean_object* v_cls_1791_ = stack[8].m_obj;
uint8_t v_collapsed_1792_ = stack[9].m_num;
lean_object* v_tag_1793_ = stack[10].m_obj;
lean_object* v_msg_1794_ = stack[11].m_obj;
lean_object* v_toBind_1795_ = stack[12].m_obj;
lean_object* v___x_1796_ = stack[13].m_obj;
lean_object* v_inst_1797_ = stack[14].m_obj;
lean_object* v_getOptionsUnrestricted_1798_ = stack[15].m_obj;
lean_object* v_opts_1799_ = stack[16].m_obj;
lean_object* v_res_1808_;
v_res_1808_ = l_Lean_withTraceNode___redArg___lam__11(v_k_1783_, v_inst_1784_, v_toApplicative_1785_, v_always_1786_, v_inst_1787_, v_inst_1788_, v_inst_1789_, v_inst_1790_, v_cls_1791_, v_collapsed_1792_, v_tag_1793_, v_msg_1794_, v_toBind_1795_, v___x_1796_, v_inst_1797_, v_getOptionsUnrestricted_1798_, v_opts_1799_);
stack->m_obj
 = v_res_1808_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_k_1809_ = _args[0];
lean_object* v_inst_1810_ = _args[1];
lean_object* v_toApplicative_1811_ = _args[2];
lean_object* v_always_1812_ = _args[3];
lean_object* v_inst_1813_ = _args[4];
lean_object* v_inst_1814_ = _args[5];
lean_object* v_inst_1815_ = _args[6];
lean_object* v_inst_1816_ = _args[7];
lean_object* v_cls_1817_ = _args[8];
lean_object* v_collapsed_1818_ = _args[9];
lean_object* v_tag_1819_ = _args[10];
lean_object* v_msg_1820_ = _args[11];
lean_object* v_toBind_1821_ = _args[12];
lean_object* v___x_1822_ = _args[13];
lean_object* v_inst_1823_ = _args[14];
lean_object* v_getOptionsUnrestricted_1824_ = _args[15];
lean_object* v_opts_1825_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1826_; lean_object* v_res_1827_; 
v_collapsed_boxed_1826_ = lean_unbox(v_collapsed_1818_);
v_res_1827_ = l_Lean_withTraceNode___redArg___lam__11(v_k_1809_, v_inst_1810_, v_toApplicative_1811_, v_always_1812_, v_inst_1813_, v_inst_1814_, v_inst_1815_, v_inst_1816_, v_cls_1817_, v_collapsed_boxed_1826_, v_tag_1819_, v_msg_1820_, v_toBind_1821_, v___x_1822_, v_inst_1823_, v_getOptionsUnrestricted_1824_, v_opts_1825_);
return v_res_1827_;
}
}
lean_object* l_Lean_withTraceNode___redArg(lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_always_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_cls_1836_, lean_object* v_msg_1837_, lean_object* v_k_1838_, uint8_t v_collapsed_1839_, lean_object* v_tag_1840_){
_start:
{
lean_object* v___x_1841_; lean_object* v_toApplicative_1842_; lean_object* v_toBind_1843_; lean_object* v_getOptionsUnrestricted_1844_; lean_object* v___x_1845_; lean_object* v___f_1846_; lean_object* v___x_1847_; 
v___x_1841_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1842_ = lean_ctor_get(v_inst_1828_, 0);
lean_inc_ref(v_toApplicative_1842_);
v_toBind_1843_ = lean_ctor_get(v_inst_1828_, 1);
lean_inc_n(v_toBind_1843_, 2);
v_getOptionsUnrestricted_1844_ = lean_ctor_get(v_inst_1832_, 1);
lean_inc_n(v_getOptionsUnrestricted_1844_, 2);
lean_dec_ref(v_inst_1832_);
v___x_1845_ = lean_box(v_collapsed_1839_);
v___f_1846_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_1846_, 0, v_k_1838_);
lean_closure_set(v___f_1846_, 1, v_inst_1829_);
lean_closure_set(v___f_1846_, 2, v_toApplicative_1842_);
lean_closure_set(v___f_1846_, 3, v_always_1833_);
lean_closure_set(v___f_1846_, 4, v_inst_1828_);
lean_closure_set(v___f_1846_, 5, v_inst_1830_);
lean_closure_set(v___f_1846_, 6, v_inst_1831_);
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
LEAN_EXPORT void l_Lean_withTraceNode___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1828_ = stack[0].m_obj;
lean_object* v_inst_1829_ = stack[1].m_obj;
lean_object* v_inst_1830_ = stack[2].m_obj;
lean_object* v_inst_1831_ = stack[3].m_obj;
lean_object* v_inst_1832_ = stack[4].m_obj;
lean_object* v_always_1833_ = stack[5].m_obj;
lean_object* v_inst_1834_ = stack[6].m_obj;
lean_object* v_inst_1835_ = stack[7].m_obj;
lean_object* v_cls_1836_ = stack[8].m_obj;
lean_object* v_msg_1837_ = stack[9].m_obj;
lean_object* v_k_1838_ = stack[10].m_obj;
uint8_t v_collapsed_1839_ = stack[11].m_num;
lean_object* v_tag_1840_ = stack[12].m_obj;
lean_object* v_res_1848_;
v_res_1848_ = l_Lean_withTraceNode___redArg(v_inst_1828_, v_inst_1829_, v_inst_1830_, v_inst_1831_, v_inst_1832_, v_always_1833_, v_inst_1834_, v_inst_1835_, v_cls_1836_, v_msg_1837_, v_k_1838_, v_collapsed_1839_, v_tag_1840_);
stack->m_obj
 = v_res_1848_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___redArg___boxed(lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_always_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_cls_1857_, lean_object* v_msg_1858_, lean_object* v_k_1859_, lean_object* v_collapsed_1860_, lean_object* v_tag_1861_){
_start:
{
uint8_t v_collapsed_boxed_1862_; lean_object* v_res_1863_; 
v_collapsed_boxed_1862_ = lean_unbox(v_collapsed_1860_);
v_res_1863_ = l_Lean_withTraceNode___redArg(v_inst_1849_, v_inst_1850_, v_inst_1851_, v_inst_1852_, v_inst_1853_, v_always_1854_, v_inst_1855_, v_inst_1856_, v_cls_1857_, v_msg_1858_, v_k_1859_, v_collapsed_boxed_1862_, v_tag_1861_);
return v_res_1863_;
}
}
lean_object* l_Lean_withTraceNode(lean_object* v_00_u03b1_1864_, lean_object* v_m_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_00_u03b5_1871_, lean_object* v_always_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_cls_1875_, lean_object* v_msg_1876_, lean_object* v_k_1877_, uint8_t v_collapsed_1878_, lean_object* v_tag_1879_){
_start:
{
lean_object* v___x_1880_; lean_object* v_toApplicative_1881_; lean_object* v_toBind_1882_; lean_object* v_getOptionsUnrestricted_1883_; lean_object* v___x_1884_; lean_object* v___f_1885_; lean_object* v___x_1886_; 
v___x_1880_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1881_ = lean_ctor_get(v_inst_1866_, 0);
lean_inc_ref(v_toApplicative_1881_);
v_toBind_1882_ = lean_ctor_get(v_inst_1866_, 1);
lean_inc_n(v_toBind_1882_, 2);
v_getOptionsUnrestricted_1883_ = lean_ctor_get(v_inst_1870_, 1);
lean_inc_n(v_getOptionsUnrestricted_1883_, 2);
lean_dec_ref(v_inst_1870_);
v___x_1884_ = lean_box(v_collapsed_1878_);
v___f_1885_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__11___boxed), 17, 16);
lean_closure_set(v___f_1885_, 0, v_k_1877_);
lean_closure_set(v___f_1885_, 1, v_inst_1867_);
lean_closure_set(v___f_1885_, 2, v_toApplicative_1881_);
lean_closure_set(v___f_1885_, 3, v_always_1872_);
lean_closure_set(v___f_1885_, 4, v_inst_1866_);
lean_closure_set(v___f_1885_, 5, v_inst_1868_);
lean_closure_set(v___f_1885_, 6, v_inst_1869_);
lean_closure_set(v___f_1885_, 7, v_inst_1874_);
lean_closure_set(v___f_1885_, 8, v_cls_1875_);
lean_closure_set(v___f_1885_, 9, v___x_1884_);
lean_closure_set(v___f_1885_, 10, v_tag_1879_);
lean_closure_set(v___f_1885_, 11, v_msg_1876_);
lean_closure_set(v___f_1885_, 12, v_toBind_1882_);
lean_closure_set(v___f_1885_, 13, v___x_1880_);
lean_closure_set(v___f_1885_, 14, v_inst_1873_);
lean_closure_set(v___f_1885_, 15, v_getOptionsUnrestricted_1883_);
v___x_1886_ = lean_apply_4(v_toBind_1882_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_1883_, v___f_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT void l_Lean_withTraceNode_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1866_ = stack[2].m_obj;
lean_object* v_inst_1867_ = stack[3].m_obj;
lean_object* v_inst_1868_ = stack[4].m_obj;
lean_object* v_inst_1869_ = stack[5].m_obj;
lean_object* v_inst_1870_ = stack[6].m_obj;
lean_object* v_always_1872_ = stack[8].m_obj;
lean_object* v_inst_1873_ = stack[9].m_obj;
lean_object* v_inst_1874_ = stack[10].m_obj;
lean_object* v_cls_1875_ = stack[11].m_obj;
lean_object* v_msg_1876_ = stack[12].m_obj;
lean_object* v_k_1877_ = stack[13].m_obj;
uint8_t v_collapsed_1878_ = stack[14].m_num;
lean_object* v_tag_1879_ = stack[15].m_obj;
lean_object* v_res_1887_;
v_res_1887_ = l_Lean_withTraceNode(lean_box(0), lean_box(0), v_inst_1866_, v_inst_1867_, v_inst_1868_, v_inst_1869_, v_inst_1870_, lean_box(0), v_always_1872_, v_inst_1873_, v_inst_1874_, v_cls_1875_, v_msg_1876_, v_k_1877_, v_collapsed_1878_, v_tag_1879_);
stack->m_obj
 = v_res_1887_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___boxed(lean_object* v_00_u03b1_1888_, lean_object* v_m_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_inst_1892_, lean_object* v_inst_1893_, lean_object* v_inst_1894_, lean_object* v_00_u03b5_1895_, lean_object* v_always_1896_, lean_object* v_inst_1897_, lean_object* v_inst_1898_, lean_object* v_cls_1899_, lean_object* v_msg_1900_, lean_object* v_k_1901_, lean_object* v_collapsed_1902_, lean_object* v_tag_1903_){
_start:
{
uint8_t v_collapsed_boxed_1904_; lean_object* v_res_1905_; 
v_collapsed_boxed_1904_ = lean_unbox(v_collapsed_1902_);
v_res_1905_ = l_Lean_withTraceNode(v_00_u03b1_1888_, v_m_1889_, v_inst_1890_, v_inst_1891_, v_inst_1892_, v_inst_1893_, v_inst_1894_, v_00_u03b5_1895_, v_always_1896_, v_inst_1897_, v_inst_1898_, v_cls_1899_, v_msg_1900_, v_k_1901_, v_collapsed_boxed_1904_, v_tag_1903_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0(lean_object* v_self_1906_){
_start:
{
lean_object* v_fst_1907_; 
v_fst_1907_ = lean_ctor_get(v_self_1906_, 0);
lean_inc(v_fst_1907_);
return v_fst_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__0___boxed(lean_object* v_self_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_withTraceNode_x27___redArg___lam__0(v_self_1908_);
lean_dec_ref(v_self_1908_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__1(lean_object* v_toPure_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_a_1911_);
v___x_1913_ = lean_apply_2(v_toPure_1910_, lean_box(0), v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__2(lean_object* v_toPure_1914_, lean_object* v_ex_1915_){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_ex_1915_);
v___x_1917_ = lean_apply_2(v_toPure_1914_, lean_box(0), v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__3(lean_object* v_toPure_1918_, lean_object* v_x_1919_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1920_ = lean_ctor_get(v_x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v_x_1919_, 1);
v___x_1921_ = l_Lean_Exception_toMessageData(v_a_1920_);
v___x_1922_ = lean_apply_2(v_toPure_1918_, lean_box(0), v___x_1921_);
return v___x_1922_;
}
else
{
lean_object* v_a_1923_; lean_object* v_snd_1924_; lean_object* v___x_1925_; 
v_a_1923_ = lean_ctor_get(v_x_1919_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v_x_1919_, 1);
v_snd_1924_ = lean_ctor_get(v_a_1923_, 1);
lean_inc(v_snd_1924_);
lean_dec(v_a_1923_);
v___x_1925_ = lean_apply_2(v_toPure_1918_, lean_box(0), v_snd_1924_);
return v___x_1925_;
}
}
}
lean_object* l_Lean_withTraceNode_x27___redArg___lam__6(lean_object* v_inst_1926_, lean_object* v_inst_1927_, lean_object* v_inst_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v___f_1931_, lean_object* v_cls_1932_, uint8_t v_collapsed_1933_, lean_object* v_tag_1934_, lean_object* v_opts_1935_, uint8_t v_clsEnabled_1936_, lean_object* v_oldTraces_1937_, lean_object* v_msg_1938_, lean_object* v_resStartStop_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg(v_inst_1926_, v_inst_1927_, v_inst_1928_, v_inst_1929_, v_inst_1930_, v___f_1931_, v_cls_1932_, v_collapsed_1933_, v_tag_1934_, v_opts_1935_, v_clsEnabled_1936_, v_oldTraces_1937_, v_msg_1938_, v_resStartStop_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT void l_Lean_withTraceNode_x27___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1926_ = stack[0].m_obj;
lean_object* v_inst_1927_ = stack[1].m_obj;
lean_object* v_inst_1928_ = stack[2].m_obj;
lean_object* v_inst_1929_ = stack[3].m_obj;
lean_object* v_inst_1930_ = stack[4].m_obj;
lean_object* v___f_1931_ = stack[5].m_obj;
lean_object* v_cls_1932_ = stack[6].m_obj;
uint8_t v_collapsed_1933_ = stack[7].m_num;
lean_object* v_tag_1934_ = stack[8].m_obj;
lean_object* v_opts_1935_ = stack[9].m_obj;
uint8_t v_clsEnabled_1936_ = stack[10].m_num;
lean_object* v_oldTraces_1937_ = stack[11].m_obj;
lean_object* v_msg_1938_ = stack[12].m_obj;
lean_object* v_resStartStop_1939_ = stack[13].m_obj;
lean_object* v_res_1941_;
v_res_1941_ = l_Lean_withTraceNode_x27___redArg___lam__6(v_inst_1926_, v_inst_1927_, v_inst_1928_, v_inst_1929_, v_inst_1930_, v___f_1931_, v_cls_1932_, v_collapsed_1933_, v_tag_1934_, v_opts_1935_, v_clsEnabled_1936_, v_oldTraces_1937_, v_msg_1938_, v_resStartStop_1939_);
stack->m_obj
 = v_res_1941_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__6___boxed(lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_inst_1945_, lean_object* v_inst_1946_, lean_object* v___f_1947_, lean_object* v_cls_1948_, lean_object* v_collapsed_1949_, lean_object* v_tag_1950_, lean_object* v_opts_1951_, lean_object* v_clsEnabled_1952_, lean_object* v_oldTraces_1953_, lean_object* v_msg_1954_, lean_object* v_resStartStop_1955_){
_start:
{
uint8_t v_collapsed_boxed_1956_; uint8_t v_clsEnabled_boxed_1957_; lean_object* v_res_1958_; 
v_collapsed_boxed_1956_ = lean_unbox(v_collapsed_1949_);
v_clsEnabled_boxed_1957_ = lean_unbox(v_clsEnabled_1952_);
v_res_1958_ = l_Lean_withTraceNode_x27___redArg___lam__6(v_inst_1942_, v_inst_1943_, v_inst_1944_, v_inst_1945_, v_inst_1946_, v___f_1947_, v_cls_1948_, v_collapsed_boxed_1956_, v_tag_1950_, v_opts_1951_, v_clsEnabled_boxed_1957_, v_oldTraces_1953_, v_msg_1954_, v_resStartStop_1955_);
lean_dec_ref(v_opts_1951_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__4(lean_object* v_start_1959_, lean_object* v_a_1960_, lean_object* v_toPure_1961_, lean_object* v_stop_1962_){
_start:
{
double v___x_1963_; double v___x_1964_; double v___x_1965_; double v___x_1966_; double v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1963_ = lean_float_of_nat(v_start_1959_);
v___x_1964_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0, &l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___lam__0___closed__0);
v___x_1965_ = lean_float_div(v___x_1963_, v___x_1964_);
v___x_1966_ = lean_float_of_nat(v_stop_1962_);
v___x_1967_ = lean_float_div(v___x_1966_, v___x_1964_);
v___x_1968_ = lean_box_float(v___x_1965_);
v___x_1969_ = lean_box_float(v___x_1967_);
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v_a_1960_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_apply_2(v_toPure_1961_, lean_box(0), v___x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__5(lean_object* v_start_1973_, lean_object* v_toPure_1974_, lean_object* v_toBind_1975_, lean_object* v___x_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___f_1978_; lean_object* v___x_1979_; 
v___f_1978_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__4), 4, 3);
lean_closure_set(v___f_1978_, 0, v_start_1973_);
lean_closure_set(v___f_1978_, 1, v_a_1977_);
lean_closure_set(v___f_1978_, 2, v_toPure_1974_);
v___x_1979_ = lean_apply_4(v_toBind_1975_, lean_box(0), lean_box(0), v___x_1976_, v___f_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__7(lean_object* v_toPure_1980_, lean_object* v_toBind_1981_, lean_object* v___x_1982_, lean_object* v___x_1983_, lean_object* v_start_1984_){
_start:
{
lean_object* v___f_1985_; lean_object* v___x_1986_; 
lean_inc(v_toBind_1981_);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1985_, 0, v_start_1984_);
lean_closure_set(v___f_1985_, 1, v_toPure_1980_);
lean_closure_set(v___f_1985_, 2, v_toBind_1981_);
lean_closure_set(v___f_1985_, 3, v___x_1982_);
v___x_1986_ = lean_apply_4(v_toBind_1981_, lean_box(0), lean_box(0), v___x_1983_, v___f_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__8(lean_object* v_start_1987_, lean_object* v_a_1988_, lean_object* v_toPure_1989_, lean_object* v_stop_1990_){
_start:
{
double v___x_1991_; double v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1991_ = lean_float_of_nat(v_start_1987_);
v___x_1992_ = lean_float_of_nat(v_stop_1990_);
v___x_1993_ = lean_box_float(v___x_1991_);
v___x_1994_ = lean_box_float(v___x_1992_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v_a_1988_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_apply_2(v_toPure_1989_, lean_box(0), v___x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__9(lean_object* v_start_1998_, lean_object* v_toPure_1999_, lean_object* v_toBind_2000_, lean_object* v___x_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___f_2003_; lean_object* v___x_2004_; 
v___f_2003_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__8), 4, 3);
lean_closure_set(v___f_2003_, 0, v_start_1998_);
lean_closure_set(v___f_2003_, 1, v_a_2002_);
lean_closure_set(v___f_2003_, 2, v_toPure_1999_);
v___x_2004_ = lean_apply_4(v_toBind_2000_, lean_box(0), lean_box(0), v___x_2001_, v___f_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__10(lean_object* v_toPure_2005_, lean_object* v_toBind_2006_, lean_object* v___x_2007_, lean_object* v___x_2008_, lean_object* v_start_2009_){
_start:
{
lean_object* v___f_2010_; lean_object* v___x_2011_; 
lean_inc(v_toBind_2006_);
v___f_2010_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__9), 5, 4);
lean_closure_set(v___f_2010_, 0, v_start_2009_);
lean_closure_set(v___f_2010_, 1, v_toPure_2005_);
lean_closure_set(v___f_2010_, 2, v_toBind_2006_);
lean_closure_set(v___f_2010_, 3, v___x_2007_);
v___x_2011_ = lean_apply_4(v_toBind_2006_, lean_box(0), lean_box(0), v___x_2008_, v___f_2010_);
return v___x_2011_;
}
}
lean_object* l_Lean_withTraceNode_x27___redArg___lam__11(lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v___f_2017_, lean_object* v_cls_2018_, uint8_t v_collapsed_2019_, lean_object* v_tag_2020_, lean_object* v_opts_2021_, uint8_t v_clsEnabled_2022_, lean_object* v_msg_2023_, lean_object* v_toBind_2024_, lean_object* v_k_2025_, lean_object* v___f_2026_, lean_object* v___f_2027_, lean_object* v___x_2028_, lean_object* v_inst_2029_, lean_object* v_toPure_2030_, lean_object* v_oldTraces_2031_){
_start:
{
lean_object* v_tryCatch_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___f_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v_tryCatch_2032_ = lean_ctor_get(v_inst_2012_, 1);
lean_inc(v_tryCatch_2032_);
v___x_2033_ = lean_box(v_collapsed_2019_);
v___x_2034_ = lean_box(v_clsEnabled_2022_);
lean_inc_ref(v_opts_2021_);
v___f_2035_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__6___boxed), 14, 13);
lean_closure_set(v___f_2035_, 0, v_inst_2013_);
lean_closure_set(v___f_2035_, 1, v_inst_2014_);
lean_closure_set(v___f_2035_, 2, v_inst_2015_);
lean_closure_set(v___f_2035_, 3, v_inst_2016_);
lean_closure_set(v___f_2035_, 4, v_inst_2012_);
lean_closure_set(v___f_2035_, 5, v___f_2017_);
lean_closure_set(v___f_2035_, 6, v_cls_2018_);
lean_closure_set(v___f_2035_, 7, v___x_2033_);
lean_closure_set(v___f_2035_, 8, v_tag_2020_);
lean_closure_set(v___f_2035_, 9, v_opts_2021_);
lean_closure_set(v___f_2035_, 10, v___x_2034_);
lean_closure_set(v___f_2035_, 11, v_oldTraces_2031_);
lean_closure_set(v___f_2035_, 12, v_msg_2023_);
lean_inc(v_toBind_2024_);
v___x_2036_ = lean_apply_4(v_toBind_2024_, lean_box(0), lean_box(0), v_k_2025_, v___f_2026_);
v___x_2037_ = lean_apply_3(v_tryCatch_2032_, lean_box(0), v___x_2036_, v___f_2027_);
v___x_2038_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2039_ = l_Lean_Option_get___redArg(v___x_2028_, v_opts_2021_, v___x_2038_);
lean_dec_ref(v_opts_2021_);
v___x_2040_ = lean_unbox(v___x_2039_);
lean_dec(v___x_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_2042_ = lean_apply_2(v_inst_2029_, lean_box(0), v___x_2041_);
lean_inc(v___x_2042_);
lean_inc_n(v_toBind_2024_, 2);
v___f_2043_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__7), 5, 4);
lean_closure_set(v___f_2043_, 0, v_toPure_2030_);
lean_closure_set(v___f_2043_, 1, v_toBind_2024_);
lean_closure_set(v___f_2043_, 2, v___x_2042_);
lean_closure_set(v___f_2043_, 3, v___x_2037_);
v___x_2044_ = lean_apply_4(v_toBind_2024_, lean_box(0), lean_box(0), v___x_2042_, v___f_2043_);
v___x_2045_ = lean_apply_4(v_toBind_2024_, lean_box(0), lean_box(0), v___x_2044_, v___f_2035_);
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___f_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2046_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_2047_ = lean_apply_2(v_inst_2029_, lean_box(0), v___x_2046_);
lean_inc(v___x_2047_);
lean_inc_n(v_toBind_2024_, 2);
v___f_2048_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__10), 5, 4);
lean_closure_set(v___f_2048_, 0, v_toPure_2030_);
lean_closure_set(v___f_2048_, 1, v_toBind_2024_);
lean_closure_set(v___f_2048_, 2, v___x_2047_);
lean_closure_set(v___f_2048_, 3, v___x_2037_);
v___x_2049_ = lean_apply_4(v_toBind_2024_, lean_box(0), lean_box(0), v___x_2047_, v___f_2048_);
v___x_2050_ = lean_apply_4(v_toBind_2024_, lean_box(0), lean_box(0), v___x_2049_, v___f_2035_);
return v___x_2050_;
}
}
}
LEAN_EXPORT void l_Lean_withTraceNode_x27___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2012_ = stack[0].m_obj;
lean_object* v_inst_2013_ = stack[1].m_obj;
lean_object* v_inst_2014_ = stack[2].m_obj;
lean_object* v_inst_2015_ = stack[3].m_obj;
lean_object* v_inst_2016_ = stack[4].m_obj;
lean_object* v___f_2017_ = stack[5].m_obj;
lean_object* v_cls_2018_ = stack[6].m_obj;
uint8_t v_collapsed_2019_ = stack[7].m_num;
lean_object* v_tag_2020_ = stack[8].m_obj;
lean_object* v_opts_2021_ = stack[9].m_obj;
uint8_t v_clsEnabled_2022_ = stack[10].m_num;
lean_object* v_msg_2023_ = stack[11].m_obj;
lean_object* v_toBind_2024_ = stack[12].m_obj;
lean_object* v_k_2025_ = stack[13].m_obj;
lean_object* v___f_2026_ = stack[14].m_obj;
lean_object* v___f_2027_ = stack[15].m_obj;
lean_object* v___x_2028_ = stack[16].m_obj;
lean_object* v_inst_2029_ = stack[17].m_obj;
lean_object* v_toPure_2030_ = stack[18].m_obj;
lean_object* v_oldTraces_2031_ = stack[19].m_obj;
lean_object* v_res_2051_;
v_res_2051_ = l_Lean_withTraceNode_x27___redArg___lam__11(v_inst_2012_, v_inst_2013_, v_inst_2014_, v_inst_2015_, v_inst_2016_, v___f_2017_, v_cls_2018_, v_collapsed_2019_, v_tag_2020_, v_opts_2021_, v_clsEnabled_2022_, v_msg_2023_, v_toBind_2024_, v_k_2025_, v___f_2026_, v___f_2027_, v___x_2028_, v_inst_2029_, v_toPure_2030_, v_oldTraces_2031_);
stack->m_obj
 = v_res_2051_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_inst_2052_ = _args[0];
lean_object* v_inst_2053_ = _args[1];
lean_object* v_inst_2054_ = _args[2];
lean_object* v_inst_2055_ = _args[3];
lean_object* v_inst_2056_ = _args[4];
lean_object* v___f_2057_ = _args[5];
lean_object* v_cls_2058_ = _args[6];
lean_object* v_collapsed_2059_ = _args[7];
lean_object* v_tag_2060_ = _args[8];
lean_object* v_opts_2061_ = _args[9];
lean_object* v_clsEnabled_2062_ = _args[10];
lean_object* v_msg_2063_ = _args[11];
lean_object* v_toBind_2064_ = _args[12];
lean_object* v_k_2065_ = _args[13];
lean_object* v___f_2066_ = _args[14];
lean_object* v___f_2067_ = _args[15];
lean_object* v___x_2068_ = _args[16];
lean_object* v_inst_2069_ = _args[17];
lean_object* v_toPure_2070_ = _args[18];
lean_object* v_oldTraces_2071_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_2072_; uint8_t v_clsEnabled_boxed_2073_; lean_object* v_res_2074_; 
v_collapsed_boxed_2072_ = lean_unbox(v_collapsed_2059_);
v_clsEnabled_boxed_2073_ = lean_unbox(v_clsEnabled_2062_);
v_res_2074_ = l_Lean_withTraceNode_x27___redArg___lam__11(v_inst_2052_, v_inst_2053_, v_inst_2054_, v_inst_2055_, v_inst_2056_, v___f_2057_, v_cls_2058_, v_collapsed_boxed_2072_, v_tag_2060_, v_opts_2061_, v_clsEnabled_boxed_2073_, v_msg_2063_, v_toBind_2064_, v_k_2065_, v___f_2066_, v___f_2067_, v___x_2068_, v_inst_2069_, v_toPure_2070_, v_oldTraces_2071_);
return v_res_2074_;
}
}
lean_object* l_Lean_withTraceNode_x27___redArg___lam__12(lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v___f_2080_, lean_object* v_cls_2081_, uint8_t v_collapsed_2082_, lean_object* v_tag_2083_, lean_object* v_opts_2084_, lean_object* v_msg_2085_, lean_object* v_toBind_2086_, lean_object* v_k_2087_, lean_object* v___f_2088_, lean_object* v___f_2089_, lean_object* v___x_2090_, lean_object* v_inst_2091_, lean_object* v_toPure_2092_, uint8_t v_clsEnabled_2093_){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___f_2096_; 
v___x_2094_ = lean_box(v_collapsed_2082_);
v___x_2095_ = lean_box(v_clsEnabled_2093_);
lean_inc_ref(v___x_2090_);
lean_inc(v_k_2087_);
lean_inc(v_toBind_2086_);
lean_inc_ref(v_opts_2084_);
lean_inc_ref(v_inst_2077_);
lean_inc_ref(v_inst_2076_);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__11___boxed), 20, 19);
lean_closure_set(v___f_2096_, 0, v_inst_2075_);
lean_closure_set(v___f_2096_, 1, v_inst_2076_);
lean_closure_set(v___f_2096_, 2, v_inst_2077_);
lean_closure_set(v___f_2096_, 3, v_inst_2078_);
lean_closure_set(v___f_2096_, 4, v_inst_2079_);
lean_closure_set(v___f_2096_, 5, v___f_2080_);
lean_closure_set(v___f_2096_, 6, v_cls_2081_);
lean_closure_set(v___f_2096_, 7, v___x_2094_);
lean_closure_set(v___f_2096_, 8, v_tag_2083_);
lean_closure_set(v___f_2096_, 9, v_opts_2084_);
lean_closure_set(v___f_2096_, 10, v___x_2095_);
lean_closure_set(v___f_2096_, 11, v_msg_2085_);
lean_closure_set(v___f_2096_, 12, v_toBind_2086_);
lean_closure_set(v___f_2096_, 13, v_k_2087_);
lean_closure_set(v___f_2096_, 14, v___f_2088_);
lean_closure_set(v___f_2096_, 15, v___f_2089_);
lean_closure_set(v___f_2096_, 16, v___x_2090_);
lean_closure_set(v___f_2096_, 17, v_inst_2091_);
lean_closure_set(v___f_2096_, 18, v_toPure_2092_);
if (v_clsEnabled_2093_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2100_ = l_Lean_trace_profiler;
v___x_2101_ = l_Lean_Option_get___redArg(v___x_2090_, v_opts_2084_, v___x_2100_);
lean_dec_ref(v_opts_2084_);
v___x_2102_ = lean_unbox(v___x_2101_);
lean_dec(v___x_2101_);
if (v___x_2102_ == 0)
{
lean_dec_ref(v___f_2096_);
lean_dec(v_toBind_2086_);
lean_dec_ref(v_inst_2077_);
lean_dec_ref(v_inst_2076_);
return v_k_2087_;
}
else
{
lean_dec(v_k_2087_);
goto v___jp_2097_;
}
}
else
{
lean_dec_ref(v___x_2090_);
lean_dec(v_k_2087_);
lean_dec_ref(v_opts_2084_);
goto v___jp_2097_;
}
v___jp_2097_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_2076_, v_inst_2077_);
v___x_2099_ = lean_apply_4(v_toBind_2086_, lean_box(0), lean_box(0), v___x_2098_, v___f_2096_);
return v___x_2099_;
}
}
}
LEAN_EXPORT void l_Lean_withTraceNode_x27___redArg___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2075_ = stack[0].m_obj;
lean_object* v_inst_2076_ = stack[1].m_obj;
lean_object* v_inst_2077_ = stack[2].m_obj;
lean_object* v_inst_2078_ = stack[3].m_obj;
lean_object* v_inst_2079_ = stack[4].m_obj;
lean_object* v___f_2080_ = stack[5].m_obj;
lean_object* v_cls_2081_ = stack[6].m_obj;
uint8_t v_collapsed_2082_ = stack[7].m_num;
lean_object* v_tag_2083_ = stack[8].m_obj;
lean_object* v_opts_2084_ = stack[9].m_obj;
lean_object* v_msg_2085_ = stack[10].m_obj;
lean_object* v_toBind_2086_ = stack[11].m_obj;
lean_object* v_k_2087_ = stack[12].m_obj;
lean_object* v___f_2088_ = stack[13].m_obj;
lean_object* v___f_2089_ = stack[14].m_obj;
lean_object* v___x_2090_ = stack[15].m_obj;
lean_object* v_inst_2091_ = stack[16].m_obj;
lean_object* v_toPure_2092_ = stack[17].m_obj;
uint8_t v_clsEnabled_2093_ = stack[18].m_num;
lean_object* v_res_2103_;
v_res_2103_ = l_Lean_withTraceNode_x27___redArg___lam__12(v_inst_2075_, v_inst_2076_, v_inst_2077_, v_inst_2078_, v_inst_2079_, v___f_2080_, v_cls_2081_, v_collapsed_2082_, v_tag_2083_, v_opts_2084_, v_msg_2085_, v_toBind_2086_, v_k_2087_, v___f_2088_, v___f_2089_, v___x_2090_, v_inst_2091_, v_toPure_2092_, v_clsEnabled_2093_);
stack->m_obj
 = v_res_2103_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_inst_2104_ = _args[0];
lean_object* v_inst_2105_ = _args[1];
lean_object* v_inst_2106_ = _args[2];
lean_object* v_inst_2107_ = _args[3];
lean_object* v_inst_2108_ = _args[4];
lean_object* v___f_2109_ = _args[5];
lean_object* v_cls_2110_ = _args[6];
lean_object* v_collapsed_2111_ = _args[7];
lean_object* v_tag_2112_ = _args[8];
lean_object* v_opts_2113_ = _args[9];
lean_object* v_msg_2114_ = _args[10];
lean_object* v_toBind_2115_ = _args[11];
lean_object* v_k_2116_ = _args[12];
lean_object* v___f_2117_ = _args[13];
lean_object* v___f_2118_ = _args[14];
lean_object* v___x_2119_ = _args[15];
lean_object* v_inst_2120_ = _args[16];
lean_object* v_toPure_2121_ = _args[17];
lean_object* v_clsEnabled_2122_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_2123_; uint8_t v_clsEnabled_boxed_2124_; lean_object* v_res_2125_; 
v_collapsed_boxed_2123_ = lean_unbox(v_collapsed_2111_);
v_clsEnabled_boxed_2124_ = lean_unbox(v_clsEnabled_2122_);
v_res_2125_ = l_Lean_withTraceNode_x27___redArg___lam__12(v_inst_2104_, v_inst_2105_, v_inst_2106_, v_inst_2107_, v_inst_2108_, v___f_2109_, v_cls_2110_, v_collapsed_boxed_2123_, v_tag_2112_, v_opts_2113_, v_msg_2114_, v_toBind_2115_, v_k_2116_, v___f_2117_, v___f_2118_, v___x_2119_, v_inst_2120_, v_toPure_2121_, v_clsEnabled_boxed_2124_);
return v_res_2125_;
}
}
lean_object* l_Lean_withTraceNode_x27___redArg___lam__13(lean_object* v_k_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v___f_2132_, lean_object* v_cls_2133_, uint8_t v_collapsed_2134_, lean_object* v_tag_2135_, lean_object* v_msg_2136_, lean_object* v_toBind_2137_, lean_object* v___f_2138_, lean_object* v___f_2139_, lean_object* v___x_2140_, lean_object* v_inst_2141_, lean_object* v_toPure_2142_, lean_object* v___f_2143_, lean_object* v_opts_2144_){
_start:
{
uint8_t v_hasTrace_2145_; 
v_hasTrace_2145_ = lean_ctor_get_uint8(v_opts_2144_, sizeof(void*)*1);
if (v_hasTrace_2145_ == 0)
{
lean_dec_ref(v_opts_2144_);
lean_dec(v___f_2143_);
lean_dec(v_toPure_2142_);
lean_dec(v_inst_2141_);
lean_dec_ref(v___x_2140_);
lean_dec(v___f_2139_);
lean_dec(v___f_2138_);
lean_dec(v_toBind_2137_);
lean_dec(v_msg_2136_);
lean_dec_ref(v_tag_2135_);
lean_dec(v_cls_2133_);
lean_dec_ref(v___f_2132_);
lean_dec(v_inst_2131_);
lean_dec_ref(v_inst_2130_);
lean_dec_ref(v_inst_2129_);
lean_dec_ref(v_inst_2128_);
lean_dec_ref(v_inst_2127_);
return v_k_2126_;
}
else
{
lean_object* v_getInheritedTraceOptions_2146_; lean_object* v___x_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_getInheritedTraceOptions_2146_ = lean_ctor_get(v_inst_2127_, 2);
lean_inc(v_getInheritedTraceOptions_2146_);
v___x_2147_ = lean_box(v_collapsed_2134_);
lean_inc_n(v_toBind_2137_, 2);
v___f_2148_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__12___boxed), 19, 18);
lean_closure_set(v___f_2148_, 0, v_inst_2128_);
lean_closure_set(v___f_2148_, 1, v_inst_2129_);
lean_closure_set(v___f_2148_, 2, v_inst_2127_);
lean_closure_set(v___f_2148_, 3, v_inst_2130_);
lean_closure_set(v___f_2148_, 4, v_inst_2131_);
lean_closure_set(v___f_2148_, 5, v___f_2132_);
lean_closure_set(v___f_2148_, 6, v_cls_2133_);
lean_closure_set(v___f_2148_, 7, v___x_2147_);
lean_closure_set(v___f_2148_, 8, v_tag_2135_);
lean_closure_set(v___f_2148_, 9, v_opts_2144_);
lean_closure_set(v___f_2148_, 10, v_msg_2136_);
lean_closure_set(v___f_2148_, 11, v_toBind_2137_);
lean_closure_set(v___f_2148_, 12, v_k_2126_);
lean_closure_set(v___f_2148_, 13, v___f_2138_);
lean_closure_set(v___f_2148_, 14, v___f_2139_);
lean_closure_set(v___f_2148_, 15, v___x_2140_);
lean_closure_set(v___f_2148_, 16, v_inst_2141_);
lean_closure_set(v___f_2148_, 17, v_toPure_2142_);
v___x_2149_ = lean_apply_4(v_toBind_2137_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2146_, v___f_2143_);
v___x_2150_ = lean_apply_4(v_toBind_2137_, lean_box(0), lean_box(0), v___x_2149_, v___f_2148_);
return v___x_2150_;
}
}
}
LEAN_EXPORT void l_Lean_withTraceNode_x27___redArg___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2126_ = stack[0].m_obj;
lean_object* v_inst_2127_ = stack[1].m_obj;
lean_object* v_inst_2128_ = stack[2].m_obj;
lean_object* v_inst_2129_ = stack[3].m_obj;
lean_object* v_inst_2130_ = stack[4].m_obj;
lean_object* v_inst_2131_ = stack[5].m_obj;
lean_object* v___f_2132_ = stack[6].m_obj;
lean_object* v_cls_2133_ = stack[7].m_obj;
uint8_t v_collapsed_2134_ = stack[8].m_num;
lean_object* v_tag_2135_ = stack[9].m_obj;
lean_object* v_msg_2136_ = stack[10].m_obj;
lean_object* v_toBind_2137_ = stack[11].m_obj;
lean_object* v___f_2138_ = stack[12].m_obj;
lean_object* v___f_2139_ = stack[13].m_obj;
lean_object* v___x_2140_ = stack[14].m_obj;
lean_object* v_inst_2141_ = stack[15].m_obj;
lean_object* v_toPure_2142_ = stack[16].m_obj;
lean_object* v___f_2143_ = stack[17].m_obj;
lean_object* v_opts_2144_ = stack[18].m_obj;
lean_object* v_res_2151_;
v_res_2151_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_k_2126_, v_inst_2127_, v_inst_2128_, v_inst_2129_, v_inst_2130_, v_inst_2131_, v___f_2132_, v_cls_2133_, v_collapsed_2134_, v_tag_2135_, v_msg_2136_, v_toBind_2137_, v___f_2138_, v___f_2139_, v___x_2140_, v_inst_2141_, v_toPure_2142_, v___f_2143_, v_opts_2144_);
stack->m_obj
 = v_res_2151_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___lam__13___boxed(lean_object** _args){
lean_object* v_k_2152_ = _args[0];
lean_object* v_inst_2153_ = _args[1];
lean_object* v_inst_2154_ = _args[2];
lean_object* v_inst_2155_ = _args[3];
lean_object* v_inst_2156_ = _args[4];
lean_object* v_inst_2157_ = _args[5];
lean_object* v___f_2158_ = _args[6];
lean_object* v_cls_2159_ = _args[7];
lean_object* v_collapsed_2160_ = _args[8];
lean_object* v_tag_2161_ = _args[9];
lean_object* v_msg_2162_ = _args[10];
lean_object* v_toBind_2163_ = _args[11];
lean_object* v___f_2164_ = _args[12];
lean_object* v___f_2165_ = _args[13];
lean_object* v___x_2166_ = _args[14];
lean_object* v_inst_2167_ = _args[15];
lean_object* v_toPure_2168_ = _args[16];
lean_object* v___f_2169_ = _args[17];
lean_object* v_opts_2170_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_2171_; lean_object* v_res_2172_; 
v_collapsed_boxed_2171_ = lean_unbox(v_collapsed_2160_);
v_res_2172_ = l_Lean_withTraceNode_x27___redArg___lam__13(v_k_2152_, v_inst_2153_, v_inst_2154_, v_inst_2155_, v_inst_2156_, v_inst_2157_, v___f_2158_, v_cls_2159_, v_collapsed_boxed_2171_, v_tag_2161_, v_msg_2162_, v_toBind_2163_, v___f_2164_, v___f_2165_, v___x_2166_, v_inst_2167_, v_toPure_2168_, v___f_2169_, v_opts_2170_);
return v_res_2172_;
}
}
lean_object* l_Lean_withTraceNode_x27___redArg(lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_inst_2179_, lean_object* v_inst_2180_, lean_object* v_cls_2181_, lean_object* v_k_2182_, uint8_t v_collapsed_2183_, lean_object* v_tag_2184_){
_start:
{
lean_object* v_toApplicative_2185_; lean_object* v_toFunctor_2186_; lean_object* v_toBind_2187_; lean_object* v_toPure_2188_; lean_object* v_map_2189_; lean_object* v___x_2190_; lean_object* v_getOptionsUnrestricted_2191_; lean_object* v___f_2192_; lean_object* v___f_2193_; lean_object* v___f_2194_; lean_object* v_msg_2195_; lean_object* v___f_2196_; lean_object* v___f_2197_; lean_object* v___x_2198_; lean_object* v___f_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_toApplicative_2185_ = lean_ctor_get(v_inst_2174_, 0);
v_toFunctor_2186_ = lean_ctor_get(v_toApplicative_2185_, 0);
v_toBind_2187_ = lean_ctor_get(v_inst_2174_, 1);
lean_inc_n(v_toBind_2187_, 3);
v_toPure_2188_ = lean_ctor_get(v_toApplicative_2185_, 1);
lean_inc_n(v_toPure_2188_, 5);
v_map_2189_ = lean_ctor_get(v_toFunctor_2186_, 0);
lean_inc(v_map_2189_);
v___x_2190_ = l_Lean_KVMap_instValueBool;
v_getOptionsUnrestricted_2191_ = lean_ctor_get(v_inst_2178_, 1);
lean_inc_n(v_getOptionsUnrestricted_2191_, 2);
lean_dec_ref(v_inst_2178_);
v___f_2192_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v___f_2193_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2193_, 0, v_toPure_2188_);
v___f_2194_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2194_, 0, v_toPure_2188_);
v_msg_2195_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3), 2, 1);
lean_closure_set(v_msg_2195_, 0, v_toPure_2188_);
v___f_2196_ = ((lean_object*)(l_Lean_instExceptToTraceResult___redArg___closed__0));
lean_inc(v_cls_2181_);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__12), 5, 4);
lean_closure_set(v___f_2197_, 0, v_toPure_2188_);
lean_closure_set(v___f_2197_, 1, v_cls_2181_);
lean_closure_set(v___f_2197_, 2, v_toBind_2187_);
lean_closure_set(v___f_2197_, 3, v_getOptionsUnrestricted_2191_);
v___x_2198_ = lean_box(v_collapsed_2183_);
v___f_2199_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 19, 18);
lean_closure_set(v___f_2199_, 0, v_k_2182_);
lean_closure_set(v___f_2199_, 1, v_inst_2175_);
lean_closure_set(v___f_2199_, 2, v_inst_2179_);
lean_closure_set(v___f_2199_, 3, v_inst_2174_);
lean_closure_set(v___f_2199_, 4, v_inst_2176_);
lean_closure_set(v___f_2199_, 5, v_inst_2177_);
lean_closure_set(v___f_2199_, 6, v___f_2196_);
lean_closure_set(v___f_2199_, 7, v_cls_2181_);
lean_closure_set(v___f_2199_, 8, v___x_2198_);
lean_closure_set(v___f_2199_, 9, v_tag_2184_);
lean_closure_set(v___f_2199_, 10, v_msg_2195_);
lean_closure_set(v___f_2199_, 11, v_toBind_2187_);
lean_closure_set(v___f_2199_, 12, v___f_2193_);
lean_closure_set(v___f_2199_, 13, v___f_2194_);
lean_closure_set(v___f_2199_, 14, v___x_2190_);
lean_closure_set(v___f_2199_, 15, v_inst_2180_);
lean_closure_set(v___f_2199_, 16, v_toPure_2188_);
lean_closure_set(v___f_2199_, 17, v___f_2197_);
v___x_2200_ = lean_apply_4(v_toBind_2187_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_2191_, v___f_2199_);
v___x_2201_ = lean_apply_4(v_map_2189_, lean_box(0), lean_box(0), v___f_2192_, v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT void l_Lean_withTraceNode_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2174_ = stack[0].m_obj;
lean_object* v_inst_2175_ = stack[1].m_obj;
lean_object* v_inst_2176_ = stack[2].m_obj;
lean_object* v_inst_2177_ = stack[3].m_obj;
lean_object* v_inst_2178_ = stack[4].m_obj;
lean_object* v_inst_2179_ = stack[5].m_obj;
lean_object* v_inst_2180_ = stack[6].m_obj;
lean_object* v_cls_2181_ = stack[7].m_obj;
lean_object* v_k_2182_ = stack[8].m_obj;
uint8_t v_collapsed_2183_ = stack[9].m_num;
lean_object* v_tag_2184_ = stack[10].m_obj;
lean_object* v_res_2202_;
v_res_2202_ = l_Lean_withTraceNode_x27___redArg(v_inst_2174_, v_inst_2175_, v_inst_2176_, v_inst_2177_, v_inst_2178_, v_inst_2179_, v_inst_2180_, v_cls_2181_, v_k_2182_, v_collapsed_2183_, v_tag_2184_);
stack->m_obj
 = v_res_2202_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___redArg___boxed(lean_object* v_inst_2203_, lean_object* v_inst_2204_, lean_object* v_inst_2205_, lean_object* v_inst_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v_cls_2210_, lean_object* v_k_2211_, lean_object* v_collapsed_2212_, lean_object* v_tag_2213_){
_start:
{
uint8_t v_collapsed_boxed_2214_; lean_object* v_res_2215_; 
v_collapsed_boxed_2214_ = lean_unbox(v_collapsed_2212_);
v_res_2215_ = l_Lean_withTraceNode_x27___redArg(v_inst_2203_, v_inst_2204_, v_inst_2205_, v_inst_2206_, v_inst_2207_, v_inst_2208_, v_inst_2209_, v_cls_2210_, v_k_2211_, v_collapsed_boxed_2214_, v_tag_2213_);
return v_res_2215_;
}
}
lean_object* l_Lean_withTraceNode_x27(lean_object* v_00_u03b1_2216_, lean_object* v_m_2217_, lean_object* v_inst_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_inst_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_cls_2225_, lean_object* v_k_2226_, uint8_t v_collapsed_2227_, lean_object* v_tag_2228_){
_start:
{
lean_object* v_toApplicative_2229_; lean_object* v_toFunctor_2230_; lean_object* v_toBind_2231_; lean_object* v_toPure_2232_; lean_object* v_map_2233_; lean_object* v___x_2234_; lean_object* v_getOptionsUnrestricted_2235_; lean_object* v___f_2236_; lean_object* v___f_2237_; lean_object* v___f_2238_; lean_object* v_msg_2239_; lean_object* v___f_2240_; lean_object* v___f_2241_; lean_object* v___x_2242_; lean_object* v___f_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v_toApplicative_2229_ = lean_ctor_get(v_inst_2218_, 0);
v_toFunctor_2230_ = lean_ctor_get(v_toApplicative_2229_, 0);
v_toBind_2231_ = lean_ctor_get(v_inst_2218_, 1);
lean_inc_n(v_toBind_2231_, 3);
v_toPure_2232_ = lean_ctor_get(v_toApplicative_2229_, 1);
lean_inc_n(v_toPure_2232_, 5);
v_map_2233_ = lean_ctor_get(v_toFunctor_2230_, 0);
lean_inc(v_map_2233_);
v___x_2234_ = l_Lean_KVMap_instValueBool;
v_getOptionsUnrestricted_2235_ = lean_ctor_get(v_inst_2222_, 1);
lean_inc_n(v_getOptionsUnrestricted_2235_, 2);
lean_dec_ref(v_inst_2222_);
v___f_2236_ = ((lean_object*)(l_Lean_withTraceNode_x27___redArg___closed__0));
v___f_2237_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2237_, 0, v_toPure_2232_);
v___f_2238_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2238_, 0, v_toPure_2232_);
v_msg_2239_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__3), 2, 1);
lean_closure_set(v_msg_2239_, 0, v_toPure_2232_);
v___f_2240_ = ((lean_object*)(l_Lean_instExceptToTraceResult___redArg___closed__0));
lean_inc(v_cls_2225_);
v___f_2241_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__12), 5, 4);
lean_closure_set(v___f_2241_, 0, v_toPure_2232_);
lean_closure_set(v___f_2241_, 1, v_cls_2225_);
lean_closure_set(v___f_2241_, 2, v_toBind_2231_);
lean_closure_set(v___f_2241_, 3, v_getOptionsUnrestricted_2235_);
v___x_2242_ = lean_box(v_collapsed_2227_);
v___f_2243_ = lean_alloc_closure((void*)(l_Lean_withTraceNode_x27___redArg___lam__13___boxed), 19, 18);
lean_closure_set(v___f_2243_, 0, v_k_2226_);
lean_closure_set(v___f_2243_, 1, v_inst_2219_);
lean_closure_set(v___f_2243_, 2, v_inst_2223_);
lean_closure_set(v___f_2243_, 3, v_inst_2218_);
lean_closure_set(v___f_2243_, 4, v_inst_2220_);
lean_closure_set(v___f_2243_, 5, v_inst_2221_);
lean_closure_set(v___f_2243_, 6, v___f_2240_);
lean_closure_set(v___f_2243_, 7, v_cls_2225_);
lean_closure_set(v___f_2243_, 8, v___x_2242_);
lean_closure_set(v___f_2243_, 9, v_tag_2228_);
lean_closure_set(v___f_2243_, 10, v_msg_2239_);
lean_closure_set(v___f_2243_, 11, v_toBind_2231_);
lean_closure_set(v___f_2243_, 12, v___f_2237_);
lean_closure_set(v___f_2243_, 13, v___f_2238_);
lean_closure_set(v___f_2243_, 14, v___x_2234_);
lean_closure_set(v___f_2243_, 15, v_inst_2224_);
lean_closure_set(v___f_2243_, 16, v_toPure_2232_);
lean_closure_set(v___f_2243_, 17, v___f_2241_);
v___x_2244_ = lean_apply_4(v_toBind_2231_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_2235_, v___f_2243_);
v___x_2245_ = lean_apply_4(v_map_2233_, lean_box(0), lean_box(0), v___f_2236_, v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT void l_Lean_withTraceNode_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2218_ = stack[2].m_obj;
lean_object* v_inst_2219_ = stack[3].m_obj;
lean_object* v_inst_2220_ = stack[4].m_obj;
lean_object* v_inst_2221_ = stack[5].m_obj;
lean_object* v_inst_2222_ = stack[6].m_obj;
lean_object* v_inst_2223_ = stack[7].m_obj;
lean_object* v_inst_2224_ = stack[8].m_obj;
lean_object* v_cls_2225_ = stack[9].m_obj;
lean_object* v_k_2226_ = stack[10].m_obj;
uint8_t v_collapsed_2227_ = stack[11].m_num;
lean_object* v_tag_2228_ = stack[12].m_obj;
lean_object* v_res_2246_;
v_res_2246_ = l_Lean_withTraceNode_x27(lean_box(0), lean_box(0), v_inst_2218_, v_inst_2219_, v_inst_2220_, v_inst_2221_, v_inst_2222_, v_inst_2223_, v_inst_2224_, v_cls_2225_, v_k_2226_, v_collapsed_2227_, v_tag_2228_);
stack->m_obj
 = v_res_2246_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode_x27___boxed(lean_object* v_00_u03b1_2247_, lean_object* v_m_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_inst_2252_, lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_cls_2256_, lean_object* v_k_2257_, lean_object* v_collapsed_2258_, lean_object* v_tag_2259_){
_start:
{
uint8_t v_collapsed_boxed_2260_; lean_object* v_res_2261_; 
v_collapsed_boxed_2260_ = lean_unbox(v_collapsed_2258_);
v_res_2261_ = l_Lean_withTraceNode_x27(v_00_u03b1_2247_, v_m_2248_, v_inst_2249_, v_inst_2250_, v_inst_2251_, v_inst_2252_, v_inst_2253_, v_inst_2254_, v_inst_2255_, v_cls_2256_, v_k_2257_, v_collapsed_boxed_2260_, v_tag_2259_);
return v_res_2261_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__4(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__3));
v___x_2271_ = l_Lean_mkAtom(v___x_2270_);
return v___x_2271_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__5(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__4, &l_Lean_registerTraceClass___auto__1___closed__4_once, _init_l_Lean_registerTraceClass___auto__1___closed__4);
v___x_2273_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2274_ = lean_array_push(v___x_2273_, v___x_2272_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__6(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2275_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__5, &l_Lean_registerTraceClass___auto__1___closed__5_once, _init_l_Lean_registerTraceClass___auto__1___closed__5);
v___x_2276_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__2));
v___x_2277_ = lean_box(2);
v___x_2278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___x_2276_);
lean_ctor_set(v___x_2278_, 2, v___x_2275_);
return v___x_2278_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__7(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__6, &l_Lean_registerTraceClass___auto__1___closed__6_once, _init_l_Lean_registerTraceClass___auto__1___closed__6);
v___x_2280_ = lean_obj_once(&l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13, &l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13_once, _init_l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__13);
v___x_2281_ = lean_array_push(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2282_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__7, &l_Lean_registerTraceClass___auto__1___closed__7_once, _init_l_Lean_registerTraceClass___auto__1___closed__7);
v___x_2283_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__11));
v___x_2284_ = lean_box(2);
v___x_2285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
lean_ctor_set(v___x_2285_, 1, v___x_2283_);
lean_ctor_set(v___x_2285_, 2, v___x_2282_);
return v___x_2285_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__8, &l_Lean_registerTraceClass___auto__1___closed__8_once, _init_l_Lean_registerTraceClass___auto__1___closed__8);
v___x_2287_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2288_ = lean_array_push(v___x_2287_, v___x_2286_);
return v___x_2288_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2289_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__9, &l_Lean_registerTraceClass___auto__1___closed__9_once, _init_l_Lean_registerTraceClass___auto__1___closed__9);
v___x_2290_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2291_ = lean_box(2);
v___x_2292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v___x_2290_);
lean_ctor_set(v___x_2292_, 2, v___x_2289_);
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__11(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__10, &l_Lean_registerTraceClass___auto__1___closed__10_once, _init_l_Lean_registerTraceClass___auto__1___closed__10);
v___x_2294_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2295_ = lean_array_push(v___x_2294_, v___x_2293_);
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2296_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__11, &l_Lean_registerTraceClass___auto__1___closed__11_once, _init_l_Lean_registerTraceClass___auto__1___closed__11);
v___x_2297_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__7));
v___x_2298_ = lean_box(2);
v___x_2299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v___x_2297_);
lean_ctor_set(v___x_2299_, 2, v___x_2296_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__12, &l_Lean_registerTraceClass___auto__1___closed__12_once, _init_l_Lean_registerTraceClass___auto__1___closed__12);
v___x_2301_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__5));
v___x_2302_ = lean_array_push(v___x_2301_, v___x_2300_);
return v___x_2302_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2303_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__13, &l_Lean_registerTraceClass___auto__1___closed__13_once, _init_l_Lean_registerTraceClass___auto__1___closed__13);
v___x_2304_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__4));
v___x_2305_ = lean_box(2);
v___x_2306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v___x_2304_);
lean_ctor_set(v___x_2306_, 2, v___x_2303_);
return v___x_2306_;
}
}
static lean_object* _init_l_Lean_registerTraceClass___auto__1(void){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_obj_once(&l_Lean_registerTraceClass___auto__1___closed__14, &l_Lean_registerTraceClass___auto__1___closed__14_once, _init_l_Lean_registerTraceClass___auto__1___closed__14);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2308_, lean_object* v_x_2309_){
_start:
{
if (lean_obj_tag(v_x_2309_) == 0)
{
return v_x_2308_;
}
else
{
lean_object* v_key_2310_; lean_object* v_value_2311_; lean_object* v_tail_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2338_; 
v_key_2310_ = lean_ctor_get(v_x_2309_, 0);
v_value_2311_ = lean_ctor_get(v_x_2309_, 1);
v_tail_2312_ = lean_ctor_get(v_x_2309_, 2);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_x_2309_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2314_ = v_x_2309_;
v_isShared_2315_ = v_isSharedCheck_2338_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_tail_2312_);
lean_inc(v_value_2311_);
lean_inc(v_key_2310_);
lean_dec(v_x_2309_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2338_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; uint64_t v___y_2318_; 
v___x_2316_ = lean_array_get_size(v_x_2308_);
if (lean_obj_tag(v_key_2310_) == 0)
{
uint64_t v___x_2336_; 
v___x_2336_ = 1723ULL;
v___y_2318_ = v___x_2336_;
goto v___jp_2317_;
}
else
{
uint64_t v_hash_2337_; 
v_hash_2337_ = lean_ctor_get_uint64(v_key_2310_, sizeof(void*)*2);
v___y_2318_ = v_hash_2337_;
goto v___jp_2317_;
}
v___jp_2317_:
{
uint64_t v___x_2319_; uint64_t v___x_2320_; uint64_t v_fold_2321_; uint64_t v___x_2322_; uint64_t v___x_2323_; uint64_t v___x_2324_; size_t v___x_2325_; size_t v___x_2326_; size_t v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2319_ = 32ULL;
v___x_2320_ = lean_uint64_shift_right(v___y_2318_, v___x_2319_);
v_fold_2321_ = lean_uint64_xor(v___y_2318_, v___x_2320_);
v___x_2322_ = 16ULL;
v___x_2323_ = lean_uint64_shift_right(v_fold_2321_, v___x_2322_);
v___x_2324_ = lean_uint64_xor(v_fold_2321_, v___x_2323_);
v___x_2325_ = lean_uint64_to_usize(v___x_2324_);
v___x_2326_ = lean_usize_of_nat(v___x_2316_);
v___x_2327_ = ((size_t)1ULL);
v___x_2328_ = lean_usize_sub(v___x_2326_, v___x_2327_);
v___x_2329_ = lean_usize_land(v___x_2325_, v___x_2328_);
v___x_2330_ = lean_array_uget_borrowed(v_x_2308_, v___x_2329_);
lean_inc(v___x_2330_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 2, v___x_2330_);
v___x_2332_ = v___x_2314_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_key_2310_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_value_2311_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_array_uset(v_x_2308_, v___x_2329_, v___x_2332_);
v_x_2308_ = v___x_2333_;
v_x_2309_ = v_tail_2312_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(lean_object* v_i_2339_, lean_object* v_source_2340_, lean_object* v_target_2341_){
_start:
{
lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = lean_array_get_size(v_source_2340_);
v___x_2343_ = lean_nat_dec_lt(v_i_2339_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_dec_ref(v_source_2340_);
lean_dec(v_i_2339_);
return v_target_2341_;
}
else
{
lean_object* v_es_2344_; lean_object* v___x_2345_; lean_object* v_source_2346_; lean_object* v_target_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v_es_2344_ = lean_array_fget(v_source_2340_, v_i_2339_);
v___x_2345_ = lean_box(0);
v_source_2346_ = lean_array_fset(v_source_2340_, v_i_2339_, v___x_2345_);
v_target_2347_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_target_2341_, v_es_2344_);
v___x_2348_ = lean_unsigned_to_nat(1u);
v___x_2349_ = lean_nat_add(v_i_2339_, v___x_2348_);
lean_dec(v_i_2339_);
v_i_2339_ = v___x_2349_;
v_source_2340_ = v_source_2346_;
v_target_2341_ = v_target_2347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(lean_object* v_data_2351_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v_nbuckets_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2352_ = lean_array_get_size(v_data_2351_);
v___x_2353_ = lean_unsigned_to_nat(2u);
v_nbuckets_2354_ = lean_nat_mul(v___x_2352_, v___x_2353_);
v___x_2355_ = lean_unsigned_to_nat(0u);
v___x_2356_ = lean_box(0);
v___x_2357_ = lean_mk_array(v_nbuckets_2354_, v___x_2356_);
v___x_2358_ = lean_array_propagate_mark(v_data_2351_, v___x_2357_);
v___x_2359_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v___x_2355_, v_data_2351_, v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(lean_object* v_m_2360_, lean_object* v_a_2361_, lean_object* v_b_2362_){
_start:
{
lean_object* v_size_2363_; lean_object* v_buckets_2364_; lean_object* v___x_2365_; uint64_t v___y_2367_; 
v_size_2363_ = lean_ctor_get(v_m_2360_, 0);
v_buckets_2364_ = lean_ctor_get(v_m_2360_, 1);
v___x_2365_ = lean_array_get_size(v_buckets_2364_);
if (lean_obj_tag(v_a_2361_) == 0)
{
uint64_t v___x_2404_; 
v___x_2404_ = 1723ULL;
v___y_2367_ = v___x_2404_;
goto v___jp_2366_;
}
else
{
uint64_t v_hash_2405_; 
v_hash_2405_ = lean_ctor_get_uint64(v_a_2361_, sizeof(void*)*2);
v___y_2367_ = v_hash_2405_;
goto v___jp_2366_;
}
v___jp_2366_:
{
uint64_t v___x_2368_; uint64_t v___x_2369_; uint64_t v_fold_2370_; uint64_t v___x_2371_; uint64_t v___x_2372_; uint64_t v___x_2373_; size_t v___x_2374_; size_t v___x_2375_; size_t v___x_2376_; size_t v___x_2377_; size_t v___x_2378_; lean_object* v_bkt_2379_; uint8_t v___x_2380_; 
v___x_2368_ = 32ULL;
v___x_2369_ = lean_uint64_shift_right(v___y_2367_, v___x_2368_);
v_fold_2370_ = lean_uint64_xor(v___y_2367_, v___x_2369_);
v___x_2371_ = 16ULL;
v___x_2372_ = lean_uint64_shift_right(v_fold_2370_, v___x_2371_);
v___x_2373_ = lean_uint64_xor(v_fold_2370_, v___x_2372_);
v___x_2374_ = lean_uint64_to_usize(v___x_2373_);
v___x_2375_ = lean_usize_of_nat(v___x_2365_);
v___x_2376_ = ((size_t)1ULL);
v___x_2377_ = lean_usize_sub(v___x_2375_, v___x_2376_);
v___x_2378_ = lean_usize_land(v___x_2374_, v___x_2377_);
v_bkt_2379_ = lean_array_uget_borrowed(v_buckets_2364_, v___x_2378_);
v___x_2380_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_Trace_0__Lean_checkTraceOption_go_spec__0_spec__0___redArg(v_a_2361_, v_bkt_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2401_; 
lean_inc_ref(v_buckets_2364_);
lean_inc(v_size_2363_);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_m_2360_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; lean_object* v_unused_2403_; 
v_unused_2402_ = lean_ctor_get(v_m_2360_, 1);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_m_2360_, 0);
lean_dec(v_unused_2403_);
v___x_2382_ = v_m_2360_;
v_isShared_2383_ = v_isSharedCheck_2401_;
goto v_resetjp_2381_;
}
else
{
lean_dec(v_m_2360_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2401_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v_size_x27_2385_; lean_object* v___x_2386_; lean_object* v_buckets_x27_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2384_ = lean_unsigned_to_nat(1u);
v_size_x27_2385_ = lean_nat_add(v_size_2363_, v___x_2384_);
lean_dec(v_size_2363_);
lean_inc(v_bkt_2379_);
v___x_2386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2386_, 0, v_a_2361_);
lean_ctor_set(v___x_2386_, 1, v_b_2362_);
lean_ctor_set(v___x_2386_, 2, v_bkt_2379_);
v_buckets_x27_2387_ = lean_array_uset(v_buckets_2364_, v___x_2378_, v___x_2386_);
v___x_2388_ = lean_unsigned_to_nat(4u);
v___x_2389_ = lean_nat_mul(v_size_x27_2385_, v___x_2388_);
v___x_2390_ = lean_unsigned_to_nat(3u);
v___x_2391_ = lean_nat_div(v___x_2389_, v___x_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_array_get_size(v_buckets_x27_2387_);
v___x_2393_ = lean_nat_dec_le(v___x_2391_, v___x_2392_);
lean_dec(v___x_2391_);
if (v___x_2393_ == 0)
{
lean_object* v_val_2394_; lean_object* v___x_2396_; 
v_val_2394_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_buckets_x27_2387_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 1, v_val_2394_);
lean_ctor_set(v___x_2382_, 0, v_size_x27_2385_);
v___x_2396_ = v___x_2382_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_size_x27_2385_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_val_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
else
{
lean_object* v___x_2399_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 1, v_buckets_x27_2387_);
lean_ctor_set(v___x_2382_, 0, v_size_x27_2385_);
v___x_2399_ = v___x_2382_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_size_x27_2385_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_buckets_x27_2387_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
else
{
lean_dec(v_b_2362_);
lean_dec(v_a_2361_);
return v_m_2360_;
}
}
}
}
lean_object* l_Lean_registerTraceClass(lean_object* v_traceClassName_2409_, uint8_t v_inherited_2410_, lean_object* v_ref_2411_){
_start:
{
lean_object* v___x_2413_; lean_object* v_optionName_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2413_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v_optionName_2414_ = l_Lean_Name_append(v___x_2413_, v_traceClassName_2409_);
v___x_2415_ = ((lean_object*)(l_Lean_registerTraceClass___closed__0));
v___x_2416_ = ((lean_object*)(l_Lean_registerTraceClass___closed__1));
v___x_2417_ = lean_box(0);
lean_inc_n(v_optionName_2414_, 2);
v___x_2418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2418_, 0, v_optionName_2414_);
lean_ctor_set(v___x_2418_, 1, v_ref_2411_);
lean_ctor_set(v___x_2418_, 2, v___x_2415_);
lean_ctor_set(v___x_2418_, 3, v___x_2416_);
lean_ctor_set(v___x_2418_, 4, v___x_2417_);
v___x_2419_ = lean_register_option(v_optionName_2414_, v___x_2418_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2435_; 
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2435_ == 0)
{
lean_object* v_unused_2436_; 
v_unused_2436_ = lean_ctor_get(v___x_2419_, 0);
lean_dec(v_unused_2436_);
v___x_2421_ = v___x_2419_;
v_isShared_2422_ = v_isSharedCheck_2435_;
goto v_resetjp_2420_;
}
else
{
lean_dec(v___x_2419_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2435_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
if (v_inherited_2410_ == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
lean_dec(v_optionName_2414_);
v___x_2423_ = lean_box(0);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2423_);
v___x_2425_ = v___x_2421_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2427_ = l_Lean_inheritedTraceOptions;
v___x_2428_ = lean_st_ref_take(v___x_2427_);
v___x_2429_ = lean_box(0);
v___x_2430_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v___x_2428_, v_optionName_2414_, v___x_2429_);
v___x_2431_ = lean_st_ref_put(v___x_2427_, v___x_2430_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2431_);
v___x_2433_ = v___x_2421_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_dec(v_optionName_2414_);
return v___x_2419_;
}
}
}
LEAN_EXPORT void l_Lean_registerTraceClass_0interp(lean_interpreter_value* stack)
{
lean_object* v_traceClassName_2409_ = stack[0].m_obj;
uint8_t v_inherited_2410_ = stack[1].m_num;
lean_object* v_ref_2411_ = stack[2].m_obj;
lean_object* v_res_2437_;
v_res_2437_ = l_Lean_registerTraceClass(v_traceClassName_2409_, v_inherited_2410_, v_ref_2411_);
stack->m_obj
 = v_res_2437_;
}
LEAN_EXPORT lean_object* l_Lean_registerTraceClass___boxed(lean_object* v_traceClassName_2438_, lean_object* v_inherited_2439_, lean_object* v_ref_2440_, lean_object* v_a_2441_){
_start:
{
uint8_t v_inherited_boxed_2442_; lean_object* v_res_2443_; 
v_inherited_boxed_2442_ = lean_unbox(v_inherited_2439_);
v_res_2443_ = l_Lean_registerTraceClass(v_traceClassName_2438_, v_inherited_boxed_2442_, v_ref_2440_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0(lean_object* v_00_u03b2_2444_, lean_object* v_m_2445_, lean_object* v_a_2446_, lean_object* v_b_2447_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0___redArg(v_m_2445_, v_a_2446_, v_b_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0(lean_object* v_00_u03b2_2449_, lean_object* v_data_2450_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0___redArg(v_data_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2452_, lean_object* v_i_2453_, lean_object* v_source_2454_, lean_object* v_target_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1___redArg(v_i_2453_, v_source_2454_, v_target_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2457_, lean_object* v_x_2458_, lean_object* v_x_2459_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_registerTraceClass_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2458_, v_x_2459_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_2471_ = l_String_toRawSubstring_x27(v___x_2470_);
return v___x_2471_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__13));
v___x_2478_ = l_String_toRawSubstring_x27(v___x_2477_);
return v___x_2478_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__18));
v___x_2484_ = l_String_toRawSubstring_x27(v___x_2483_);
return v___x_2484_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31(void){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Array_mkArray0___redArg();
return v___x_2512_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__40));
v___x_2539_ = l_String_toRawSubstring_x27(v___x_2538_);
return v___x_2539_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58(void){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__57));
v___x_2575_ = l_String_toRawSubstring_x27(v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(lean_object* v_id_2597_, lean_object* v_s_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v_msg_2698_; lean_object* v_quotContext_2699_; lean_object* v_currMacroScope_2700_; lean_object* v_ref_2701_; lean_object* v___y_2702_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
lean_inc(v_s_2598_);
v___x_2748_ = l_Lean_Syntax_getKind(v_s_2598_);
v___x_2749_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__49));
v___x_2750_ = lean_name_eq(v___x_2748_, v___x_2749_);
lean_dec(v___x_2748_);
if (v___x_2750_ == 0)
{
lean_object* v_quotContext_2751_; lean_object* v_currMacroScope_2752_; lean_object* v_ref_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_quotContext_2751_ = lean_ctor_get(v_a_2599_, 1);
v_currMacroScope_2752_ = lean_ctor_get(v_a_2599_, 2);
v_ref_2753_ = lean_ctor_get(v_a_2599_, 5);
v___x_2754_ = l_Lean_SourceInfo_fromRef(v_ref_2753_, v___x_2750_);
v___x_2755_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__51));
v___x_2756_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__52));
v___x_2757_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
lean_inc_n(v___x_2754_, 8);
v___x_2758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2754_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2760_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2761_ = lean_box(0);
lean_inc_n(v_currMacroScope_2752_, 3);
lean_inc_n(v_quotContext_2751_, 3);
v___x_2762_ = l_Lean_addMacroScope(v_quotContext_2751_, v___x_2761_, v_currMacroScope_2752_);
v___x_2763_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__55));
v___x_2764_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2754_);
lean_ctor_set(v___x_2764_, 1, v___x_2760_);
lean_ctor_set(v___x_2764_, 2, v___x_2762_);
lean_ctor_set(v___x_2764_, 3, v___x_2763_);
v___x_2765_ = l_Lean_Syntax_node1(v___x_2754_, v___x_2759_, v___x_2764_);
v___x_2766_ = l_Lean_Syntax_node2(v___x_2754_, v___x_2756_, v___x_2758_, v___x_2765_);
v___x_2767_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__56));
v___x_2768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2754_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2770_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__58);
v___x_2771_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__59));
v___x_2772_ = l_Lean_addMacroScope(v_quotContext_2751_, v___x_2771_, v_currMacroScope_2752_);
v___x_2773_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__64));
v___x_2774_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2754_);
lean_ctor_set(v___x_2774_, 1, v___x_2770_);
lean_ctor_set(v___x_2774_, 2, v___x_2772_);
lean_ctor_set(v___x_2774_, 3, v___x_2773_);
v___x_2775_ = l_Lean_Syntax_node1(v___x_2754_, v___x_2769_, v___x_2774_);
v___x_2776_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2754_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = l_Lean_Syntax_node5(v___x_2754_, v___x_2755_, v___x_2766_, v_s_2598_, v___x_2768_, v___x_2775_, v___x_2777_);
v_msg_2698_ = v___x_2778_;
v_quotContext_2699_ = v_quotContext_2751_;
v_currMacroScope_2700_ = v_currMacroScope_2752_;
v_ref_2701_ = v_ref_2753_;
v___y_2702_ = v_a_2600_;
goto v___jp_2697_;
}
else
{
lean_object* v_quotContext_2779_; lean_object* v_currMacroScope_2780_; lean_object* v_ref_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_quotContext_2779_ = lean_ctor_get(v_a_2599_, 1);
v_currMacroScope_2780_ = lean_ctor_get(v_a_2599_, 2);
v_ref_2781_ = lean_ctor_get(v_a_2599_, 5);
v___x_2782_ = 0;
v___x_2783_ = l_Lean_SourceInfo_fromRef(v_ref_2781_, v___x_2782_);
v___x_2784_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__66));
v___x_2785_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__67));
lean_inc(v___x_2783_);
v___x_2786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2783_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = l_Lean_Syntax_node2(v___x_2783_, v___x_2784_, v___x_2786_, v_s_2598_);
lean_inc(v_currMacroScope_2780_);
lean_inc(v_quotContext_2779_);
v_msg_2698_ = v___x_2787_;
v_quotContext_2699_ = v_quotContext_2779_;
v_currMacroScope_2700_ = v_currMacroScope_2780_;
v_ref_2701_ = v_ref_2781_;
v___y_2702_ = v_a_2600_;
goto v___jp_2697_;
}
v___jp_2601_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_inc_n(v___y_2612_, 8);
lean_inc(v___y_2624_);
lean_inc_n(v___y_2618_, 30);
v___x_2626_ = l_Lean_Syntax_node5(v___y_2618_, v___y_2624_, v___y_2617_, v___y_2612_, v___y_2612_, v___y_2623_, v___y_2625_);
lean_inc(v___y_2621_);
v___x_2627_ = l_Lean_Syntax_node1(v___y_2618_, v___y_2621_, v___x_2626_);
lean_inc(v___y_2604_);
v___x_2628_ = l_Lean_Syntax_node4(v___y_2618_, v___y_2604_, v___y_2605_, v___y_2612_, v___y_2608_, v___x_2627_);
lean_inc_n(v___y_2614_, 3);
v___x_2629_ = l_Lean_Syntax_node2(v___y_2618_, v___y_2614_, v___x_2628_, v___y_2612_);
v___x_2630_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__0));
lean_inc_ref_n(v___y_2619_, 7);
lean_inc_ref_n(v___y_2613_, 7);
lean_inc_ref_n(v___y_2616_, 10);
v___x_2631_ = l_Lean_Name_mkStr4(v___y_2616_, v___y_2613_, v___y_2619_, v___x_2630_);
v___x_2632_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__1));
v___x_2633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___y_2618_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__2));
v___x_2635_ = l_Lean_Name_mkStr4(v___y_2616_, v___y_2613_, v___y_2619_, v___x_2634_);
v___x_2636_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__3));
v___x_2637_ = l_Lean_Name_mkStr4(v___y_2616_, v___y_2613_, v___y_2619_, v___x_2636_);
v___x_2638_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__4));
v___x_2639_ = l_Lean_Name_mkStr4(v___y_2616_, v___y_2613_, v___y_2619_, v___x_2638_);
v___x_2640_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__5));
v___x_2641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___y_2618_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__7));
v___x_2643_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__8);
v___x_2644_ = lean_box(0);
lean_inc_n(v___y_2611_, 2);
lean_inc_n(v___y_2607_, 2);
v___x_2645_ = l_Lean_addMacroScope(v___y_2607_, v___x_2644_, v___y_2611_);
v___x_2646_ = l_Lean_Name_mkStr1(v___y_2616_);
v___x_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
lean_inc_n(v___y_2622_, 2);
v___x_2648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
lean_ctor_set(v___x_2648_, 1, v___y_2622_);
v___x_2649_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2649_, 0, v___y_2618_);
lean_ctor_set(v___x_2649_, 1, v___x_2643_);
lean_ctor_set(v___x_2649_, 2, v___x_2645_);
lean_ctor_set(v___x_2649_, 3, v___x_2648_);
v___x_2650_ = l_Lean_Syntax_node1(v___y_2618_, v___x_2642_, v___x_2649_);
v___x_2651_ = l_Lean_Syntax_node2(v___y_2618_, v___x_2639_, v___x_2641_, v___x_2650_);
v___x_2652_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__9));
v___x_2653_ = l_Lean_Name_mkStr4(v___y_2616_, v___y_2613_, v___y_2619_, v___x_2652_);
v___x_2654_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__10));
v___x_2655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___y_2618_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__11));
v___x_2657_ = l_Lean_Name_mkStr4(v___y_2616_, v___y_2613_, v___y_2619_, v___x_2656_);
v___x_2658_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__12));
v___x_2659_ = l_Lean_Name_mkStr4(v___y_2616_, v___y_2613_, v___y_2619_, v___x_2658_);
v___x_2660_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__14);
v___x_2661_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__15));
v___x_2662_ = l_Lean_Name_mkStr2(v___y_2616_, v___x_2661_);
lean_inc(v___x_2662_);
v___x_2663_ = l_Lean_addMacroScope(v___y_2607_, v___x_2662_, v___y_2611_);
v___x_2664_ = lean_box(0);
v___x_2665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2662_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v___y_2622_);
v___x_2667_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2667_, 0, v___y_2618_);
lean_ctor_set(v___x_2667_, 1, v___x_2660_);
lean_ctor_set(v___x_2667_, 2, v___x_2663_);
lean_ctor_set(v___x_2667_, 3, v___x_2666_);
lean_inc(v___y_2615_);
lean_inc_n(v___y_2603_, 4);
v___x_2668_ = l_Lean_Syntax_node1(v___y_2618_, v___y_2603_, v___y_2615_);
lean_inc(v___x_2659_);
v___x_2669_ = l_Lean_Syntax_node2(v___y_2618_, v___x_2659_, v___x_2667_, v___x_2668_);
lean_inc(v___x_2657_);
v___x_2670_ = l_Lean_Syntax_node1(v___y_2618_, v___x_2657_, v___x_2669_);
v___x_2671_ = l_Lean_Syntax_node2(v___y_2618_, v___x_2653_, v___x_2655_, v___x_2670_);
v___x_2672_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__16));
v___x_2673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___y_2618_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = l_Lean_Syntax_node3(v___y_2618_, v___x_2637_, v___x_2651_, v___x_2671_, v___x_2673_);
v___x_2675_ = l_Lean_Syntax_node2(v___y_2618_, v___x_2635_, v___y_2612_, v___x_2674_);
v___x_2676_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__17));
v___x_2677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___y_2618_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
v___x_2678_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__19);
v___x_2679_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__20));
v___x_2680_ = l_Lean_Name_mkStr2(v___y_2616_, v___x_2679_);
lean_inc(v___x_2680_);
v___x_2681_ = l_Lean_addMacroScope(v___y_2607_, v___x_2680_, v___y_2611_);
v___x_2682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set(v___x_2682_, 1, v___x_2664_);
v___x_2683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v___y_2622_);
v___x_2684_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2684_, 0, v___y_2618_);
lean_ctor_set(v___x_2684_, 1, v___x_2678_);
lean_ctor_set(v___x_2684_, 2, v___x_2681_);
lean_ctor_set(v___x_2684_, 3, v___x_2683_);
v___x_2685_ = l_Lean_Syntax_node2(v___y_2618_, v___y_2603_, v___y_2615_, v___y_2610_);
v___x_2686_ = l_Lean_Syntax_node2(v___y_2618_, v___x_2659_, v___x_2684_, v___x_2685_);
v___x_2687_ = l_Lean_Syntax_node1(v___y_2618_, v___x_2657_, v___x_2686_);
v___x_2688_ = l_Lean_Syntax_node2(v___y_2618_, v___y_2614_, v___x_2687_, v___y_2612_);
v___x_2689_ = l_Lean_Syntax_node1(v___y_2618_, v___y_2603_, v___x_2688_);
lean_inc_n(v___y_2606_, 2);
v___x_2690_ = l_Lean_Syntax_node1(v___y_2618_, v___y_2606_, v___x_2689_);
v___x_2691_ = l_Lean_Syntax_node6(v___y_2618_, v___x_2631_, v___x_2633_, v___x_2675_, v___x_2677_, v___x_2690_, v___y_2612_, v___y_2612_);
v___x_2692_ = l_Lean_Syntax_node2(v___y_2618_, v___y_2614_, v___x_2691_, v___y_2612_);
v___x_2693_ = l_Lean_Syntax_node2(v___y_2618_, v___y_2603_, v___x_2629_, v___x_2692_);
v___x_2694_ = l_Lean_Syntax_node1(v___y_2618_, v___y_2606_, v___x_2693_);
lean_inc(v___y_2620_);
v___x_2695_ = l_Lean_Syntax_node2(v___y_2618_, v___y_2620_, v___y_2602_, v___x_2694_);
v___x_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
lean_ctor_set(v___x_2696_, 1, v___y_2609_);
return v___x_2696_;
}
v___jp_2697_:
{
uint8_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2703_ = 0;
v___x_2704_ = l_Lean_SourceInfo_fromRef(v_ref_2701_, v___x_2703_);
v___x_2705_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__0));
v___x_2706_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__1));
v___x_2707_ = ((lean_object*)(l_Lean_registerTraceClass___auto__1___closed__0));
v___x_2708_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__22));
v___x_2709_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__23));
lean_inc_n(v___x_2704_, 7);
v___x_2710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2704_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__25));
v___x_2712_ = ((lean_object*)(l_Lean_MonadTrace_getInheritedTraceOptions___autoParam___closed__9));
v___x_2713_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__27));
v___x_2714_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__29));
v___x_2715_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__30));
v___x_2716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2704_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__31);
v___x_2718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2704_);
lean_ctor_set(v___x_2718_, 1, v___x_2712_);
lean_ctor_set(v___x_2718_, 2, v___x_2717_);
v___x_2719_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__33));
lean_inc_ref(v___x_2718_);
v___x_2720_ = l_Lean_Syntax_node1(v___x_2704_, v___x_2719_, v___x_2718_);
v___x_2721_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__35));
v___x_2722_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__37));
v___x_2723_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__39));
v___x_2724_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41, &l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41_once, _init_l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__41);
v___x_2725_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__42));
lean_inc(v_currMacroScope_2700_);
lean_inc(v_quotContext_2699_);
v___x_2726_ = l_Lean_addMacroScope(v_quotContext_2699_, v___x_2725_, v_currMacroScope_2700_);
v___x_2727_ = lean_box(0);
v___x_2728_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2704_);
lean_ctor_set(v___x_2728_, 1, v___x_2724_);
lean_ctor_set(v___x_2728_, 2, v___x_2726_);
lean_ctor_set(v___x_2728_, 3, v___x_2727_);
lean_inc_ref(v___x_2728_);
v___x_2729_ = l_Lean_Syntax_node1(v___x_2704_, v___x_2723_, v___x_2728_);
v___x_2730_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__43));
v___x_2731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2704_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = l_Lean_Syntax_getId(v_id_2597_);
v___x_2733_ = l_Lean_Name_eraseMacroScopes(v___x_2732_);
lean_dec(v___x_2732_);
lean_inc(v___x_2733_);
v___x_2734_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2727_, v___x_2733_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_quoteNameMk(v___x_2733_);
v___y_2602_ = v___x_2710_;
v___y_2603_ = v___x_2712_;
v___y_2604_ = v___x_2714_;
v___y_2605_ = v___x_2716_;
v___y_2606_ = v___x_2711_;
v___y_2607_ = v_quotContext_2699_;
v___y_2608_ = v___x_2720_;
v___y_2609_ = v___y_2702_;
v___y_2610_ = v_msg_2698_;
v___y_2611_ = v_currMacroScope_2700_;
v___y_2612_ = v___x_2718_;
v___y_2613_ = v___x_2706_;
v___y_2614_ = v___x_2713_;
v___y_2615_ = v___x_2728_;
v___y_2616_ = v___x_2705_;
v___y_2617_ = v___x_2729_;
v___y_2618_ = v___x_2704_;
v___y_2619_ = v___x_2707_;
v___y_2620_ = v___x_2708_;
v___y_2621_ = v___x_2721_;
v___y_2622_ = v___x_2727_;
v___y_2623_ = v___x_2731_;
v___y_2624_ = v___x_2722_;
v___y_2625_ = v___x_2735_;
goto v___jp_2601_;
}
else
{
lean_object* v_val_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
lean_dec(v___x_2733_);
v_val_2736_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_val_2736_);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2737_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__45));
v___x_2738_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__46));
v___x_2739_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___closed__47));
v___x_2740_ = lean_string_intercalate(v___x_2739_, v_val_2736_);
v___x_2741_ = lean_string_append(v___x_2738_, v___x_2740_);
lean_dec_ref(v___x_2740_);
v___x_2742_ = lean_box(2);
v___x_2743_ = l_Lean_Syntax_mkNameLit(v___x_2741_, v___x_2742_);
v___x_2744_ = lean_unsigned_to_nat(1u);
v___x_2745_ = lean_mk_empty_array_with_capacity(v___x_2744_);
v___x_2746_ = lean_array_push(v___x_2745_, v___x_2743_);
v___x_2747_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2742_);
lean_ctor_set(v___x_2747_, 1, v___x_2737_);
lean_ctor_set(v___x_2747_, 2, v___x_2746_);
v___y_2602_ = v___x_2710_;
v___y_2603_ = v___x_2712_;
v___y_2604_ = v___x_2714_;
v___y_2605_ = v___x_2716_;
v___y_2606_ = v___x_2711_;
v___y_2607_ = v_quotContext_2699_;
v___y_2608_ = v___x_2720_;
v___y_2609_ = v___y_2702_;
v___y_2610_ = v_msg_2698_;
v___y_2611_ = v_currMacroScope_2700_;
v___y_2612_ = v___x_2718_;
v___y_2613_ = v___x_2706_;
v___y_2614_ = v___x_2713_;
v___y_2615_ = v___x_2728_;
v___y_2616_ = v___x_2705_;
v___y_2617_ = v___x_2729_;
v___y_2618_ = v___x_2704_;
v___y_2619_ = v___x_2707_;
v___y_2620_ = v___x_2708_;
v___y_2621_ = v___x_2721_;
v___y_2622_ = v___x_2727_;
v___y_2623_ = v___x_2731_;
v___y_2624_ = v___x_2722_;
v___y_2625_ = v___x_2747_;
goto v___jp_2601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_expandTraceMacro___boxed(lean_object* v_id_2788_, lean_object* v_s_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v_id_2788_, v_s_2789_, v_a_2790_, v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_id_2788_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(lean_object* v_x_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2850_ = ((lean_object*)(l_Lean_doElemTrace_x5b___x5d_____00__closed__1));
lean_inc(v_x_2847_);
v___x_2851_ = l_Lean_Syntax_isOfKind(v_x_2847_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec(v_x_2847_);
v___x_2852_ = lean_box(1);
v___x_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v_a_2849_);
return v___x_2853_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v_a_2859_; lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
v___x_2854_ = lean_unsigned_to_nat(1u);
v___x_2855_ = l_Lean_Syntax_getArg(v_x_2847_, v___x_2854_);
v___x_2856_ = lean_unsigned_to_nat(3u);
v___x_2857_ = l_Lean_Syntax_getArg(v_x_2847_, v___x_2856_);
lean_dec(v_x_2847_);
v___x_2858_ = l___private_Lean_Util_Trace_0__Lean_expandTraceMacro(v___x_2855_, v___x_2857_, v_a_2848_, v_a_2849_);
lean_dec(v___x_2855_);
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
v_a_2860_ = lean_ctor_get(v___x_2858_, 1);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2858_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_inc(v_a_2859_);
lean_dec(v___x_2858_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2859_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1___boxed(lean_object* v_x_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean___aux__Lean__Util__Trace______macroRules__Lean__doElemTrace_x5b___x5d______1(v_x_2868_, v_a_2869_, v_a_2870_);
lean_dec_ref(v_a_2869_);
return v_res_2871_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(lean_object* v_inst_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_always_2876_, lean_object* v_inst_2877_, lean_object* v_cls_2878_, uint8_t v_collapsed_2879_, lean_object* v_tag_2880_, lean_object* v_opts_2881_, uint8_t v_clsEnabled_2882_, lean_object* v_oldTraces_2883_, lean_object* v_ref_2884_, lean_object* v_msg_2885_, lean_object* v_resStartStop_2886_){
_start:
{
lean_object* v___x_2887_; lean_object* v_toBind_2888_; lean_object* v___x_2889_; lean_object* v_snd_2890_; lean_object* v_fst_2891_; lean_object* v_fst_2892_; lean_object* v_snd_2893_; lean_object* v___f_2894_; lean_object* v___f_2895_; lean_object* v_data_2897_; lean_object* v___x_2900_; lean_object* v___x_2901_; uint8_t v___y_2912_; double v___y_2917_; uint8_t v___x_2922_; 
v___x_2887_ = l_Lean_KVMap_instValueBool;
v_toBind_2888_ = lean_ctor_get(v_inst_2872_, 1);
lean_inc(v_toBind_2888_);
v___x_2889_ = l_instMonadExceptOfMonadExceptOf___redArg(v_always_2876_);
v_snd_2890_ = lean_ctor_get(v_resStartStop_2886_, 1);
lean_inc(v_snd_2890_);
v_fst_2891_ = lean_ctor_get(v_resStartStop_2886_, 0);
lean_inc_n(v_fst_2891_, 2);
lean_dec_ref(v_resStartStop_2886_);
v_fst_2892_ = lean_ctor_get(v_snd_2890_, 0);
lean_inc(v_fst_2892_);
v_snd_2893_ = lean_ctor_get(v_snd_2890_, 1);
lean_inc(v_snd_2893_);
lean_dec(v_snd_2890_);
lean_inc_ref(v_oldTraces_2883_);
v___f_2894_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2894_, 0, v_oldTraces_2883_);
lean_inc_ref(v_inst_2872_);
v___f_2895_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2895_, 0, v_inst_2872_);
lean_closure_set(v___f_2895_, 1, v___x_2889_);
lean_closure_set(v___f_2895_, 2, v_fst_2891_);
v___x_2900_ = l_Lean_trace_profiler;
v___x_2901_ = l_Lean_Option_get___redArg(v___x_2887_, v_opts_2881_, v___x_2900_);
v___x_2922_ = lean_unbox(v___x_2901_);
if (v___x_2922_ == 0)
{
uint8_t v___x_2923_; 
v___x_2923_ = lean_unbox(v___x_2901_);
v___y_2912_ = v___x_2923_;
goto v___jp_2911_;
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v___x_2924_ = l_Lean_KVMap_instValueNat;
v___x_2925_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2926_ = l_Lean_Option_get___redArg(v___x_2887_, v_opts_2881_, v___x_2925_);
v___x_2927_ = lean_unbox(v___x_2926_);
lean_dec(v___x_2926_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; lean_object* v___x_2929_; double v___x_2930_; double v___x_2931_; double v___x_2932_; 
v___x_2928_ = l_Lean_trace_profiler_threshold;
v___x_2929_ = l_Lean_Option_get___redArg(v___x_2924_, v_opts_2881_, v___x_2928_);
v___x_2930_ = lean_float_of_nat(v___x_2929_);
v___x_2931_ = lean_float_once(&l_Lean_trace_profiler_threshold_unitAdjusted___closed__0, &l_Lean_trace_profiler_threshold_unitAdjusted___closed__0_once, _init_l_Lean_trace_profiler_threshold_unitAdjusted___closed__0);
v___x_2932_ = lean_float_div(v___x_2930_, v___x_2931_);
v___y_2917_ = v___x_2932_;
goto v___jp_2916_;
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2934_; double v___x_2935_; 
v___x_2933_ = l_Lean_trace_profiler_threshold;
v___x_2934_ = l_Lean_Option_get___redArg(v___x_2924_, v_opts_2881_, v___x_2933_);
v___x_2935_ = lean_float_of_nat(v___x_2934_);
v___y_2917_ = v___x_2935_;
goto v___jp_2916_;
}
}
v___jp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg(v_inst_2872_, v_inst_2873_, v_inst_2874_, v_inst_2875_, v_oldTraces_2883_, v_data_2897_, v_ref_2884_, v_msg_2885_);
v___x_2899_ = lean_apply_4(v_toBind_2888_, lean_box(0), lean_box(0), v___x_2898_, v___f_2895_);
return v___x_2899_;
}
v___jp_2902_:
{
lean_object* v_result_2903_; lean_object* v___x_2904_; double v___x_2905_; lean_object* v_data_2906_; uint8_t v___x_2907_; 
v_result_2903_ = lean_apply_1(v_inst_2877_, v_fst_2891_);
v___x_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2904_, 0, v_result_2903_);
v___x_2905_ = lean_float_once(&l_Lean_addTrace___redArg___lam__0___closed__0, &l_Lean_addTrace___redArg___lam__0___closed__0_once, _init_l_Lean_addTrace___redArg___lam__0___closed__0);
lean_inc_ref(v_tag_2880_);
lean_inc_ref(v___x_2904_);
lean_inc(v_cls_2878_);
v_data_2906_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2906_, 0, v_cls_2878_);
lean_ctor_set(v_data_2906_, 1, v___x_2904_);
lean_ctor_set(v_data_2906_, 2, v_tag_2880_);
lean_ctor_set_float(v_data_2906_, sizeof(void*)*3, v___x_2905_);
lean_ctor_set_float(v_data_2906_, sizeof(void*)*3 + 8, v___x_2905_);
lean_ctor_set_uint8(v_data_2906_, sizeof(void*)*3 + 16, v_collapsed_2879_);
v___x_2907_ = lean_unbox(v___x_2901_);
lean_dec(v___x_2901_);
if (v___x_2907_ == 0)
{
lean_dec_ref_known(v___x_2904_, 1);
lean_dec(v_snd_2893_);
lean_dec(v_fst_2892_);
lean_dec_ref(v_tag_2880_);
lean_dec(v_cls_2878_);
v_data_2897_ = v_data_2906_;
goto v___jp_2896_;
}
else
{
lean_object* v_data_2908_; double v___x_2909_; double v___x_2910_; 
lean_dec_ref_known(v_data_2906_, 3);
v_data_2908_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2908_, 0, v_cls_2878_);
lean_ctor_set(v_data_2908_, 1, v___x_2904_);
lean_ctor_set(v_data_2908_, 2, v_tag_2880_);
v___x_2909_ = lean_unbox_float(v_fst_2892_);
lean_dec(v_fst_2892_);
lean_ctor_set_float(v_data_2908_, sizeof(void*)*3, v___x_2909_);
v___x_2910_ = lean_unbox_float(v_snd_2893_);
lean_dec(v_snd_2893_);
lean_ctor_set_float(v_data_2908_, sizeof(void*)*3 + 8, v___x_2910_);
lean_ctor_set_uint8(v_data_2908_, sizeof(void*)*3 + 16, v_collapsed_2879_);
v_data_2897_ = v_data_2908_;
goto v___jp_2896_;
}
}
v___jp_2911_:
{
if (v_clsEnabled_2882_ == 0)
{
if (v___y_2912_ == 0)
{
lean_object* v_modifyTraceState_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_dec(v___x_2901_);
lean_dec(v_snd_2893_);
lean_dec(v_fst_2892_);
lean_dec(v_fst_2891_);
lean_dec_ref(v_msg_2885_);
lean_dec(v_ref_2884_);
lean_dec_ref(v_oldTraces_2883_);
lean_dec_ref(v_tag_2880_);
lean_dec(v_cls_2878_);
lean_dec_ref(v_inst_2877_);
lean_dec(v_inst_2875_);
lean_dec_ref(v_inst_2874_);
lean_dec_ref(v_inst_2872_);
v_modifyTraceState_2913_ = lean_ctor_get(v_inst_2873_, 0);
lean_inc(v_modifyTraceState_2913_);
lean_dec_ref(v_inst_2873_);
v___x_2914_ = lean_apply_1(v_modifyTraceState_2913_, v___f_2894_);
v___x_2915_ = lean_apply_4(v_toBind_2888_, lean_box(0), lean_box(0), v___x_2914_, v___f_2895_);
return v___x_2915_;
}
else
{
lean_dec_ref(v___f_2894_);
goto v___jp_2902_;
}
}
else
{
lean_dec_ref(v___f_2894_);
goto v___jp_2902_;
}
}
v___jp_2916_:
{
double v___x_2918_; double v___x_2919_; double v___x_2920_; uint8_t v___x_2921_; 
v___x_2918_ = lean_unbox_float(v_snd_2893_);
v___x_2919_ = lean_unbox_float(v_fst_2892_);
v___x_2920_ = lean_float_sub(v___x_2918_, v___x_2919_);
v___x_2921_ = lean_float_decLt(v___y_2917_, v___x_2920_);
v___y_2912_ = v___x_2921_;
goto v___jp_2911_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2872_ = stack[0].m_obj;
lean_object* v_inst_2873_ = stack[1].m_obj;
lean_object* v_inst_2874_ = stack[2].m_obj;
lean_object* v_inst_2875_ = stack[3].m_obj;
lean_object* v_always_2876_ = stack[4].m_obj;
lean_object* v_inst_2877_ = stack[5].m_obj;
lean_object* v_cls_2878_ = stack[6].m_obj;
uint8_t v_collapsed_2879_ = stack[7].m_num;
lean_object* v_tag_2880_ = stack[8].m_obj;
lean_object* v_opts_2881_ = stack[9].m_obj;
uint8_t v_clsEnabled_2882_ = stack[10].m_num;
lean_object* v_oldTraces_2883_ = stack[11].m_obj;
lean_object* v_ref_2884_ = stack[12].m_obj;
lean_object* v_msg_2885_ = stack[13].m_obj;
lean_object* v_resStartStop_2886_ = stack[14].m_obj;
lean_object* v_res_2936_;
v_res_2936_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2872_, v_inst_2873_, v_inst_2874_, v_inst_2875_, v_always_2876_, v_inst_2877_, v_cls_2878_, v_collapsed_2879_, v_tag_2880_, v_opts_2881_, v_clsEnabled_2882_, v_oldTraces_2883_, v_ref_2884_, v_msg_2885_, v_resStartStop_2886_);
stack->m_obj
 = v_res_2936_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg___boxed(lean_object* v_inst_2937_, lean_object* v_inst_2938_, lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_always_2941_, lean_object* v_inst_2942_, lean_object* v_cls_2943_, lean_object* v_collapsed_2944_, lean_object* v_tag_2945_, lean_object* v_opts_2946_, lean_object* v_clsEnabled_2947_, lean_object* v_oldTraces_2948_, lean_object* v_ref_2949_, lean_object* v_msg_2950_, lean_object* v_resStartStop_2951_){
_start:
{
uint8_t v_collapsed_boxed_2952_; uint8_t v_clsEnabled_boxed_2953_; lean_object* v_res_2954_; 
v_collapsed_boxed_2952_ = lean_unbox(v_collapsed_2944_);
v_clsEnabled_boxed_2953_ = lean_unbox(v_clsEnabled_2947_);
v_res_2954_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2937_, v_inst_2938_, v_inst_2939_, v_inst_2940_, v_always_2941_, v_inst_2942_, v_cls_2943_, v_collapsed_boxed_2952_, v_tag_2945_, v_opts_2946_, v_clsEnabled_boxed_2953_, v_oldTraces_2948_, v_ref_2949_, v_msg_2950_, v_resStartStop_2951_);
lean_dec_ref(v_opts_2946_);
return v_res_2954_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_object* v_00_u03b1_2955_, lean_object* v_m_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_00_u03b5_2959_, lean_object* v_inst_2960_, lean_object* v_inst_2961_, lean_object* v_always_2962_, lean_object* v_inst_2963_, lean_object* v_cls_2964_, uint8_t v_collapsed_2965_, lean_object* v_tag_2966_, lean_object* v_opts_2967_, uint8_t v_clsEnabled_2968_, lean_object* v_oldTraces_2969_, lean_object* v_ref_2970_, lean_object* v_msg_2971_, lean_object* v_resStartStop_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2957_, v_inst_2958_, v_inst_2960_, v_inst_2961_, v_always_2962_, v_inst_2963_, v_cls_2964_, v_collapsed_2965_, v_tag_2966_, v_opts_2967_, v_clsEnabled_2968_, v_oldTraces_2969_, v_ref_2970_, v_msg_2971_, v_resStartStop_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2957_ = stack[2].m_obj;
lean_object* v_inst_2958_ = stack[3].m_obj;
lean_object* v_inst_2960_ = stack[5].m_obj;
lean_object* v_inst_2961_ = stack[6].m_obj;
lean_object* v_always_2962_ = stack[7].m_obj;
lean_object* v_inst_2963_ = stack[8].m_obj;
lean_object* v_cls_2964_ = stack[9].m_obj;
uint8_t v_collapsed_2965_ = stack[10].m_num;
lean_object* v_tag_2966_ = stack[11].m_obj;
lean_object* v_opts_2967_ = stack[12].m_obj;
uint8_t v_clsEnabled_2968_ = stack[13].m_num;
lean_object* v_oldTraces_2969_ = stack[14].m_obj;
lean_object* v_ref_2970_ = stack[15].m_obj;
lean_object* v_msg_2971_ = stack[16].m_obj;
lean_object* v_resStartStop_2972_ = stack[17].m_obj;
lean_object* v_res_2974_;
v_res_2974_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(lean_box(0), lean_box(0), v_inst_2957_, v_inst_2958_, lean_box(0), v_inst_2960_, v_inst_2961_, v_always_2962_, v_inst_2963_, v_cls_2964_, v_collapsed_2965_, v_tag_2966_, v_opts_2967_, v_clsEnabled_2968_, v_oldTraces_2969_, v_ref_2970_, v_msg_2971_, v_resStartStop_2972_);
stack->m_obj
 = v_res_2974_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___boxed(lean_object** _args){
lean_object* v_00_u03b1_2975_ = _args[0];
lean_object* v_m_2976_ = _args[1];
lean_object* v_inst_2977_ = _args[2];
lean_object* v_inst_2978_ = _args[3];
lean_object* v_00_u03b5_2979_ = _args[4];
lean_object* v_inst_2980_ = _args[5];
lean_object* v_inst_2981_ = _args[6];
lean_object* v_always_2982_ = _args[7];
lean_object* v_inst_2983_ = _args[8];
lean_object* v_cls_2984_ = _args[9];
lean_object* v_collapsed_2985_ = _args[10];
lean_object* v_tag_2986_ = _args[11];
lean_object* v_opts_2987_ = _args[12];
lean_object* v_clsEnabled_2988_ = _args[13];
lean_object* v_oldTraces_2989_ = _args[14];
lean_object* v_ref_2990_ = _args[15];
lean_object* v_msg_2991_ = _args[16];
lean_object* v_resStartStop_2992_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2993_; uint8_t v_clsEnabled_boxed_2994_; lean_object* v_res_2995_; 
v_collapsed_boxed_2993_ = lean_unbox(v_collapsed_2985_);
v_clsEnabled_boxed_2994_ = lean_unbox(v_clsEnabled_2988_);
v_res_2995_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback(v_00_u03b1_2975_, v_m_2976_, v_inst_2977_, v_inst_2978_, v_00_u03b5_2979_, v_inst_2980_, v_inst_2981_, v_always_2982_, v_inst_2983_, v_cls_2984_, v_collapsed_boxed_2993_, v_tag_2986_, v_opts_2987_, v_clsEnabled_boxed_2994_, v_oldTraces_2989_, v_ref_2990_, v_msg_2991_, v_resStartStop_2992_);
lean_dec_ref(v_opts_2987_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__0(lean_object* v_inst_2996_, lean_object* v_____do__lift_2997_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_apply_1(v_inst_2996_, v_____do__lift_2997_);
return v___x_2998_;
}
}
lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1(lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_inst_3001_, lean_object* v_inst_3002_, lean_object* v_always_3003_, lean_object* v_inst_3004_, lean_object* v_cls_3005_, uint8_t v_collapsed_3006_, lean_object* v_tag_3007_, lean_object* v_opts_3008_, uint8_t v_clsEnabled_3009_, lean_object* v_oldTraces_3010_, lean_object* v_ref_3011_, lean_object* v_msg_3012_, lean_object* v_resStartStop_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l___private_Lean_Util_Trace_0__Lean_withTraceNodeBefore_postCallback___redArg(v_inst_2999_, v_inst_3000_, v_inst_3001_, v_inst_3002_, v_always_3003_, v_inst_3004_, v_cls_3005_, v_collapsed_3006_, v_tag_3007_, v_opts_3008_, v_clsEnabled_3009_, v_oldTraces_3010_, v_ref_3011_, v_msg_3012_, v_resStartStop_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT void l_Lean_withTraceNodeBefore___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2999_ = stack[0].m_obj;
lean_object* v_inst_3000_ = stack[1].m_obj;
lean_object* v_inst_3001_ = stack[2].m_obj;
lean_object* v_inst_3002_ = stack[3].m_obj;
lean_object* v_always_3003_ = stack[4].m_obj;
lean_object* v_inst_3004_ = stack[5].m_obj;
lean_object* v_cls_3005_ = stack[6].m_obj;
uint8_t v_collapsed_3006_ = stack[7].m_num;
lean_object* v_tag_3007_ = stack[8].m_obj;
lean_object* v_opts_3008_ = stack[9].m_obj;
uint8_t v_clsEnabled_3009_ = stack[10].m_num;
lean_object* v_oldTraces_3010_ = stack[11].m_obj;
lean_object* v_ref_3011_ = stack[12].m_obj;
lean_object* v_msg_3012_ = stack[13].m_obj;
lean_object* v_resStartStop_3013_ = stack[14].m_obj;
lean_object* v_res_3015_;
v_res_3015_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_2999_, v_inst_3000_, v_inst_3001_, v_inst_3002_, v_always_3003_, v_inst_3004_, v_cls_3005_, v_collapsed_3006_, v_tag_3007_, v_opts_3008_, v_clsEnabled_3009_, v_oldTraces_3010_, v_ref_3011_, v_msg_3012_, v_resStartStop_3013_);
stack->m_obj
 = v_res_3015_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__1___boxed(lean_object* v_inst_3016_, lean_object* v_inst_3017_, lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_always_3020_, lean_object* v_inst_3021_, lean_object* v_cls_3022_, lean_object* v_collapsed_3023_, lean_object* v_tag_3024_, lean_object* v_opts_3025_, lean_object* v_clsEnabled_3026_, lean_object* v_oldTraces_3027_, lean_object* v_ref_3028_, lean_object* v_msg_3029_, lean_object* v_resStartStop_3030_){
_start:
{
uint8_t v_collapsed_boxed_3031_; uint8_t v_clsEnabled_boxed_3032_; lean_object* v_res_3033_; 
v_collapsed_boxed_3031_ = lean_unbox(v_collapsed_3023_);
v_clsEnabled_boxed_3032_ = lean_unbox(v_clsEnabled_3026_);
v_res_3033_ = l_Lean_withTraceNodeBefore___redArg___lam__1(v_inst_3016_, v_inst_3017_, v_inst_3018_, v_inst_3019_, v_always_3020_, v_inst_3021_, v_cls_3022_, v_collapsed_boxed_3031_, v_tag_3024_, v_opts_3025_, v_clsEnabled_boxed_3032_, v_oldTraces_3027_, v_ref_3028_, v_msg_3029_, v_resStartStop_3030_);
lean_dec_ref(v_opts_3025_);
return v_res_3033_;
}
}
lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10(lean_object* v_always_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_inst_3038_, lean_object* v_inst_3039_, lean_object* v_cls_3040_, uint8_t v_collapsed_3041_, lean_object* v_tag_3042_, lean_object* v_opts_3043_, uint8_t v_clsEnabled_3044_, lean_object* v_oldTraces_3045_, lean_object* v_ref_3046_, lean_object* v_toPure_3047_, lean_object* v_toBind_3048_, lean_object* v_k_3049_, lean_object* v___x_3050_, lean_object* v_inst_3051_, lean_object* v_msg_3052_){
_start:
{
lean_object* v_tryCatch_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___f_3056_; lean_object* v___f_3057_; lean_object* v___f_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v_tryCatch_3053_ = lean_ctor_get(v_always_3034_, 1);
lean_inc(v_tryCatch_3053_);
v___x_3054_ = lean_box(v_collapsed_3041_);
v___x_3055_ = lean_box(v_clsEnabled_3044_);
lean_inc_ref(v_opts_3043_);
v___f_3056_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__1___boxed), 15, 14);
lean_closure_set(v___f_3056_, 0, v_inst_3035_);
lean_closure_set(v___f_3056_, 1, v_inst_3036_);
lean_closure_set(v___f_3056_, 2, v_inst_3037_);
lean_closure_set(v___f_3056_, 3, v_inst_3038_);
lean_closure_set(v___f_3056_, 4, v_always_3034_);
lean_closure_set(v___f_3056_, 5, v_inst_3039_);
lean_closure_set(v___f_3056_, 6, v_cls_3040_);
lean_closure_set(v___f_3056_, 7, v___x_3054_);
lean_closure_set(v___f_3056_, 8, v_tag_3042_);
lean_closure_set(v___f_3056_, 9, v_opts_3043_);
lean_closure_set(v___f_3056_, 10, v___x_3055_);
lean_closure_set(v___f_3056_, 11, v_oldTraces_3045_);
lean_closure_set(v___f_3056_, 12, v_ref_3046_);
lean_closure_set(v___f_3056_, 13, v_msg_3052_);
lean_inc_n(v_toPure_3047_, 2);
v___f_3057_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3057_, 0, v_toPure_3047_);
v___f_3058_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__2), 2, 1);
lean_closure_set(v___f_3058_, 0, v_toPure_3047_);
lean_inc(v_toBind_3048_);
v___x_3059_ = lean_apply_4(v_toBind_3048_, lean_box(0), lean_box(0), v_k_3049_, v___f_3058_);
v___x_3060_ = lean_apply_3(v_tryCatch_3053_, lean_box(0), v___x_3059_, v___f_3057_);
v___x_3061_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3062_ = l_Lean_Option_get___redArg(v___x_3050_, v_opts_3043_, v___x_3061_);
lean_dec_ref(v_opts_3043_);
v___x_3063_ = lean_unbox(v___x_3062_);
lean_dec(v___x_3062_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___f_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3064_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__0));
v___x_3065_ = lean_apply_2(v_inst_3051_, lean_box(0), v___x_3064_);
lean_inc(v___x_3065_);
lean_inc_n(v_toBind_3048_, 2);
v___f_3066_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3066_, 0, v_toPure_3047_);
lean_closure_set(v___f_3066_, 1, v_toBind_3048_);
lean_closure_set(v___f_3066_, 2, v___x_3065_);
lean_closure_set(v___f_3066_, 3, v___x_3060_);
v___x_3067_ = lean_apply_4(v_toBind_3048_, lean_box(0), lean_box(0), v___x_3065_, v___f_3066_);
v___x_3068_ = lean_apply_4(v_toBind_3048_, lean_box(0), lean_box(0), v___x_3067_, v___f_3056_);
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___f_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3069_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withStartStop___redArg___closed__1));
v___x_3070_ = lean_apply_2(v_inst_3051_, lean_box(0), v___x_3069_);
lean_inc(v___x_3070_);
lean_inc_n(v_toBind_3048_, 2);
v___f_3071_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__8), 5, 4);
lean_closure_set(v___f_3071_, 0, v_toPure_3047_);
lean_closure_set(v___f_3071_, 1, v_toBind_3048_);
lean_closure_set(v___f_3071_, 2, v___x_3070_);
lean_closure_set(v___f_3071_, 3, v___x_3060_);
v___x_3072_ = lean_apply_4(v_toBind_3048_, lean_box(0), lean_box(0), v___x_3070_, v___f_3071_);
v___x_3073_ = lean_apply_4(v_toBind_3048_, lean_box(0), lean_box(0), v___x_3072_, v___f_3056_);
return v___x_3073_;
}
}
}
LEAN_EXPORT void l_Lean_withTraceNodeBefore___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_always_3034_ = stack[0].m_obj;
lean_object* v_inst_3035_ = stack[1].m_obj;
lean_object* v_inst_3036_ = stack[2].m_obj;
lean_object* v_inst_3037_ = stack[3].m_obj;
lean_object* v_inst_3038_ = stack[4].m_obj;
lean_object* v_inst_3039_ = stack[5].m_obj;
lean_object* v_cls_3040_ = stack[6].m_obj;
uint8_t v_collapsed_3041_ = stack[7].m_num;
lean_object* v_tag_3042_ = stack[8].m_obj;
lean_object* v_opts_3043_ = stack[9].m_obj;
uint8_t v_clsEnabled_3044_ = stack[10].m_num;
lean_object* v_oldTraces_3045_ = stack[11].m_obj;
lean_object* v_ref_3046_ = stack[12].m_obj;
lean_object* v_toPure_3047_ = stack[13].m_obj;
lean_object* v_toBind_3048_ = stack[14].m_obj;
lean_object* v_k_3049_ = stack[15].m_obj;
lean_object* v___x_3050_ = stack[16].m_obj;
lean_object* v_inst_3051_ = stack[17].m_obj;
lean_object* v_msg_3052_ = stack[18].m_obj;
lean_object* v_res_3074_;
v_res_3074_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_always_3034_, v_inst_3035_, v_inst_3036_, v_inst_3037_, v_inst_3038_, v_inst_3039_, v_cls_3040_, v_collapsed_3041_, v_tag_3042_, v_opts_3043_, v_clsEnabled_3044_, v_oldTraces_3045_, v_ref_3046_, v_toPure_3047_, v_toBind_3048_, v_k_3049_, v___x_3050_, v_inst_3051_, v_msg_3052_);
stack->m_obj
 = v_res_3074_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__10___boxed(lean_object** _args){
lean_object* v_always_3075_ = _args[0];
lean_object* v_inst_3076_ = _args[1];
lean_object* v_inst_3077_ = _args[2];
lean_object* v_inst_3078_ = _args[3];
lean_object* v_inst_3079_ = _args[4];
lean_object* v_inst_3080_ = _args[5];
lean_object* v_cls_3081_ = _args[6];
lean_object* v_collapsed_3082_ = _args[7];
lean_object* v_tag_3083_ = _args[8];
lean_object* v_opts_3084_ = _args[9];
lean_object* v_clsEnabled_3085_ = _args[10];
lean_object* v_oldTraces_3086_ = _args[11];
lean_object* v_ref_3087_ = _args[12];
lean_object* v_toPure_3088_ = _args[13];
lean_object* v_toBind_3089_ = _args[14];
lean_object* v_k_3090_ = _args[15];
lean_object* v___x_3091_ = _args[16];
lean_object* v_inst_3092_ = _args[17];
lean_object* v_msg_3093_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_3094_; uint8_t v_clsEnabled_boxed_3095_; lean_object* v_res_3096_; 
v_collapsed_boxed_3094_ = lean_unbox(v_collapsed_3082_);
v_clsEnabled_boxed_3095_ = lean_unbox(v_clsEnabled_3085_);
v_res_3096_ = l_Lean_withTraceNodeBefore___redArg___lam__10(v_always_3075_, v_inst_3076_, v_inst_3077_, v_inst_3078_, v_inst_3079_, v_inst_3080_, v_cls_3081_, v_collapsed_boxed_3094_, v_tag_3083_, v_opts_3084_, v_clsEnabled_boxed_3095_, v_oldTraces_3086_, v_ref_3087_, v_toPure_3088_, v_toBind_3089_, v_k_3090_, v___x_3091_, v_inst_3092_, v_msg_3093_);
return v_res_3096_;
}
}
lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3(lean_object* v_always_3097_, lean_object* v_inst_3098_, lean_object* v_inst_3099_, lean_object* v_inst_3100_, lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_cls_3103_, uint8_t v_collapsed_3104_, lean_object* v_tag_3105_, lean_object* v_opts_3106_, uint8_t v_clsEnabled_3107_, lean_object* v_oldTraces_3108_, lean_object* v_toPure_3109_, lean_object* v_toBind_3110_, lean_object* v_k_3111_, lean_object* v___x_3112_, lean_object* v_inst_3113_, lean_object* v_msg_3114_, lean_object* v___f_3115_, lean_object* v_withRef_3116_, lean_object* v_getRef_3117_, lean_object* v_ref_3118_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___f_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___f_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3119_ = lean_box(v_collapsed_3104_);
v___x_3120_ = lean_box(v_clsEnabled_3107_);
lean_inc_n(v_toBind_3110_, 3);
lean_inc(v_ref_3118_);
v___f_3121_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__10___boxed), 19, 18);
lean_closure_set(v___f_3121_, 0, v_always_3097_);
lean_closure_set(v___f_3121_, 1, v_inst_3098_);
lean_closure_set(v___f_3121_, 2, v_inst_3099_);
lean_closure_set(v___f_3121_, 3, v_inst_3100_);
lean_closure_set(v___f_3121_, 4, v_inst_3101_);
lean_closure_set(v___f_3121_, 5, v_inst_3102_);
lean_closure_set(v___f_3121_, 6, v_cls_3103_);
lean_closure_set(v___f_3121_, 7, v___x_3119_);
lean_closure_set(v___f_3121_, 8, v_tag_3105_);
lean_closure_set(v___f_3121_, 9, v_opts_3106_);
lean_closure_set(v___f_3121_, 10, v___x_3120_);
lean_closure_set(v___f_3121_, 11, v_oldTraces_3108_);
lean_closure_set(v___f_3121_, 12, v_ref_3118_);
lean_closure_set(v___f_3121_, 13, v_toPure_3109_);
lean_closure_set(v___f_3121_, 14, v_toBind_3110_);
lean_closure_set(v___f_3121_, 15, v_k_3111_);
lean_closure_set(v___f_3121_, 16, v___x_3112_);
lean_closure_set(v___f_3121_, 17, v_inst_3113_);
v___x_3122_ = lean_box(0);
v___x_3123_ = lean_apply_1(v_msg_3114_, v___x_3122_);
v___x_3124_ = lean_apply_4(v_toBind_3110_, lean_box(0), lean_box(0), v___x_3123_, v___f_3115_);
v___f_3125_ = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3125_, 0, v_ref_3118_);
lean_closure_set(v___f_3125_, 1, v_withRef_3116_);
lean_closure_set(v___f_3125_, 2, v___x_3124_);
v___x_3126_ = lean_apply_4(v_toBind_3110_, lean_box(0), lean_box(0), v_getRef_3117_, v___f_3125_);
v___x_3127_ = lean_apply_4(v_toBind_3110_, lean_box(0), lean_box(0), v___x_3126_, v___f_3121_);
return v___x_3127_;
}
}
LEAN_EXPORT void l_Lean_withTraceNodeBefore___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_always_3097_ = stack[0].m_obj;
lean_object* v_inst_3098_ = stack[1].m_obj;
lean_object* v_inst_3099_ = stack[2].m_obj;
lean_object* v_inst_3100_ = stack[3].m_obj;
lean_object* v_inst_3101_ = stack[4].m_obj;
lean_object* v_inst_3102_ = stack[5].m_obj;
lean_object* v_cls_3103_ = stack[6].m_obj;
uint8_t v_collapsed_3104_ = stack[7].m_num;
lean_object* v_tag_3105_ = stack[8].m_obj;
lean_object* v_opts_3106_ = stack[9].m_obj;
uint8_t v_clsEnabled_3107_ = stack[10].m_num;
lean_object* v_oldTraces_3108_ = stack[11].m_obj;
lean_object* v_toPure_3109_ = stack[12].m_obj;
lean_object* v_toBind_3110_ = stack[13].m_obj;
lean_object* v_k_3111_ = stack[14].m_obj;
lean_object* v___x_3112_ = stack[15].m_obj;
lean_object* v_inst_3113_ = stack[16].m_obj;
lean_object* v_msg_3114_ = stack[17].m_obj;
lean_object* v___f_3115_ = stack[18].m_obj;
lean_object* v_withRef_3116_ = stack[19].m_obj;
lean_object* v_getRef_3117_ = stack[20].m_obj;
lean_object* v_ref_3118_ = stack[21].m_obj;
lean_object* v_res_3128_;
v_res_3128_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_always_3097_, v_inst_3098_, v_inst_3099_, v_inst_3100_, v_inst_3101_, v_inst_3102_, v_cls_3103_, v_collapsed_3104_, v_tag_3105_, v_opts_3106_, v_clsEnabled_3107_, v_oldTraces_3108_, v_toPure_3109_, v_toBind_3110_, v_k_3111_, v___x_3112_, v_inst_3113_, v_msg_3114_, v___f_3115_, v_withRef_3116_, v_getRef_3117_, v_ref_3118_);
stack->m_obj
 = v_res_3128_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_always_3129_ = _args[0];
lean_object* v_inst_3130_ = _args[1];
lean_object* v_inst_3131_ = _args[2];
lean_object* v_inst_3132_ = _args[3];
lean_object* v_inst_3133_ = _args[4];
lean_object* v_inst_3134_ = _args[5];
lean_object* v_cls_3135_ = _args[6];
lean_object* v_collapsed_3136_ = _args[7];
lean_object* v_tag_3137_ = _args[8];
lean_object* v_opts_3138_ = _args[9];
lean_object* v_clsEnabled_3139_ = _args[10];
lean_object* v_oldTraces_3140_ = _args[11];
lean_object* v_toPure_3141_ = _args[12];
lean_object* v_toBind_3142_ = _args[13];
lean_object* v_k_3143_ = _args[14];
lean_object* v___x_3144_ = _args[15];
lean_object* v_inst_3145_ = _args[16];
lean_object* v_msg_3146_ = _args[17];
lean_object* v___f_3147_ = _args[18];
lean_object* v_withRef_3148_ = _args[19];
lean_object* v_getRef_3149_ = _args[20];
lean_object* v_ref_3150_ = _args[21];
_start:
{
uint8_t v_collapsed_boxed_3151_; uint8_t v_clsEnabled_boxed_3152_; lean_object* v_res_3153_; 
v_collapsed_boxed_3151_ = lean_unbox(v_collapsed_3136_);
v_clsEnabled_boxed_3152_ = lean_unbox(v_clsEnabled_3139_);
v_res_3153_ = l_Lean_withTraceNodeBefore___redArg___lam__3(v_always_3129_, v_inst_3130_, v_inst_3131_, v_inst_3132_, v_inst_3133_, v_inst_3134_, v_cls_3135_, v_collapsed_boxed_3151_, v_tag_3137_, v_opts_3138_, v_clsEnabled_boxed_3152_, v_oldTraces_3140_, v_toPure_3141_, v_toBind_3142_, v_k_3143_, v___x_3144_, v_inst_3145_, v_msg_3146_, v___f_3147_, v_withRef_3148_, v_getRef_3149_, v_ref_3150_);
return v_res_3153_;
}
}
lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2(lean_object* v_inst_3154_, lean_object* v_always_3155_, lean_object* v_inst_3156_, lean_object* v_inst_3157_, lean_object* v_inst_3158_, lean_object* v_inst_3159_, lean_object* v_cls_3160_, uint8_t v_collapsed_3161_, lean_object* v_tag_3162_, lean_object* v_opts_3163_, uint8_t v_clsEnabled_3164_, lean_object* v_toPure_3165_, lean_object* v_toBind_3166_, lean_object* v_k_3167_, lean_object* v___x_3168_, lean_object* v_inst_3169_, lean_object* v_msg_3170_, lean_object* v___f_3171_, lean_object* v_oldTraces_3172_){
_start:
{
lean_object* v_getRef_3173_; lean_object* v_withRef_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___f_3177_; lean_object* v___x_3178_; 
v_getRef_3173_ = lean_ctor_get(v_inst_3154_, 0);
lean_inc_n(v_getRef_3173_, 2);
v_withRef_3174_ = lean_ctor_get(v_inst_3154_, 1);
lean_inc(v_withRef_3174_);
v___x_3175_ = lean_box(v_collapsed_3161_);
v___x_3176_ = lean_box(v_clsEnabled_3164_);
lean_inc(v_toBind_3166_);
v___f_3177_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__3___boxed), 22, 21);
lean_closure_set(v___f_3177_, 0, v_always_3155_);
lean_closure_set(v___f_3177_, 1, v_inst_3156_);
lean_closure_set(v___f_3177_, 2, v_inst_3157_);
lean_closure_set(v___f_3177_, 3, v_inst_3154_);
lean_closure_set(v___f_3177_, 4, v_inst_3158_);
lean_closure_set(v___f_3177_, 5, v_inst_3159_);
lean_closure_set(v___f_3177_, 6, v_cls_3160_);
lean_closure_set(v___f_3177_, 7, v___x_3175_);
lean_closure_set(v___f_3177_, 8, v_tag_3162_);
lean_closure_set(v___f_3177_, 9, v_opts_3163_);
lean_closure_set(v___f_3177_, 10, v___x_3176_);
lean_closure_set(v___f_3177_, 11, v_oldTraces_3172_);
lean_closure_set(v___f_3177_, 12, v_toPure_3165_);
lean_closure_set(v___f_3177_, 13, v_toBind_3166_);
lean_closure_set(v___f_3177_, 14, v_k_3167_);
lean_closure_set(v___f_3177_, 15, v___x_3168_);
lean_closure_set(v___f_3177_, 16, v_inst_3169_);
lean_closure_set(v___f_3177_, 17, v_msg_3170_);
lean_closure_set(v___f_3177_, 18, v___f_3171_);
lean_closure_set(v___f_3177_, 19, v_withRef_3174_);
lean_closure_set(v___f_3177_, 20, v_getRef_3173_);
v___x_3178_ = lean_apply_4(v_toBind_3166_, lean_box(0), lean_box(0), v_getRef_3173_, v___f_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT void l_Lean_withTraceNodeBefore___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3154_ = stack[0].m_obj;
lean_object* v_always_3155_ = stack[1].m_obj;
lean_object* v_inst_3156_ = stack[2].m_obj;
lean_object* v_inst_3157_ = stack[3].m_obj;
lean_object* v_inst_3158_ = stack[4].m_obj;
lean_object* v_inst_3159_ = stack[5].m_obj;
lean_object* v_cls_3160_ = stack[6].m_obj;
uint8_t v_collapsed_3161_ = stack[7].m_num;
lean_object* v_tag_3162_ = stack[8].m_obj;
lean_object* v_opts_3163_ = stack[9].m_obj;
uint8_t v_clsEnabled_3164_ = stack[10].m_num;
lean_object* v_toPure_3165_ = stack[11].m_obj;
lean_object* v_toBind_3166_ = stack[12].m_obj;
lean_object* v_k_3167_ = stack[13].m_obj;
lean_object* v___x_3168_ = stack[14].m_obj;
lean_object* v_inst_3169_ = stack[15].m_obj;
lean_object* v_msg_3170_ = stack[16].m_obj;
lean_object* v___f_3171_ = stack[17].m_obj;
lean_object* v_oldTraces_3172_ = stack[18].m_obj;
lean_object* v_res_3179_;
v_res_3179_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3154_, v_always_3155_, v_inst_3156_, v_inst_3157_, v_inst_3158_, v_inst_3159_, v_cls_3160_, v_collapsed_3161_, v_tag_3162_, v_opts_3163_, v_clsEnabled_3164_, v_toPure_3165_, v_toBind_3166_, v_k_3167_, v___x_3168_, v_inst_3169_, v_msg_3170_, v___f_3171_, v_oldTraces_3172_);
stack->m_obj
 = v_res_3179_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_inst_3180_ = _args[0];
lean_object* v_always_3181_ = _args[1];
lean_object* v_inst_3182_ = _args[2];
lean_object* v_inst_3183_ = _args[3];
lean_object* v_inst_3184_ = _args[4];
lean_object* v_inst_3185_ = _args[5];
lean_object* v_cls_3186_ = _args[6];
lean_object* v_collapsed_3187_ = _args[7];
lean_object* v_tag_3188_ = _args[8];
lean_object* v_opts_3189_ = _args[9];
lean_object* v_clsEnabled_3190_ = _args[10];
lean_object* v_toPure_3191_ = _args[11];
lean_object* v_toBind_3192_ = _args[12];
lean_object* v_k_3193_ = _args[13];
lean_object* v___x_3194_ = _args[14];
lean_object* v_inst_3195_ = _args[15];
lean_object* v_msg_3196_ = _args[16];
lean_object* v___f_3197_ = _args[17];
lean_object* v_oldTraces_3198_ = _args[18];
_start:
{
uint8_t v_collapsed_boxed_3199_; uint8_t v_clsEnabled_boxed_3200_; lean_object* v_res_3201_; 
v_collapsed_boxed_3199_ = lean_unbox(v_collapsed_3187_);
v_clsEnabled_boxed_3200_ = lean_unbox(v_clsEnabled_3190_);
v_res_3201_ = l_Lean_withTraceNodeBefore___redArg___lam__2(v_inst_3180_, v_always_3181_, v_inst_3182_, v_inst_3183_, v_inst_3184_, v_inst_3185_, v_cls_3186_, v_collapsed_boxed_3199_, v_tag_3188_, v_opts_3189_, v_clsEnabled_boxed_3200_, v_toPure_3191_, v_toBind_3192_, v_k_3193_, v___x_3194_, v_inst_3195_, v_msg_3196_, v___f_3197_, v_oldTraces_3198_);
return v_res_3201_;
}
}
lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4(lean_object* v_inst_3202_, lean_object* v_always_3203_, lean_object* v_inst_3204_, lean_object* v_inst_3205_, lean_object* v_inst_3206_, lean_object* v_inst_3207_, lean_object* v_cls_3208_, uint8_t v_collapsed_3209_, lean_object* v_tag_3210_, lean_object* v_opts_3211_, lean_object* v_toPure_3212_, lean_object* v_toBind_3213_, lean_object* v_k_3214_, lean_object* v___x_3215_, lean_object* v_inst_3216_, lean_object* v_msg_3217_, lean_object* v___f_3218_, uint8_t v_clsEnabled_3219_){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___f_3222_; 
v___x_3220_ = lean_box(v_collapsed_3209_);
v___x_3221_ = lean_box(v_clsEnabled_3219_);
lean_inc_ref(v___x_3215_);
lean_inc(v_k_3214_);
lean_inc(v_toBind_3213_);
lean_inc_ref(v_opts_3211_);
lean_inc_ref(v_inst_3205_);
lean_inc_ref(v_inst_3204_);
v___f_3222_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__2___boxed), 19, 18);
lean_closure_set(v___f_3222_, 0, v_inst_3202_);
lean_closure_set(v___f_3222_, 1, v_always_3203_);
lean_closure_set(v___f_3222_, 2, v_inst_3204_);
lean_closure_set(v___f_3222_, 3, v_inst_3205_);
lean_closure_set(v___f_3222_, 4, v_inst_3206_);
lean_closure_set(v___f_3222_, 5, v_inst_3207_);
lean_closure_set(v___f_3222_, 6, v_cls_3208_);
lean_closure_set(v___f_3222_, 7, v___x_3220_);
lean_closure_set(v___f_3222_, 8, v_tag_3210_);
lean_closure_set(v___f_3222_, 9, v_opts_3211_);
lean_closure_set(v___f_3222_, 10, v___x_3221_);
lean_closure_set(v___f_3222_, 11, v_toPure_3212_);
lean_closure_set(v___f_3222_, 12, v_toBind_3213_);
lean_closure_set(v___f_3222_, 13, v_k_3214_);
lean_closure_set(v___f_3222_, 14, v___x_3215_);
lean_closure_set(v___f_3222_, 15, v_inst_3216_);
lean_closure_set(v___f_3222_, 16, v_msg_3217_);
lean_closure_set(v___f_3222_, 17, v___f_3218_);
if (v_clsEnabled_3219_ == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3226_ = l_Lean_trace_profiler;
v___x_3227_ = l_Lean_Option_get___redArg(v___x_3215_, v_opts_3211_, v___x_3226_);
lean_dec_ref(v_opts_3211_);
v___x_3228_ = lean_unbox(v___x_3227_);
lean_dec(v___x_3227_);
if (v___x_3228_ == 0)
{
lean_dec_ref(v___f_3222_);
lean_dec(v_toBind_3213_);
lean_dec_ref(v_inst_3205_);
lean_dec_ref(v_inst_3204_);
return v_k_3214_;
}
else
{
lean_dec(v_k_3214_);
goto v___jp_3223_;
}
}
else
{
lean_dec_ref(v___x_3215_);
lean_dec(v_k_3214_);
lean_dec_ref(v_opts_3211_);
goto v___jp_3223_;
}
v___jp_3223_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3204_, v_inst_3205_);
v___x_3225_ = lean_apply_4(v_toBind_3213_, lean_box(0), lean_box(0), v___x_3224_, v___f_3222_);
return v___x_3225_;
}
}
}
LEAN_EXPORT void l_Lean_withTraceNodeBefore___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3202_ = stack[0].m_obj;
lean_object* v_always_3203_ = stack[1].m_obj;
lean_object* v_inst_3204_ = stack[2].m_obj;
lean_object* v_inst_3205_ = stack[3].m_obj;
lean_object* v_inst_3206_ = stack[4].m_obj;
lean_object* v_inst_3207_ = stack[5].m_obj;
lean_object* v_cls_3208_ = stack[6].m_obj;
uint8_t v_collapsed_3209_ = stack[7].m_num;
lean_object* v_tag_3210_ = stack[8].m_obj;
lean_object* v_opts_3211_ = stack[9].m_obj;
lean_object* v_toPure_3212_ = stack[10].m_obj;
lean_object* v_toBind_3213_ = stack[11].m_obj;
lean_object* v_k_3214_ = stack[12].m_obj;
lean_object* v___x_3215_ = stack[13].m_obj;
lean_object* v_inst_3216_ = stack[14].m_obj;
lean_object* v_msg_3217_ = stack[15].m_obj;
lean_object* v___f_3218_ = stack[16].m_obj;
uint8_t v_clsEnabled_3219_ = stack[17].m_num;
lean_object* v_res_3229_;
v_res_3229_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3202_, v_always_3203_, v_inst_3204_, v_inst_3205_, v_inst_3206_, v_inst_3207_, v_cls_3208_, v_collapsed_3209_, v_tag_3210_, v_opts_3211_, v_toPure_3212_, v_toBind_3213_, v_k_3214_, v___x_3215_, v_inst_3216_, v_msg_3217_, v___f_3218_, v_clsEnabled_3219_);
stack->m_obj
 = v_res_3229_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_inst_3230_ = _args[0];
lean_object* v_always_3231_ = _args[1];
lean_object* v_inst_3232_ = _args[2];
lean_object* v_inst_3233_ = _args[3];
lean_object* v_inst_3234_ = _args[4];
lean_object* v_inst_3235_ = _args[5];
lean_object* v_cls_3236_ = _args[6];
lean_object* v_collapsed_3237_ = _args[7];
lean_object* v_tag_3238_ = _args[8];
lean_object* v_opts_3239_ = _args[9];
lean_object* v_toPure_3240_ = _args[10];
lean_object* v_toBind_3241_ = _args[11];
lean_object* v_k_3242_ = _args[12];
lean_object* v___x_3243_ = _args[13];
lean_object* v_inst_3244_ = _args[14];
lean_object* v_msg_3245_ = _args[15];
lean_object* v___f_3246_ = _args[16];
lean_object* v_clsEnabled_3247_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3248_; uint8_t v_clsEnabled_boxed_3249_; lean_object* v_res_3250_; 
v_collapsed_boxed_3248_ = lean_unbox(v_collapsed_3237_);
v_clsEnabled_boxed_3249_ = lean_unbox(v_clsEnabled_3247_);
v_res_3250_ = l_Lean_withTraceNodeBefore___redArg___lam__4(v_inst_3230_, v_always_3231_, v_inst_3232_, v_inst_3233_, v_inst_3234_, v_inst_3235_, v_cls_3236_, v_collapsed_boxed_3248_, v_tag_3238_, v_opts_3239_, v_toPure_3240_, v_toBind_3241_, v_k_3242_, v___x_3243_, v_inst_3244_, v_msg_3245_, v___f_3246_, v_clsEnabled_boxed_3249_);
return v_res_3250_;
}
}
lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7(lean_object* v_k_3251_, lean_object* v_inst_3252_, lean_object* v_toApplicative_3253_, lean_object* v_inst_3254_, lean_object* v_always_3255_, lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_inst_3258_, lean_object* v_cls_3259_, uint8_t v_collapsed_3260_, lean_object* v_tag_3261_, lean_object* v_toBind_3262_, lean_object* v___x_3263_, lean_object* v_inst_3264_, lean_object* v_msg_3265_, lean_object* v___f_3266_, lean_object* v_getOptionsUnrestricted_3267_, lean_object* v_opts_3268_){
_start:
{
uint8_t v_hasTrace_3269_; 
v_hasTrace_3269_ = lean_ctor_get_uint8(v_opts_3268_, sizeof(void*)*1);
if (v_hasTrace_3269_ == 0)
{
lean_dec_ref(v_opts_3268_);
lean_dec(v_getOptionsUnrestricted_3267_);
lean_dec(v___f_3266_);
lean_dec(v_msg_3265_);
lean_dec(v_inst_3264_);
lean_dec_ref(v___x_3263_);
lean_dec(v_toBind_3262_);
lean_dec_ref(v_tag_3261_);
lean_dec(v_cls_3259_);
lean_dec_ref(v_inst_3258_);
lean_dec(v_inst_3257_);
lean_dec_ref(v_inst_3256_);
lean_dec_ref(v_always_3255_);
lean_dec_ref(v_inst_3254_);
lean_dec_ref(v_toApplicative_3253_);
lean_dec_ref(v_inst_3252_);
return v_k_3251_;
}
else
{
lean_object* v_getInheritedTraceOptions_3270_; lean_object* v_toPure_3271_; lean_object* v___x_3272_; lean_object* v___f_3273_; lean_object* v___f_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_getInheritedTraceOptions_3270_ = lean_ctor_get(v_inst_3252_, 2);
lean_inc(v_getInheritedTraceOptions_3270_);
v_toPure_3271_ = lean_ctor_get(v_toApplicative_3253_, 1);
lean_inc_n(v_toPure_3271_, 2);
lean_dec_ref(v_toApplicative_3253_);
v___x_3272_ = lean_box(v_collapsed_3260_);
lean_inc_n(v_toBind_3262_, 3);
lean_inc(v_cls_3259_);
v___f_3273_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__4___boxed), 18, 17);
lean_closure_set(v___f_3273_, 0, v_inst_3254_);
lean_closure_set(v___f_3273_, 1, v_always_3255_);
lean_closure_set(v___f_3273_, 2, v_inst_3256_);
lean_closure_set(v___f_3273_, 3, v_inst_3252_);
lean_closure_set(v___f_3273_, 4, v_inst_3257_);
lean_closure_set(v___f_3273_, 5, v_inst_3258_);
lean_closure_set(v___f_3273_, 6, v_cls_3259_);
lean_closure_set(v___f_3273_, 7, v___x_3272_);
lean_closure_set(v___f_3273_, 8, v_tag_3261_);
lean_closure_set(v___f_3273_, 9, v_opts_3268_);
lean_closure_set(v___f_3273_, 10, v_toPure_3271_);
lean_closure_set(v___f_3273_, 11, v_toBind_3262_);
lean_closure_set(v___f_3273_, 12, v_k_3251_);
lean_closure_set(v___f_3273_, 13, v___x_3263_);
lean_closure_set(v___f_3273_, 14, v_inst_3264_);
lean_closure_set(v___f_3273_, 15, v_msg_3265_);
lean_closure_set(v___f_3273_, 16, v___f_3266_);
v___f_3274_ = lean_alloc_closure((void*)(l_Lean_withTraceNode___redArg___lam__12), 5, 4);
lean_closure_set(v___f_3274_, 0, v_toPure_3271_);
lean_closure_set(v___f_3274_, 1, v_cls_3259_);
lean_closure_set(v___f_3274_, 2, v_toBind_3262_);
lean_closure_set(v___f_3274_, 3, v_getOptionsUnrestricted_3267_);
v___x_3275_ = lean_apply_4(v_toBind_3262_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3270_, v___f_3274_);
v___x_3276_ = lean_apply_4(v_toBind_3262_, lean_box(0), lean_box(0), v___x_3275_, v___f_3273_);
return v___x_3276_;
}
}
}
LEAN_EXPORT void l_Lean_withTraceNodeBefore___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3251_ = stack[0].m_obj;
lean_object* v_inst_3252_ = stack[1].m_obj;
lean_object* v_toApplicative_3253_ = stack[2].m_obj;
lean_object* v_inst_3254_ = stack[3].m_obj;
lean_object* v_always_3255_ = stack[4].m_obj;
lean_object* v_inst_3256_ = stack[5].m_obj;
lean_object* v_inst_3257_ = stack[6].m_obj;
lean_object* v_inst_3258_ = stack[7].m_obj;
lean_object* v_cls_3259_ = stack[8].m_obj;
uint8_t v_collapsed_3260_ = stack[9].m_num;
lean_object* v_tag_3261_ = stack[10].m_obj;
lean_object* v_toBind_3262_ = stack[11].m_obj;
lean_object* v___x_3263_ = stack[12].m_obj;
lean_object* v_inst_3264_ = stack[13].m_obj;
lean_object* v_msg_3265_ = stack[14].m_obj;
lean_object* v___f_3266_ = stack[15].m_obj;
lean_object* v_getOptionsUnrestricted_3267_ = stack[16].m_obj;
lean_object* v_opts_3268_ = stack[17].m_obj;
lean_object* v_res_3277_;
v_res_3277_ = l_Lean_withTraceNodeBefore___redArg___lam__7(v_k_3251_, v_inst_3252_, v_toApplicative_3253_, v_inst_3254_, v_always_3255_, v_inst_3256_, v_inst_3257_, v_inst_3258_, v_cls_3259_, v_collapsed_3260_, v_tag_3261_, v_toBind_3262_, v___x_3263_, v_inst_3264_, v_msg_3265_, v___f_3266_, v_getOptionsUnrestricted_3267_, v_opts_3268_);
stack->m_obj
 = v_res_3277_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_k_3278_ = _args[0];
lean_object* v_inst_3279_ = _args[1];
lean_object* v_toApplicative_3280_ = _args[2];
lean_object* v_inst_3281_ = _args[3];
lean_object* v_always_3282_ = _args[4];
lean_object* v_inst_3283_ = _args[5];
lean_object* v_inst_3284_ = _args[6];
lean_object* v_inst_3285_ = _args[7];
lean_object* v_cls_3286_ = _args[8];
lean_object* v_collapsed_3287_ = _args[9];
lean_object* v_tag_3288_ = _args[10];
lean_object* v_toBind_3289_ = _args[11];
lean_object* v___x_3290_ = _args[12];
lean_object* v_inst_3291_ = _args[13];
lean_object* v_msg_3292_ = _args[14];
lean_object* v___f_3293_ = _args[15];
lean_object* v_getOptionsUnrestricted_3294_ = _args[16];
lean_object* v_opts_3295_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3296_; lean_object* v_res_3297_; 
v_collapsed_boxed_3296_ = lean_unbox(v_collapsed_3287_);
v_res_3297_ = l_Lean_withTraceNodeBefore___redArg___lam__7(v_k_3278_, v_inst_3279_, v_toApplicative_3280_, v_inst_3281_, v_always_3282_, v_inst_3283_, v_inst_3284_, v_inst_3285_, v_cls_3286_, v_collapsed_boxed_3296_, v_tag_3288_, v_toBind_3289_, v___x_3290_, v_inst_3291_, v_msg_3292_, v___f_3293_, v_getOptionsUnrestricted_3294_, v_opts_3295_);
return v_res_3297_;
}
}
lean_object* l_Lean_withTraceNodeBefore___redArg(lean_object* v_inst_3298_, lean_object* v_inst_3299_, lean_object* v_inst_3300_, lean_object* v_inst_3301_, lean_object* v_inst_3302_, lean_object* v_always_3303_, lean_object* v_inst_3304_, lean_object* v_inst_3305_, lean_object* v_cls_3306_, lean_object* v_msg_3307_, lean_object* v_k_3308_, uint8_t v_collapsed_3309_, lean_object* v_tag_3310_){
_start:
{
lean_object* v___x_3311_; lean_object* v_toApplicative_3312_; lean_object* v_toBind_3313_; lean_object* v_getOptionsUnrestricted_3314_; lean_object* v___f_3315_; lean_object* v___x_3316_; lean_object* v___f_3317_; lean_object* v___x_3318_; 
v___x_3311_ = l_Lean_KVMap_instValueBool;
v_toApplicative_3312_ = lean_ctor_get(v_inst_3298_, 0);
lean_inc_ref(v_toApplicative_3312_);
v_toBind_3313_ = lean_ctor_get(v_inst_3298_, 1);
lean_inc_n(v_toBind_3313_, 2);
v_getOptionsUnrestricted_3314_ = lean_ctor_get(v_inst_3302_, 1);
lean_inc_n(v_getOptionsUnrestricted_3314_, 2);
lean_dec_ref(v_inst_3302_);
lean_inc(v_inst_3301_);
v___f_3315_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3315_, 0, v_inst_3301_);
v___x_3316_ = lean_box(v_collapsed_3309_);
v___f_3317_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 18, 17);
lean_closure_set(v___f_3317_, 0, v_k_3308_);
lean_closure_set(v___f_3317_, 1, v_inst_3299_);
lean_closure_set(v___f_3317_, 2, v_toApplicative_3312_);
lean_closure_set(v___f_3317_, 3, v_inst_3300_);
lean_closure_set(v___f_3317_, 4, v_always_3303_);
lean_closure_set(v___f_3317_, 5, v_inst_3298_);
lean_closure_set(v___f_3317_, 6, v_inst_3301_);
lean_closure_set(v___f_3317_, 7, v_inst_3305_);
lean_closure_set(v___f_3317_, 8, v_cls_3306_);
lean_closure_set(v___f_3317_, 9, v___x_3316_);
lean_closure_set(v___f_3317_, 10, v_tag_3310_);
lean_closure_set(v___f_3317_, 11, v_toBind_3313_);
lean_closure_set(v___f_3317_, 12, v___x_3311_);
lean_closure_set(v___f_3317_, 13, v_inst_3304_);
lean_closure_set(v___f_3317_, 14, v_msg_3307_);
lean_closure_set(v___f_3317_, 15, v___f_3315_);
lean_closure_set(v___f_3317_, 16, v_getOptionsUnrestricted_3314_);
v___x_3318_ = lean_apply_4(v_toBind_3313_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3314_, v___f_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT void l_Lean_withTraceNodeBefore___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3298_ = stack[0].m_obj;
lean_object* v_inst_3299_ = stack[1].m_obj;
lean_object* v_inst_3300_ = stack[2].m_obj;
lean_object* v_inst_3301_ = stack[3].m_obj;
lean_object* v_inst_3302_ = stack[4].m_obj;
lean_object* v_always_3303_ = stack[5].m_obj;
lean_object* v_inst_3304_ = stack[6].m_obj;
lean_object* v_inst_3305_ = stack[7].m_obj;
lean_object* v_cls_3306_ = stack[8].m_obj;
lean_object* v_msg_3307_ = stack[9].m_obj;
lean_object* v_k_3308_ = stack[10].m_obj;
uint8_t v_collapsed_3309_ = stack[11].m_num;
lean_object* v_tag_3310_ = stack[12].m_obj;
lean_object* v_res_3319_;
v_res_3319_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3298_, v_inst_3299_, v_inst_3300_, v_inst_3301_, v_inst_3302_, v_always_3303_, v_inst_3304_, v_inst_3305_, v_cls_3306_, v_msg_3307_, v_k_3308_, v_collapsed_3309_, v_tag_3310_);
stack->m_obj
 = v_res_3319_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___redArg___boxed(lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_inst_3322_, lean_object* v_inst_3323_, lean_object* v_inst_3324_, lean_object* v_always_3325_, lean_object* v_inst_3326_, lean_object* v_inst_3327_, lean_object* v_cls_3328_, lean_object* v_msg_3329_, lean_object* v_k_3330_, lean_object* v_collapsed_3331_, lean_object* v_tag_3332_){
_start:
{
uint8_t v_collapsed_boxed_3333_; lean_object* v_res_3334_; 
v_collapsed_boxed_3333_ = lean_unbox(v_collapsed_3331_);
v_res_3334_ = l_Lean_withTraceNodeBefore___redArg(v_inst_3320_, v_inst_3321_, v_inst_3322_, v_inst_3323_, v_inst_3324_, v_always_3325_, v_inst_3326_, v_inst_3327_, v_cls_3328_, v_msg_3329_, v_k_3330_, v_collapsed_boxed_3333_, v_tag_3332_);
return v_res_3334_;
}
}
lean_object* l_Lean_withTraceNodeBefore(lean_object* v_00_u03b1_3335_, lean_object* v_m_3336_, lean_object* v_inst_3337_, lean_object* v_inst_3338_, lean_object* v_00_u03b5_3339_, lean_object* v_inst_3340_, lean_object* v_inst_3341_, lean_object* v_inst_3342_, lean_object* v_always_3343_, lean_object* v_inst_3344_, lean_object* v_inst_3345_, lean_object* v_cls_3346_, lean_object* v_msg_3347_, lean_object* v_k_3348_, uint8_t v_collapsed_3349_, lean_object* v_tag_3350_){
_start:
{
lean_object* v___x_3351_; lean_object* v_toApplicative_3352_; lean_object* v_toBind_3353_; lean_object* v_getOptionsUnrestricted_3354_; lean_object* v___f_3355_; lean_object* v___x_3356_; lean_object* v___f_3357_; lean_object* v___x_3358_; 
v___x_3351_ = l_Lean_KVMap_instValueBool;
v_toApplicative_3352_ = lean_ctor_get(v_inst_3337_, 0);
lean_inc_ref(v_toApplicative_3352_);
v_toBind_3353_ = lean_ctor_get(v_inst_3337_, 1);
lean_inc_n(v_toBind_3353_, 2);
v_getOptionsUnrestricted_3354_ = lean_ctor_get(v_inst_3342_, 1);
lean_inc_n(v_getOptionsUnrestricted_3354_, 2);
lean_dec_ref(v_inst_3342_);
lean_inc(v_inst_3341_);
v___f_3355_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3355_, 0, v_inst_3341_);
v___x_3356_ = lean_box(v_collapsed_3349_);
v___f_3357_ = lean_alloc_closure((void*)(l_Lean_withTraceNodeBefore___redArg___lam__7___boxed), 18, 17);
lean_closure_set(v___f_3357_, 0, v_k_3348_);
lean_closure_set(v___f_3357_, 1, v_inst_3338_);
lean_closure_set(v___f_3357_, 2, v_toApplicative_3352_);
lean_closure_set(v___f_3357_, 3, v_inst_3340_);
lean_closure_set(v___f_3357_, 4, v_always_3343_);
lean_closure_set(v___f_3357_, 5, v_inst_3337_);
lean_closure_set(v___f_3357_, 6, v_inst_3341_);
lean_closure_set(v___f_3357_, 7, v_inst_3345_);
lean_closure_set(v___f_3357_, 8, v_cls_3346_);
lean_closure_set(v___f_3357_, 9, v___x_3356_);
lean_closure_set(v___f_3357_, 10, v_tag_3350_);
lean_closure_set(v___f_3357_, 11, v_toBind_3353_);
lean_closure_set(v___f_3357_, 12, v___x_3351_);
lean_closure_set(v___f_3357_, 13, v_inst_3344_);
lean_closure_set(v___f_3357_, 14, v_msg_3347_);
lean_closure_set(v___f_3357_, 15, v___f_3355_);
lean_closure_set(v___f_3357_, 16, v_getOptionsUnrestricted_3354_);
v___x_3358_ = lean_apply_4(v_toBind_3353_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3354_, v___f_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT void l_Lean_withTraceNodeBefore_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3337_ = stack[2].m_obj;
lean_object* v_inst_3338_ = stack[3].m_obj;
lean_object* v_inst_3340_ = stack[5].m_obj;
lean_object* v_inst_3341_ = stack[6].m_obj;
lean_object* v_inst_3342_ = stack[7].m_obj;
lean_object* v_always_3343_ = stack[8].m_obj;
lean_object* v_inst_3344_ = stack[9].m_obj;
lean_object* v_inst_3345_ = stack[10].m_obj;
lean_object* v_cls_3346_ = stack[11].m_obj;
lean_object* v_msg_3347_ = stack[12].m_obj;
lean_object* v_k_3348_ = stack[13].m_obj;
uint8_t v_collapsed_3349_ = stack[14].m_num;
lean_object* v_tag_3350_ = stack[15].m_obj;
lean_object* v_res_3359_;
v_res_3359_ = l_Lean_withTraceNodeBefore(lean_box(0), lean_box(0), v_inst_3337_, v_inst_3338_, lean_box(0), v_inst_3340_, v_inst_3341_, v_inst_3342_, v_always_3343_, v_inst_3344_, v_inst_3345_, v_cls_3346_, v_msg_3347_, v_k_3348_, v_collapsed_3349_, v_tag_3350_);
stack->m_obj
 = v_res_3359_;
}
LEAN_EXPORT lean_object* l_Lean_withTraceNodeBefore___boxed(lean_object* v_00_u03b1_3360_, lean_object* v_m_3361_, lean_object* v_inst_3362_, lean_object* v_inst_3363_, lean_object* v_00_u03b5_3364_, lean_object* v_inst_3365_, lean_object* v_inst_3366_, lean_object* v_inst_3367_, lean_object* v_always_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_cls_3371_, lean_object* v_msg_3372_, lean_object* v_k_3373_, lean_object* v_collapsed_3374_, lean_object* v_tag_3375_){
_start:
{
uint8_t v_collapsed_boxed_3376_; lean_object* v_res_3377_; 
v_collapsed_boxed_3376_ = lean_unbox(v_collapsed_3374_);
v_res_3377_ = l_Lean_withTraceNodeBefore(v_00_u03b1_3360_, v_m_3361_, v_inst_3362_, v_inst_3363_, v_00_u03b5_3364_, v_inst_3365_, v_inst_3366_, v_inst_3367_, v_always_3368_, v_inst_3369_, v_inst_3370_, v_cls_3371_, v_msg_3372_, v_k_3373_, v_collapsed_boxed_3376_, v_tag_3375_);
return v_res_3377_;
}
}
uint8_t l_Lean_addTraceAsMessages___redArg___lam__0(lean_object* v_x_3378_, lean_object* v_x_3379_){
_start:
{
lean_object* v_fst_3380_; lean_object* v_fst_3381_; lean_object* v_fst_3382_; lean_object* v_fst_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_fst_3380_ = lean_ctor_get(v_x_3378_, 0);
v_fst_3381_ = lean_ctor_get(v_x_3379_, 0);
v_fst_3382_ = lean_ctor_get(v_fst_3380_, 0);
v_fst_3383_ = lean_ctor_get(v_fst_3381_, 0);
v___x_3384_ = lean_unsigned_to_nat(1u);
v___x_3385_ = lean_nat_add(v_fst_3382_, v___x_3384_);
v___x_3386_ = lean_nat_dec_le(v___x_3385_, v_fst_3383_);
lean_dec(v___x_3385_);
return v___x_3386_;
}
}
LEAN_EXPORT void l_Lean_addTraceAsMessages___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3378_ = stack[0].m_obj;
lean_object* v_x_3379_ = stack[1].m_obj;
uint8_t v_res_3387_;
v_res_3387_ = l_Lean_addTraceAsMessages___redArg___lam__0(v_x_3378_, v_x_3379_);
stack->m_num = v_res_3387_;
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__0___boxed(lean_object* v_x_3388_, lean_object* v_x_3389_){
_start:
{
uint8_t v_res_3390_; lean_object* v_r_3391_; 
v_res_3390_ = l_Lean_addTraceAsMessages___redArg___lam__0(v_x_3388_, v_x_3389_);
lean_dec_ref(v_x_3389_);
lean_dec_ref(v_x_3388_);
v_r_3391_ = lean_box(v_res_3390_);
return v_r_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__1(lean_object* v_x1_3392_, lean_object* v_x2_3393_, lean_object* v_x3_3394_){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3395_, 0, v_x2_3393_);
lean_ctor_set(v___x_3395_, 1, v_x3_3394_);
v___x_3396_ = lean_array_push(v_x1_3392_, v___x_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4(lean_object* v_____do__lift_3397_, lean_object* v___x_3398_, lean_object* v_fst_3399_, lean_object* v_snd_3400_, lean_object* v_logMessage_3401_, lean_object* v_toBind_3402_, lean_object* v___f_3403_, lean_object* v_____do__lift_3404_){
_start:
{
uint8_t v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3405_ = 0;
v___x_3406_ = l_Lean_Elab_mkMessageCore(v_____do__lift_3397_, v_____do__lift_3404_, v___x_3398_, v___x_3405_, v_fst_3399_, v_snd_3400_);
v___x_3407_ = lean_apply_1(v_logMessage_3401_, v___x_3406_);
v___x_3408_ = lean_apply_4(v_toBind_3402_, lean_box(0), lean_box(0), v___x_3407_, v___f_3403_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__4___boxed(lean_object* v_____do__lift_3409_, lean_object* v___x_3410_, lean_object* v_fst_3411_, lean_object* v_snd_3412_, lean_object* v_logMessage_3413_, lean_object* v_toBind_3414_, lean_object* v___f_3415_, lean_object* v_____do__lift_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_addTraceAsMessages___redArg___lam__4(v_____do__lift_3409_, v___x_3410_, v_fst_3411_, v_snd_3412_, v_logMessage_3413_, v_toBind_3414_, v___f_3415_, v_____do__lift_3416_);
lean_dec(v_snd_3412_);
lean_dec(v_fst_3411_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__2(lean_object* v___x_3418_, lean_object* v_fst_3419_, lean_object* v_snd_3420_, lean_object* v_logMessage_3421_, lean_object* v_toBind_3422_, lean_object* v___f_3423_, lean_object* v_toMonadFileMap_3424_, lean_object* v_____do__lift_3425_){
_start:
{
lean_object* v___f_3426_; lean_object* v___x_3427_; 
lean_inc(v_toBind_3422_);
v___f_3426_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_3426_, 0, v_____do__lift_3425_);
lean_closure_set(v___f_3426_, 1, v___x_3418_);
lean_closure_set(v___f_3426_, 2, v_fst_3419_);
lean_closure_set(v___f_3426_, 3, v_snd_3420_);
lean_closure_set(v___f_3426_, 4, v_logMessage_3421_);
lean_closure_set(v___f_3426_, 5, v_toBind_3422_);
lean_closure_set(v___f_3426_, 6, v___f_3423_);
v___x_3427_ = lean_apply_4(v_toBind_3422_, lean_box(0), lean_box(0), v_toMonadFileMap_3424_, v___f_3426_);
return v___x_3427_;
}
}
lean_object* l_Lean_addTraceAsMessages___redArg___lam__3(lean_object* v___x_3428_, uint8_t v___x_3429_, lean_object* v_logMessage_3430_, lean_object* v_toBind_3431_, lean_object* v___f_3432_, lean_object* v_toMonadFileMap_3433_, lean_object* v_getFileName_3434_, lean_object* v_a_3435_, lean_object* v_x_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_fst_3438_; lean_object* v_snd_3439_; lean_object* v_fst_3440_; lean_object* v_snd_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3458_; 
v_fst_3438_ = lean_ctor_get(v_a_3435_, 0);
lean_inc(v_fst_3438_);
v_snd_3439_ = lean_ctor_get(v_a_3435_, 1);
lean_inc(v_snd_3439_);
lean_dec_ref(v_a_3435_);
v_fst_3440_ = lean_ctor_get(v_fst_3438_, 0);
v_snd_3441_ = lean_ctor_get(v_fst_3438_, 1);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_fst_3438_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3443_ = v_fst_3438_;
v_isShared_3444_ = v_isSharedCheck_3458_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_snd_3441_);
lean_inc(v_fst_3440_);
lean_dec(v_fst_3438_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3458_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; double v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3445_ = ((lean_object*)(l_Lean_checkTraceOption___closed__1));
v___x_3446_ = lean_box(0);
v___x_3447_ = lean_box(0);
v___x_3448_ = lean_float_of_nat(v___x_3428_);
v___x_3449_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__1));
v___x_3450_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3450_, 0, v___x_3446_);
lean_ctor_set(v___x_3450_, 1, v___x_3447_);
lean_ctor_set(v___x_3450_, 2, v___x_3449_);
lean_ctor_set_float(v___x_3450_, sizeof(void*)*3, v___x_3448_);
lean_ctor_set_float(v___x_3450_, sizeof(void*)*3 + 8, v___x_3448_);
lean_ctor_set_uint8(v___x_3450_, sizeof(void*)*3 + 16, v___x_3429_);
v___x_3451_ = l_Lean_MessageData_nil;
v___x_3452_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
lean_ctor_set(v___x_3452_, 2, v_snd_3439_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set_tag(v___x_3443_, 8);
lean_ctor_set(v___x_3443_, 1, v___x_3452_);
lean_ctor_set(v___x_3443_, 0, v___x_3445_);
v___x_3454_ = v___x_3443_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___f_3455_; lean_object* v___x_3456_; 
lean_inc(v_toBind_3431_);
v___f_3455_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__2), 8, 7);
lean_closure_set(v___f_3455_, 0, v___x_3454_);
lean_closure_set(v___f_3455_, 1, v_fst_3440_);
lean_closure_set(v___f_3455_, 2, v_snd_3441_);
lean_closure_set(v___f_3455_, 3, v_logMessage_3430_);
lean_closure_set(v___f_3455_, 4, v_toBind_3431_);
lean_closure_set(v___f_3455_, 5, v___f_3432_);
lean_closure_set(v___f_3455_, 6, v_toMonadFileMap_3433_);
v___x_3456_ = lean_apply_4(v_toBind_3431_, lean_box(0), lean_box(0), v_getFileName_3434_, v___f_3455_);
return v___x_3456_;
}
}
}
}
LEAN_EXPORT void l_Lean_addTraceAsMessages___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3428_ = stack[0].m_obj;
uint8_t v___x_3429_ = stack[1].m_num;
lean_object* v_logMessage_3430_ = stack[2].m_obj;
lean_object* v_toBind_3431_ = stack[3].m_obj;
lean_object* v___f_3432_ = stack[4].m_obj;
lean_object* v_toMonadFileMap_3433_ = stack[5].m_obj;
lean_object* v_getFileName_3434_ = stack[6].m_obj;
lean_object* v_a_3435_ = stack[7].m_obj;
lean_object* v___y_3437_ = stack[9].m_obj;
lean_object* v_res_3459_;
v_res_3459_ = l_Lean_addTraceAsMessages___redArg___lam__3(v___x_3428_, v___x_3429_, v_logMessage_3430_, v_toBind_3431_, v___f_3432_, v_toMonadFileMap_3433_, v_getFileName_3434_, v_a_3435_, lean_box(0), v___y_3437_);
stack->m_obj
 = v_res_3459_;
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__3___boxed(lean_object* v___x_3460_, lean_object* v___x_3461_, lean_object* v_logMessage_3462_, lean_object* v_toBind_3463_, lean_object* v___f_3464_, lean_object* v_toMonadFileMap_3465_, lean_object* v_getFileName_3466_, lean_object* v_a_3467_, lean_object* v_x_3468_, lean_object* v___y_3469_){
_start:
{
uint8_t v___x_943__boxed_3470_; lean_object* v_res_3471_; 
v___x_943__boxed_3470_ = lean_unbox(v___x_3461_);
v_res_3471_ = l_Lean_addTraceAsMessages___redArg___lam__3(v___x_3460_, v___x_943__boxed_3470_, v_logMessage_3462_, v_toBind_3463_, v___f_3464_, v_toMonadFileMap_3465_, v_getFileName_3466_, v_a_3467_, v_x_3468_, v___y_3469_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__5(lean_object* v___x_3472_, lean_object* v___f_3473_, lean_object* v_acc_3474_, lean_object* v_l_3475_){
_start:
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_3472_, v___f_3473_, v_acc_3474_, v_l_3475_);
return v___x_3476_;
}
}
lean_object* l_Lean_addTraceAsMessages___redArg___lam__6(lean_object* v_toPure_3477_, uint8_t v___x_3478_, lean_object* v_logMessage_3479_, lean_object* v_toBind_3480_, lean_object* v_toMonadFileMap_3481_, lean_object* v_getFileName_3482_, lean_object* v_inst_3483_, lean_object* v___f_3484_, lean_object* v___f_3485_, lean_object* v___f_3486_, lean_object* v_____s_3487_){
_start:
{
lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3514_; lean_object* v_size_3521_; lean_object* v_buckets_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
v_size_3521_ = lean_ctor_get(v_____s_3487_, 0);
lean_inc(v_size_3521_);
v_buckets_3522_ = lean_ctor_get(v_____s_3487_, 1);
lean_inc_ref(v_buckets_3522_);
lean_dec_ref(v_____s_3487_);
v___x_3523_ = lean_mk_empty_array_with_capacity(v_size_3521_);
lean_dec(v_size_3521_);
v___x_3524_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_addTraceNode___redArg___lam__3___closed__9));
v___x_3525_ = lean_unsigned_to_nat(0u);
v___x_3526_ = lean_array_get_size(v_buckets_3522_);
v___x_3527_ = lean_nat_dec_lt(v___x_3525_, v___x_3526_);
if (v___x_3527_ == 0)
{
lean_dec_ref(v_buckets_3522_);
lean_dec_ref(v___f_3486_);
v___y_3514_ = v___x_3523_;
goto v___jp_3513_;
}
else
{
lean_object* v___f_3528_; size_t v___x_3529_; size_t v___x_3530_; lean_object* v___x_3531_; 
v___f_3528_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__5), 4, 2);
lean_closure_set(v___f_3528_, 0, v___x_3524_);
lean_closure_set(v___f_3528_, 1, v___f_3486_);
v___x_3529_ = ((size_t)0ULL);
v___x_3530_ = lean_usize_of_nat(v___x_3526_);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3524_, v___f_3528_, v_buckets_3522_, v___x_3529_, v___x_3530_, v___x_3523_);
v___y_3514_ = v___x_3531_;
goto v___jp_3513_;
}
v___jp_3488_:
{
lean_object* v___x_3491_; lean_object* v___f_3492_; lean_object* v___x_3493_; lean_object* v___f_3494_; size_t v_sz_3495_; size_t v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3491_ = lean_box(0);
v___f_3492_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3492_, 0, v___x_3491_);
lean_closure_set(v___f_3492_, 1, v_toPure_3477_);
v___x_3493_ = lean_box(v___x_3478_);
lean_inc(v_toBind_3480_);
v___f_3494_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__3___boxed), 10, 7);
lean_closure_set(v___f_3494_, 0, v___y_3489_);
lean_closure_set(v___f_3494_, 1, v___x_3493_);
lean_closure_set(v___f_3494_, 2, v_logMessage_3479_);
lean_closure_set(v___f_3494_, 3, v_toBind_3480_);
lean_closure_set(v___f_3494_, 4, v___f_3492_);
lean_closure_set(v___f_3494_, 5, v_toMonadFileMap_3481_);
lean_closure_set(v___f_3494_, 6, v_getFileName_3482_);
v_sz_3495_ = lean_array_size(v___y_3490_);
v___x_3496_ = ((size_t)0ULL);
v___x_3497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3483_, v___y_3490_, v___f_3494_, v_sz_3495_, v___x_3496_, v___x_3491_);
v___x_3498_ = lean_apply_4(v_toBind_3480_, lean_box(0), lean_box(0), v___x_3497_, v___f_3484_);
return v___x_3498_;
}
v___jp_3499_:
{
lean_object* v___x_3505_; 
v___x_3505_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_3485_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_3504_);
lean_dec(v___y_3501_);
v___y_3489_ = v___y_3500_;
v___y_3490_ = v___x_3505_;
goto v___jp_3488_;
}
v___jp_3506_:
{
uint8_t v___x_3512_; 
v___x_3512_ = lean_nat_dec_le(v___y_3511_, v___y_3510_);
if (v___x_3512_ == 0)
{
lean_dec(v___y_3510_);
lean_inc(v___y_3511_);
v___y_3500_ = v___y_3507_;
v___y_3501_ = v___y_3508_;
v___y_3502_ = v___y_3509_;
v___y_3503_ = v___y_3511_;
v___y_3504_ = v___y_3511_;
goto v___jp_3499_;
}
else
{
v___y_3500_ = v___y_3507_;
v___y_3501_ = v___y_3508_;
v___y_3502_ = v___y_3509_;
v___y_3503_ = v___y_3511_;
v___y_3504_ = v___y_3510_;
goto v___jp_3499_;
}
}
v___jp_3513_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v___x_3515_ = lean_unsigned_to_nat(0u);
v___x_3516_ = lean_array_get_size(v___y_3514_);
v___x_3517_ = lean_nat_dec_eq(v___x_3516_, v___x_3515_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v___x_3518_ = lean_unsigned_to_nat(1u);
v___x_3519_ = lean_nat_sub(v___x_3516_, v___x_3518_);
v___x_3520_ = lean_nat_dec_le(v___x_3515_, v___x_3519_);
if (v___x_3520_ == 0)
{
lean_inc(v___x_3519_);
v___y_3507_ = v___x_3515_;
v___y_3508_ = v___x_3516_;
v___y_3509_ = v___y_3514_;
v___y_3510_ = v___x_3519_;
v___y_3511_ = v___x_3519_;
goto v___jp_3506_;
}
else
{
v___y_3507_ = v___x_3515_;
v___y_3508_ = v___x_3516_;
v___y_3509_ = v___y_3514_;
v___y_3510_ = v___x_3519_;
v___y_3511_ = v___x_3515_;
goto v___jp_3506_;
}
}
else
{
lean_dec_ref(v___f_3485_);
v___y_3489_ = v___x_3515_;
v___y_3490_ = v___y_3514_;
goto v___jp_3488_;
}
}
}
}
LEAN_EXPORT void l_Lean_addTraceAsMessages___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3477_ = stack[0].m_obj;
uint8_t v___x_3478_ = stack[1].m_num;
lean_object* v_logMessage_3479_ = stack[2].m_obj;
lean_object* v_toBind_3480_ = stack[3].m_obj;
lean_object* v_toMonadFileMap_3481_ = stack[4].m_obj;
lean_object* v_getFileName_3482_ = stack[5].m_obj;
lean_object* v_inst_3483_ = stack[6].m_obj;
lean_object* v___f_3484_ = stack[7].m_obj;
lean_object* v___f_3485_ = stack[8].m_obj;
lean_object* v___f_3486_ = stack[9].m_obj;
lean_object* v_____s_3487_ = stack[10].m_obj;
lean_object* v_res_3532_;
v_res_3532_ = l_Lean_addTraceAsMessages___redArg___lam__6(v_toPure_3477_, v___x_3478_, v_logMessage_3479_, v_toBind_3480_, v_toMonadFileMap_3481_, v_getFileName_3482_, v_inst_3483_, v___f_3484_, v___f_3485_, v___f_3486_, v_____s_3487_);
stack->m_obj
 = v_res_3532_;
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__6___boxed(lean_object* v_toPure_3533_, lean_object* v___x_3534_, lean_object* v_logMessage_3535_, lean_object* v_toBind_3536_, lean_object* v_toMonadFileMap_3537_, lean_object* v_getFileName_3538_, lean_object* v_inst_3539_, lean_object* v___f_3540_, lean_object* v___f_3541_, lean_object* v___f_3542_, lean_object* v_____s_3543_){
_start:
{
uint8_t v___x_1062__boxed_3544_; lean_object* v_res_3545_; 
v___x_1062__boxed_3544_ = lean_unbox(v___x_3534_);
v_res_3545_ = l_Lean_addTraceAsMessages___redArg___lam__6(v_toPure_3533_, v___x_1062__boxed_3544_, v_logMessage_3535_, v_toBind_3536_, v_toMonadFileMap_3537_, v_getFileName_3538_, v_inst_3539_, v___f_3540_, v___f_3541_, v___f_3542_, v_____s_3543_);
return v_res_3545_;
}
}
lean_object* l_Lean_addTraceAsMessages___redArg___lam__7(lean_object* v_traceElem_3546_, lean_object* v___f_3547_, lean_object* v___f_3548_, lean_object* v_____s_3549_, lean_object* v_toPure_3550_, uint8_t v___x_3551_, lean_object* v_____do__lift_3552_){
_start:
{
lean_object* v_ref_3553_; lean_object* v_msg_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3578_; 
v_ref_3553_ = lean_ctor_get(v_traceElem_3546_, 0);
v_msg_3554_ = lean_ctor_get(v_traceElem_3546_, 1);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_traceElem_3546_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3556_ = v_traceElem_3546_;
v_isShared_3557_ = v_isSharedCheck_3578_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_msg_3554_);
lean_inc(v_ref_3553_);
lean_dec(v_traceElem_3546_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3578_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v_ref_3570_; lean_object* v___y_3572_; lean_object* v___x_3575_; 
v_ref_3570_ = l_Lean_replaceRef(v_ref_3553_, v_____do__lift_3552_);
lean_dec(v_ref_3553_);
v___x_3575_ = l_Lean_Syntax_getPos_x3f(v_ref_3570_, v___x_3551_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_unsigned_to_nat(0u);
v___y_3572_ = v___x_3576_;
goto v___jp_3571_;
}
else
{
lean_object* v_val_3577_; 
v_val_3577_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_val_3577_);
lean_dec_ref_known(v___x_3575_, 1);
v___y_3572_ = v_val_3577_;
goto v___jp_3571_;
}
v___jp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 1, v___y_3560_);
lean_ctor_set(v___x_3556_, 0, v___y_3559_);
v___x_3562_ = v___x_3556_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___y_3559_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v___y_3560_);
v___x_3562_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v_pos2traces_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3563_ = ((lean_object*)(l_Lean_addTrace___redArg___lam__0___closed__2));
lean_inc_ref(v___x_3562_);
lean_inc_ref(v___f_3548_);
lean_inc_ref(v___f_3547_);
v___x_3564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v___f_3547_, v___f_3548_, v_____s_3549_, v___x_3562_, v___x_3563_);
v___x_3565_ = lean_array_push(v___x_3564_, v_msg_3554_);
v_pos2traces_3566_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3547_, v___f_3548_, v_____s_3549_, v___x_3562_, v___x_3565_);
v___x_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3567_, 0, v_pos2traces_3566_);
v___x_3568_ = lean_apply_2(v_toPure_3550_, lean_box(0), v___x_3567_);
return v___x_3568_;
}
}
v___jp_3571_:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_Syntax_getTailPos_x3f(v_ref_3570_, v___x_3551_);
lean_dec(v_ref_3570_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_inc(v___y_3572_);
v___y_3559_ = v___y_3572_;
v___y_3560_ = v___y_3572_;
goto v___jp_3558_;
}
else
{
lean_object* v_val_3574_; 
v_val_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_val_3574_);
lean_dec_ref_known(v___x_3573_, 1);
v___y_3559_ = v___y_3572_;
v___y_3560_ = v_val_3574_;
goto v___jp_3558_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTraceAsMessages___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_traceElem_3546_ = stack[0].m_obj;
lean_object* v___f_3547_ = stack[1].m_obj;
lean_object* v___f_3548_ = stack[2].m_obj;
lean_object* v_____s_3549_ = stack[3].m_obj;
lean_object* v_toPure_3550_ = stack[4].m_obj;
uint8_t v___x_3551_ = stack[5].m_num;
lean_object* v_____do__lift_3552_ = stack[6].m_obj;
lean_object* v_res_3579_;
v_res_3579_ = l_Lean_addTraceAsMessages___redArg___lam__7(v_traceElem_3546_, v___f_3547_, v___f_3548_, v_____s_3549_, v_toPure_3550_, v___x_3551_, v_____do__lift_3552_);
stack->m_obj
 = v_res_3579_;
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__7___boxed(lean_object* v_traceElem_3580_, lean_object* v___f_3581_, lean_object* v___f_3582_, lean_object* v_____s_3583_, lean_object* v_toPure_3584_, lean_object* v___x_3585_, lean_object* v_____do__lift_3586_){
_start:
{
uint8_t v___x_1229__boxed_3587_; lean_object* v_res_3588_; 
v___x_1229__boxed_3587_ = lean_unbox(v___x_3585_);
v_res_3588_ = l_Lean_addTraceAsMessages___redArg___lam__7(v_traceElem_3580_, v___f_3581_, v___f_3582_, v_____s_3583_, v_toPure_3584_, v___x_1229__boxed_3587_, v_____do__lift_3586_);
lean_dec(v_____do__lift_3586_);
return v_res_3588_;
}
}
lean_object* l_Lean_addTraceAsMessages___redArg___lam__8(lean_object* v_inst_3589_, lean_object* v___f_3590_, lean_object* v___f_3591_, lean_object* v_toPure_3592_, uint8_t v___x_3593_, lean_object* v_toBind_3594_, lean_object* v_traceElem_3595_, lean_object* v_____s_3596_){
_start:
{
lean_object* v_getRef_3597_; lean_object* v___x_3598_; lean_object* v___f_3599_; lean_object* v___x_3600_; 
v_getRef_3597_ = lean_ctor_get(v_inst_3589_, 0);
lean_inc(v_getRef_3597_);
lean_dec_ref(v_inst_3589_);
v___x_3598_ = lean_box(v___x_3593_);
v___f_3599_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__7___boxed), 7, 6);
lean_closure_set(v___f_3599_, 0, v_traceElem_3595_);
lean_closure_set(v___f_3599_, 1, v___f_3590_);
lean_closure_set(v___f_3599_, 2, v___f_3591_);
lean_closure_set(v___f_3599_, 3, v_____s_3596_);
lean_closure_set(v___f_3599_, 4, v_toPure_3592_);
lean_closure_set(v___f_3599_, 5, v___x_3598_);
v___x_3600_ = lean_apply_4(v_toBind_3594_, lean_box(0), lean_box(0), v_getRef_3597_, v___f_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT void l_Lean_addTraceAsMessages___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3589_ = stack[0].m_obj;
lean_object* v___f_3590_ = stack[1].m_obj;
lean_object* v___f_3591_ = stack[2].m_obj;
lean_object* v_toPure_3592_ = stack[3].m_obj;
uint8_t v___x_3593_ = stack[4].m_num;
lean_object* v_toBind_3594_ = stack[5].m_obj;
lean_object* v_traceElem_3595_ = stack[6].m_obj;
lean_object* v_____s_3596_ = stack[7].m_obj;
lean_object* v_res_3601_;
v_res_3601_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_inst_3589_, v___f_3590_, v___f_3591_, v_toPure_3592_, v___x_3593_, v_toBind_3594_, v_traceElem_3595_, v_____s_3596_);
stack->m_obj
 = v_res_3601_;
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__8___boxed(lean_object* v_inst_3602_, lean_object* v___f_3603_, lean_object* v___f_3604_, lean_object* v_toPure_3605_, lean_object* v___x_3606_, lean_object* v_toBind_3607_, lean_object* v_traceElem_3608_, lean_object* v_____s_3609_){
_start:
{
uint8_t v___x_1321__boxed_3610_; lean_object* v_res_3611_; 
v___x_1321__boxed_3610_ = lean_unbox(v___x_3606_);
v_res_3611_ = l_Lean_addTraceAsMessages___redArg___lam__8(v_inst_3602_, v___f_3603_, v___f_3604_, v_toPure_3605_, v___x_1321__boxed_3610_, v_toBind_3607_, v_traceElem_3608_, v_____s_3609_);
return v_res_3611_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__0(void){
_start:
{
lean_object* v___x_3612_; lean_object* v___f_3613_; 
v___x_3612_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_3613_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3613_, 0, v___x_3612_);
return v___f_3613_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__1(void){
_start:
{
lean_object* v___f_3614_; lean_object* v___f_3615_; 
v___f_3614_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__0, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__0_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__0);
v___f_3615_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3615_, 0, v___f_3614_);
lean_closure_set(v___f_3615_, 1, v___f_3614_);
return v___f_3615_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__2(void){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3616_ = lean_box(0);
v___x_3617_ = lean_unsigned_to_nat(16u);
v___x_3618_ = lean_mk_array(v___x_3617_, v___x_3616_);
return v___x_3618_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__3(void){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v_pos2traces_3621_; 
v___x_3619_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__2, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__2_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__2);
v___x_3620_ = lean_unsigned_to_nat(0u);
v_pos2traces_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_3621_, 0, v___x_3620_);
lean_ctor_set(v_pos2traces_3621_, 1, v___x_3619_);
return v_pos2traces_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9(lean_object* v_inst_3622_, lean_object* v___f_3623_, lean_object* v_toPure_3624_, lean_object* v_toBind_3625_, lean_object* v_inst_3626_, lean_object* v___f_3627_, lean_object* v_traces_3628_){
_start:
{
uint8_t v___x_3629_; 
v___x_3629_ = l_Lean_PersistentArray_isEmpty___redArg(v_traces_3628_);
if (v___x_3629_ == 0)
{
lean_object* v___f_3630_; lean_object* v___x_3631_; lean_object* v___f_3632_; lean_object* v_pos2traces_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___f_3630_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__1, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__1_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__1);
v___x_3631_ = lean_box(v___x_3629_);
lean_inc(v_toBind_3625_);
v___f_3632_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__8___boxed), 8, 6);
lean_closure_set(v___f_3632_, 0, v_inst_3622_);
lean_closure_set(v___f_3632_, 1, v___f_3630_);
lean_closure_set(v___f_3632_, 2, v___f_3623_);
lean_closure_set(v___f_3632_, 3, v_toPure_3624_);
lean_closure_set(v___f_3632_, 4, v___x_3631_);
lean_closure_set(v___f_3632_, 5, v_toBind_3625_);
v_pos2traces_3633_ = lean_obj_once(&l_Lean_addTraceAsMessages___redArg___lam__9___closed__3, &l_Lean_addTraceAsMessages___redArg___lam__9___closed__3_once, _init_l_Lean_addTraceAsMessages___redArg___lam__9___closed__3);
v___x_3634_ = l_Lean_PersistentArray_forIn___redArg(v_inst_3626_, v_traces_3628_, v_pos2traces_3633_, v___f_3632_);
v___x_3635_ = lean_apply_4(v_toBind_3625_, lean_box(0), lean_box(0), v___x_3634_, v___f_3627_);
return v___x_3635_;
}
else
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
lean_dec(v___f_3627_);
lean_dec_ref(v_inst_3626_);
lean_dec(v_toBind_3625_);
lean_dec_ref(v___f_3623_);
lean_dec_ref(v_inst_3622_);
v___x_3636_ = lean_box(0);
v___x_3637_ = lean_apply_2(v_toPure_3624_, lean_box(0), v___x_3636_);
return v___x_3637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__9___boxed(lean_object* v_inst_3638_, lean_object* v___f_3639_, lean_object* v_toPure_3640_, lean_object* v_toBind_3641_, lean_object* v_inst_3642_, lean_object* v___f_3643_, lean_object* v_traces_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Lean_addTraceAsMessages___redArg___lam__9(v_inst_3638_, v___f_3639_, v_toPure_3640_, v_toBind_3641_, v_inst_3642_, v___f_3643_, v_traces_3644_);
lean_dec_ref(v_traces_3644_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10(lean_object* v_toPure_3646_, lean_object* v_logMessage_3647_, lean_object* v_toBind_3648_, lean_object* v_toMonadFileMap_3649_, lean_object* v_getFileName_3650_, lean_object* v_inst_3651_, lean_object* v___f_3652_, lean_object* v___f_3653_, lean_object* v___f_3654_, lean_object* v_inst_3655_, lean_object* v___f_3656_, lean_object* v_inst_3657_, lean_object* v_____do__lift_3658_){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3662_ = l_Lean_KVMap_instValueBool;
v___x_3663_ = l_Lean_KVMap_instValueString;
v___x_3664_ = l_Lean_trace_profiler_output;
v___x_3665_ = l_Lean_Option_get_x3f___redArg(v___x_3663_, v_____do__lift_3658_, v___x_3664_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; uint8_t v___x_3668_; 
v___x_3666_ = l_Lean_trace_profiler_serve;
v___x_3667_ = l_Lean_Option_get___redArg(v___x_3662_, v_____do__lift_3658_, v___x_3666_);
v___x_3668_ = lean_unbox(v___x_3667_);
lean_dec(v___x_3667_);
if (v___x_3668_ == 0)
{
uint8_t v___x_3669_; lean_object* v___x_3670_; lean_object* v___f_3671_; lean_object* v___f_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3669_ = 1;
v___x_3670_ = lean_box(v___x_3669_);
lean_inc_ref_n(v_inst_3651_, 2);
lean_inc_n(v_toBind_3648_, 2);
lean_inc(v_toPure_3646_);
v___f_3671_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_3671_, 0, v_toPure_3646_);
lean_closure_set(v___f_3671_, 1, v___x_3670_);
lean_closure_set(v___f_3671_, 2, v_logMessage_3647_);
lean_closure_set(v___f_3671_, 3, v_toBind_3648_);
lean_closure_set(v___f_3671_, 4, v_toMonadFileMap_3649_);
lean_closure_set(v___f_3671_, 5, v_getFileName_3650_);
lean_closure_set(v___f_3671_, 6, v_inst_3651_);
lean_closure_set(v___f_3671_, 7, v___f_3652_);
lean_closure_set(v___f_3671_, 8, v___f_3653_);
lean_closure_set(v___f_3671_, 9, v___f_3654_);
v___f_3672_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_3672_, 0, v_inst_3655_);
lean_closure_set(v___f_3672_, 1, v___f_3656_);
lean_closure_set(v___f_3672_, 2, v_toPure_3646_);
lean_closure_set(v___f_3672_, 3, v_toBind_3648_);
lean_closure_set(v___f_3672_, 4, v_inst_3651_);
lean_closure_set(v___f_3672_, 5, v___f_3671_);
v___x_3673_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___redArg(v_inst_3651_, v_inst_3657_);
v___x_3674_ = lean_apply_4(v_toBind_3648_, lean_box(0), lean_box(0), v___x_3673_, v___f_3672_);
return v___x_3674_;
}
else
{
lean_dec_ref(v_inst_3657_);
lean_dec_ref(v___f_3656_);
lean_dec_ref(v_inst_3655_);
lean_dec_ref(v___f_3654_);
lean_dec_ref(v___f_3653_);
lean_dec(v___f_3652_);
lean_dec_ref(v_inst_3651_);
lean_dec(v_getFileName_3650_);
lean_dec(v_toMonadFileMap_3649_);
lean_dec(v_toBind_3648_);
lean_dec(v_logMessage_3647_);
goto v___jp_3659_;
}
}
else
{
lean_dec_ref_known(v___x_3665_, 1);
lean_dec_ref(v_inst_3657_);
lean_dec_ref(v___f_3656_);
lean_dec_ref(v_inst_3655_);
lean_dec_ref(v___f_3654_);
lean_dec_ref(v___f_3653_);
lean_dec(v___f_3652_);
lean_dec_ref(v_inst_3651_);
lean_dec(v_getFileName_3650_);
lean_dec(v_toMonadFileMap_3649_);
lean_dec(v_toBind_3648_);
lean_dec(v_logMessage_3647_);
goto v___jp_3659_;
}
v___jp_3659_:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = lean_box(0);
v___x_3661_ = lean_apply_2(v_toPure_3646_, lean_box(0), v___x_3660_);
return v___x_3661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg___lam__10___boxed(lean_object* v_toPure_3675_, lean_object* v_logMessage_3676_, lean_object* v_toBind_3677_, lean_object* v_toMonadFileMap_3678_, lean_object* v_getFileName_3679_, lean_object* v_inst_3680_, lean_object* v___f_3681_, lean_object* v___f_3682_, lean_object* v___f_3683_, lean_object* v_inst_3684_, lean_object* v___f_3685_, lean_object* v_inst_3686_, lean_object* v_____do__lift_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Lean_addTraceAsMessages___redArg___lam__10(v_toPure_3675_, v_logMessage_3676_, v_toBind_3677_, v_toMonadFileMap_3678_, v_getFileName_3679_, v_inst_3680_, v___f_3681_, v___f_3682_, v___f_3683_, v_inst_3684_, v___f_3685_, v_inst_3686_, v_____do__lift_3687_);
lean_dec_ref(v_____do__lift_3687_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___redArg(lean_object* v_inst_3694_, lean_object* v_inst_3695_, lean_object* v_inst_3696_, lean_object* v_inst_3697_, lean_object* v_inst_3698_){
_start:
{
lean_object* v___f_3699_; lean_object* v_toApplicative_3700_; lean_object* v_toBind_3701_; lean_object* v_getOptionsUnrestricted_3702_; lean_object* v_toPure_3703_; lean_object* v_toMonadFileMap_3704_; lean_object* v_getFileName_3705_; lean_object* v_logMessage_3706_; lean_object* v___f_3707_; lean_object* v___f_3708_; lean_object* v___f_3709_; lean_object* v___f_3710_; lean_object* v___x_3711_; 
v___f_3699_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__1));
v_toApplicative_3700_ = lean_ctor_get(v_inst_3695_, 0);
v_toBind_3701_ = lean_ctor_get(v_inst_3695_, 1);
lean_inc_n(v_toBind_3701_, 2);
v_getOptionsUnrestricted_3702_ = lean_ctor_get(v_inst_3694_, 1);
lean_inc(v_getOptionsUnrestricted_3702_);
lean_dec_ref(v_inst_3694_);
v_toPure_3703_ = lean_ctor_get(v_toApplicative_3700_, 1);
lean_inc_n(v_toPure_3703_, 2);
v_toMonadFileMap_3704_ = lean_ctor_get(v_inst_3697_, 0);
lean_inc(v_toMonadFileMap_3704_);
v_getFileName_3705_ = lean_ctor_get(v_inst_3697_, 2);
lean_inc(v_getFileName_3705_);
v_logMessage_3706_ = lean_ctor_get(v_inst_3697_, 4);
lean_inc(v_logMessage_3706_);
lean_dec_ref(v_inst_3697_);
v___f_3707_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__2));
v___f_3708_ = ((lean_object*)(l_Lean_addTraceAsMessages___redArg___closed__3));
v___f_3709_ = lean_alloc_closure((void*)(l_Lean_printTraces___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3709_, 0, v_toPure_3703_);
v___f_3710_ = lean_alloc_closure((void*)(l_Lean_addTraceAsMessages___redArg___lam__10___boxed), 13, 12);
lean_closure_set(v___f_3710_, 0, v_toPure_3703_);
lean_closure_set(v___f_3710_, 1, v_logMessage_3706_);
lean_closure_set(v___f_3710_, 2, v_toBind_3701_);
lean_closure_set(v___f_3710_, 3, v_toMonadFileMap_3704_);
lean_closure_set(v___f_3710_, 4, v_getFileName_3705_);
lean_closure_set(v___f_3710_, 5, v_inst_3695_);
lean_closure_set(v___f_3710_, 6, v___f_3709_);
lean_closure_set(v___f_3710_, 7, v___f_3707_);
lean_closure_set(v___f_3710_, 8, v___f_3708_);
lean_closure_set(v___f_3710_, 9, v_inst_3696_);
lean_closure_set(v___f_3710_, 10, v___f_3699_);
lean_closure_set(v___f_3710_, 11, v_inst_3698_);
v___x_3711_ = lean_apply_4(v_toBind_3701_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_3702_, v___f_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages(lean_object* v_m_3712_, lean_object* v_inst_3713_, lean_object* v_inst_3714_, lean_object* v_inst_3715_, lean_object* v_inst_3716_, lean_object* v_inst_3717_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_addTraceAsMessages___redArg(v_inst_3713_, v_inst_3714_, v_inst_3715_, v_inst_3716_, v_inst_3717_);
return v___x_3718_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3760_ = lean_unsigned_to_nat(2826257906u);
v___x_3761_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__17_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3762_ = l_Lean_Name_num___override(v___x_3761_, v___x_3760_);
return v___x_3762_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3764_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__19_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3765_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__18_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3766_ = l_Lean_Name_str___override(v___x_3765_, v___x_3764_);
return v___x_3766_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3768_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__21_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3769_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__20_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3770_ = l_Lean_Name_str___override(v___x_3769_, v___x_3768_);
return v___x_3770_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3771_ = lean_unsigned_to_nat(2u);
v___x_3772_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__22_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3773_ = l_Lean_Name_num___override(v___x_3772_, v___x_3771_);
return v___x_3773_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3775_; uint8_t v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3775_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_initFn___closed__1_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_));
v___x_3776_ = 0;
v___x_3777_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_, &l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__once, _init_l___private_Lean_Util_Trace_0__Lean_initFn___closed__23_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_);
v___x_3778_ = l_Lean_registerTraceClass(v___x_3775_, v___x_3776_, v___x_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3779_;
v_res_3779_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3779_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2____boxed(lean_object* v_a_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l___private_Lean_Util_Trace_0__Lean_initFn_00___x40_Lean_Util_Trace_2826257906____hygCtx___hyg_2_();
return v_res_3781_;
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
