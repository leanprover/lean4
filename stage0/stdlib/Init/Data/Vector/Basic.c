// Lean compiler output
// Module: Init.Data.Vector.Basic
// Imports: import Init.Data.Array.Nat public import Init.Data.Array.DecidableEq public import Init.Data.Range.Polymorphic.RangeIterator import Init.Data.Array.InsertIdx import Init.Data.Array.MapIdx import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic.Nat import Init.Omega
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isPrefixOf___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_instDecidableEqImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_mark_linear(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_append___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_repr(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Array_finIdxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zipWithMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_range_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqVector___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqVector___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqVector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqVector___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toVector___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_toVector___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_toVector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toVector___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_size___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Vector"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__0 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term#v[_,]"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__1 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__1_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value_aux_0),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 133, 146, 175, 235, 143, 200, 186)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__2 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__3 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__3_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__4 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#v["};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__5 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__5_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__5_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__6 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__6_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__7 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__7_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__7_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__8 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__8_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__9 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__9_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__10 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__10_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__11 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__11_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__12 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__13 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__14 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__11_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__15 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__8_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__16 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__6_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__17 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__18 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__19 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__20 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__21 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__21_value;
LEAN_EXPORT const lean_object* l_Vector_term_x23v_x5b___x2c_x5d = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__21_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_2),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Vector.mk"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5_value;
static lean_once_cell_t l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(253, 158, 113, 206, 216, 2, 54, 152)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9_value),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11_value)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_2),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18_value;
static lean_once_cell_t l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(85, 67, 188, 79, 172, 243, 130, 138)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term#[_,]"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(69, 119, 178, 128, 145, 112, 206, 247)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25_value;
static lean_once_cell_t l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27_value;
static lean_once_cell_t l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31_value;
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_unexpandMk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_unexpandMk___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Vector_Vector_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value)}};
static const lean_object* l_Vector_Vector_repr___redArg___closed__0 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__0_value;
static const lean_ctor_object l_Vector_Vector_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_Vector_repr___redArg___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Vector_Vector_repr___redArg___closed__1 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__1_value;
static lean_once_cell_t l_Vector_Vector_repr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_Vector_repr___redArg___closed__2;
static lean_once_cell_t l_Vector_Vector_repr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_Vector_repr___redArg___closed__3;
static const lean_ctor_object l_Vector_Vector_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__5_value)}};
static const lean_object* l_Vector_Vector_repr___redArg___closed__4 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__4_value;
static const lean_ctor_object l_Vector_Vector_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value)}};
static const lean_object* l_Vector_Vector_repr___redArg___closed__5 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__5_value;
static const lean_string_object l_Vector_Vector_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "#v[]"};
static const lean_object* l_Vector_Vector_repr___redArg___closed__6 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__6_value;
static const lean_ctor_object l_Vector_Vector_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_Vector_repr___redArg___closed__6_value)}};
static const lean_object* l_Vector_Vector_repr___redArg___closed__7 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Vector_Vector_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_repr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_replicate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_replicate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_singleton___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_singleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instInhabited___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_get(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_uget___redArg(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Vector_uget___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_uget(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Vector_uget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Vector_instGetElemNatLt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Vector_instGetElemNatLt___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_instGetElemNatLt___redArg___closed__0 = (const lean_object*)&l_Vector_instGetElemNatLt___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg();
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instMembership___redArg();
LEAN_EXPORT lean_object* l_Vector_instMembership___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instMembership(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instMembership___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_getD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_getD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_head___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_head___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_head(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_head___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_push(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_pop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_pop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_pop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_markLinear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_markLinear(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_markLinear___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_propagateMark(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_propagateMark___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_set___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Vector_set___auto__1___closed__0 = (const lean_object*)&l_Vector_set___auto__1___closed__0_value;
static const lean_string_object l_Vector_set___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Vector_set___auto__1___closed__1 = (const lean_object*)&l_Vector_set___auto__1___closed__1_value;
static const lean_ctor_object l_Vector_set___auto__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__2_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__2_value_aux_1),((lean_object*)&l_Vector_set___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__2_value_aux_2),((lean_object*)&l_Vector_set___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Vector_set___auto__1___closed__2 = (const lean_object*)&l_Vector_set___auto__1___closed__2_value;
static const lean_array_object l_Vector_set___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Vector_set___auto__1___closed__3 = (const lean_object*)&l_Vector_set___auto__1___closed__3_value;
static const lean_string_object l_Vector_set___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Vector_set___auto__1___closed__4 = (const lean_object*)&l_Vector_set___auto__1___closed__4_value;
static const lean_ctor_object l_Vector_set___auto__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__5_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__5_value_aux_1),((lean_object*)&l_Vector_set___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__5_value_aux_2),((lean_object*)&l_Vector_set___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Vector_set___auto__1___closed__5 = (const lean_object*)&l_Vector_set___auto__1___closed__5_value;
static const lean_string_object l_Vector_set___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_Vector_set___auto__1___closed__6 = (const lean_object*)&l_Vector_set___auto__1___closed__6_value;
static const lean_ctor_object l_Vector_set___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_set___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_Vector_set___auto__1___closed__7 = (const lean_object*)&l_Vector_set___auto__1___closed__7_value;
static const lean_string_object l_Vector_set___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_Vector_set___auto__1___closed__8 = (const lean_object*)&l_Vector_set___auto__1___closed__8_value;
static lean_once_cell_t l_Vector_set___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__9;
static lean_once_cell_t l_Vector_set___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__10;
static lean_once_cell_t l_Vector_set___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__11;
static lean_once_cell_t l_Vector_set___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__12;
static lean_once_cell_t l_Vector_set___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__13;
static lean_once_cell_t l_Vector_set___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__14;
static lean_once_cell_t l_Vector_set___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__15;
static lean_once_cell_t l_Vector_set___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__16;
static lean_once_cell_t l_Vector_set___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__17;
LEAN_EXPORT lean_object* l_Vector_set___auto__1;
LEAN_EXPORT lean_object* l_Vector_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_setIfInBounds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Vector_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__0 = (const lean_object*)&l_Vector_foldl___redArg___closed__0_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__1 = (const lean_object*)&l_Vector_foldl___redArg___closed__1_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__2 = (const lean_object*)&l_Vector_foldl___redArg___closed__2_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__3 = (const lean_object*)&l_Vector_foldl___redArg___closed__3_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__4 = (const lean_object*)&l_Vector_foldl___redArg___closed__4_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__5 = (const lean_object*)&l_Vector_foldl___redArg___closed__5_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__6 = (const lean_object*)&l_Vector_foldl___redArg___closed__6_value;
static const lean_ctor_object l_Vector_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_foldl___redArg___closed__0_value),((lean_object*)&l_Vector_foldl___redArg___closed__1_value)}};
static const lean_object* l_Vector_foldl___redArg___closed__7 = (const lean_object*)&l_Vector_foldl___redArg___closed__7_value;
static const lean_ctor_object l_Vector_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_foldl___redArg___closed__7_value),((lean_object*)&l_Vector_foldl___redArg___closed__2_value),((lean_object*)&l_Vector_foldl___redArg___closed__3_value),((lean_object*)&l_Vector_foldl___redArg___closed__4_value),((lean_object*)&l_Vector_foldl___redArg___closed__5_value)}};
static const lean_object* l_Vector_foldl___redArg___closed__8 = (const lean_object*)&l_Vector_foldl___redArg___closed__8_value;
static const lean_ctor_object l_Vector_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_foldl___redArg___closed__8_value),((lean_object*)&l_Vector_foldl___redArg___closed__6_value)}};
static const lean_object* l_Vector_foldl___redArg___closed__9 = (const lean_object*)&l_Vector_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Vector_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_append___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_append(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_append___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_extract___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_extract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_extract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_take___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_take___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_take(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_take___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_drop___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_drop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_drop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_shrink___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_shrink(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_shrink___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Vector_mapM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Vector_mapM___redArg___closed__0 = (const lean_object*)&l_Vector_mapM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Vector_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdxM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_firstM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_firstM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_firstM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Vector_flatten___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Vector_flatten___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_flatten___redArg___closed__0 = (const lean_object*)&l_Vector_flatten___redArg___closed__0_value;
static const lean_array_object l_Vector_flatten___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Vector_flatten___redArg___closed__1 = (const lean_object*)&l_Vector_flatten___redArg___closed__1_value;
static const lean_closure_object l_Vector_flatten___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_append___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_flatten___redArg___closed__2 = (const lean_object*)&l_Vector_flatten___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Vector_flatten___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatten(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatten___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zip___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zip___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipWith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_unzip___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_unzip___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_unzip(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_unzip___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_ofFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swap___auto__1;
LEAN_EXPORT lean_object* l_Vector_swap___auto__3;
LEAN_EXPORT lean_object* l_Vector_swap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swap___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt___auto__1;
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_swapAt_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Init.Data.Array.Basic"};
static const lean_object* l_Vector_swapAt_x21___redArg___closed__0 = (const lean_object*)&l_Vector_swapAt_x21___redArg___closed__0_value;
static const lean_string_object l_Vector_swapAt_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Array.swapAt!"};
static const lean_object* l_Vector_swapAt_x21___redArg___closed__1 = (const lean_object*)&l_Vector_swapAt_x21___redArg___closed__1_value;
static const lean_string_object l_Vector_swapAt_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "index "};
static const lean_object* l_Vector_swapAt_x21___redArg___closed__2 = (const lean_object*)&l_Vector_swapAt_x21___redArg___closed__2_value;
static const lean_string_object l_Vector_swapAt_x21___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " out of bounds"};
static const lean_object* l_Vector_swapAt_x21___redArg___closed__3 = (const lean_object*)&l_Vector_swapAt_x21___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_range(lean_object*);
LEAN_EXPORT lean_object* l_Vector_range_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_isEqv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_isEqv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_isEqv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_isEqv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instBEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_reverse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_reverse___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx___auto__1;
LEAN_EXPORT lean_object* l_Vector_eraseIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_eraseIdx_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.Vector.Basic"};
static const lean_object* l_Vector_eraseIdx_x21___redArg___closed__0 = (const lean_object*)&l_Vector_eraseIdx_x21___redArg___closed__0_value;
static const lean_string_object l_Vector_eraseIdx_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Vector.eraseIdx!"};
static const lean_object* l_Vector_eraseIdx_x21___redArg___closed__1 = (const lean_object*)&l_Vector_eraseIdx_x21___redArg___closed__1_value;
static const lean_string_object l_Vector_eraseIdx_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "index out of bounds"};
static const lean_object* l_Vector_eraseIdx_x21___redArg___closed__2 = (const lean_object*)&l_Vector_eraseIdx_x21___redArg___closed__2_value;
static lean_once_cell_t l_Vector_eraseIdx_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_eraseIdx_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx___auto__1;
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_insertIdx_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Vector.insertIdx!"};
static const lean_object* l_Vector_insertIdx_x21___redArg___closed__0 = (const lean_object*)&l_Vector_insertIdx_x21___redArg___closed__0_value;
static lean_once_cell_t l_Vector_insertIdx_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_insertIdx_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_tail___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_tail___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_tail(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_tail___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Vector_findM_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector_findM_x3f___redArg___closed__0 = (const lean_object*)&l_Vector_findM_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRev_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_isPrefixOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_isPrefixOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_anyM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_any___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_any___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_all___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Vector_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_countP___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_countP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_countP___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_count___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_sum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_sum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_sum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_prod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_prod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_leftpad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_leftpad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_rightpad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_rightpad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLT___redArg();
LEAN_EXPORT lean_object* l_Vector_instLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLE___redArg();
LEAN_EXPORT lean_object* l_Vector_instLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLE___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_lex___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Vector_lex___auto__1___closed__0 = (const lean_object*)&l_Vector_lex___auto__1___closed__0_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__1_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__1_value_aux_1),((lean_object*)&l_Vector_set___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__1_value_aux_2),((lean_object*)&l_Vector_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Vector_lex___auto__1___closed__1 = (const lean_object*)&l_Vector_lex___auto__1___closed__1_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__2;
static lean_once_cell_t l_Vector_lex___auto__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__3;
static const lean_string_object l_Vector_lex___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Vector_lex___auto__1___closed__4 = (const lean_object*)&l_Vector_lex___auto__1___closed__4_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__5_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__5_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__5_value_aux_2),((lean_object*)&l_Vector_lex___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Vector_lex___auto__1___closed__5 = (const lean_object*)&l_Vector_lex___auto__1___closed__5_value;
static const lean_string_object l_Vector_lex___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Vector_lex___auto__1___closed__6 = (const lean_object*)&l_Vector_lex___auto__1___closed__6_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__7_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__7_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__7_value_aux_2),((lean_object*)&l_Vector_lex___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Vector_lex___auto__1___closed__7 = (const lean_object*)&l_Vector_lex___auto__1___closed__7_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__8;
static lean_once_cell_t l_Vector_lex___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__9;
static const lean_string_object l_Vector_lex___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Vector_lex___auto__1___closed__10 = (const lean_object*)&l_Vector_lex___auto__1___closed__10_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_lex___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Vector_lex___auto__1___closed__11 = (const lean_object*)&l_Vector_lex___auto__1___closed__11_value;
static const lean_string_object l_Vector_lex___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Vector_lex___auto__1___closed__12 = (const lean_object*)&l_Vector_lex___auto__1___closed__12_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__13;
static lean_once_cell_t l_Vector_lex___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__14;
static lean_once_cell_t l_Vector_lex___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__15;
static lean_once_cell_t l_Vector_lex___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__16;
static lean_once_cell_t l_Vector_lex___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__17;
static lean_once_cell_t l_Vector_lex___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__18;
static lean_once_cell_t l_Vector_lex___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__19;
static lean_once_cell_t l_Vector_lex___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__20;
static const lean_string_object l_Vector_lex___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l_Vector_lex___auto__1___closed__21 = (const lean_object*)&l_Vector_lex___auto__1___closed__21_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_lex___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l_Vector_lex___auto__1___closed__22 = (const lean_object*)&l_Vector_lex___auto__1___closed__22_value;
static const lean_string_object l_Vector_lex___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l_Vector_lex___auto__1___closed__23 = (const lean_object*)&l_Vector_lex___auto__1___closed__23_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__24_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__24_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__24_value_aux_2),((lean_object*)&l_Vector_lex___auto__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l_Vector_lex___auto__1___closed__24 = (const lean_object*)&l_Vector_lex___auto__1___closed__24_value;
static const lean_string_object l_Vector_lex___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l_Vector_lex___auto__1___closed__25 = (const lean_object*)&l_Vector_lex___auto__1___closed__25_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__26;
static lean_once_cell_t l_Vector_lex___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__27;
static lean_once_cell_t l_Vector_lex___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__28;
static lean_once_cell_t l_Vector_lex___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__29;
static lean_once_cell_t l_Vector_lex___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__30;
static const lean_string_object l_Vector_lex___auto__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_Vector_lex___auto__1___closed__31 = (const lean_object*)&l_Vector_lex___auto__1___closed__31_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__32;
static lean_once_cell_t l_Vector_lex___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__33;
static lean_once_cell_t l_Vector_lex___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__34;
static lean_once_cell_t l_Vector_lex___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__35;
static lean_once_cell_t l_Vector_lex___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__36;
static lean_once_cell_t l_Vector_lex___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__37;
static lean_once_cell_t l_Vector_lex___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__38;
static lean_once_cell_t l_Vector_lex___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__39;
static lean_once_cell_t l_Vector_lex___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__40;
static lean_once_cell_t l_Vector_lex___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__41;
static lean_once_cell_t l_Vector_lex___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__42;
static lean_once_cell_t l_Vector_lex___auto__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__43;
static lean_once_cell_t l_Vector_lex___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__44;
static lean_once_cell_t l_Vector_lex___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__45;
static lean_once_cell_t l_Vector_lex___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__46;
static lean_once_cell_t l_Vector_lex___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__47;
LEAN_EXPORT lean_object* l_Vector_lex___auto__1;
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Vector_lex___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector_lex___redArg___closed__0 = (const lean_object*)&l_Vector_lex___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_lex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq___redArg(lean_object* v_inst_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Array_instDecidableEqImpl___redArg(v_inst_1_, v_x_2_, v_x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___redArg___boxed(lean_object* v_inst_5_, lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_instDecidableEqVector_decEq___redArg(v_inst_5_, v_x_6_, v_x_7_);
lean_dec_ref(v_x_7_);
lean_dec_ref(v_x_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq(lean_object* v_00_u03b1_10_, lean_object* v_n_11_, lean_object* v_inst_12_, lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = l_Array_instDecidableEqImpl___redArg(v_inst_12_, v_x_13_, v_x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___boxed(lean_object* v_00_u03b1_16_, lean_object* v_n_17_, lean_object* v_inst_18_, lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_instDecidableEqVector_decEq(v_00_u03b1_16_, v_n_17_, v_inst_18_, v_x_19_, v_x_20_);
lean_dec_ref(v_x_20_);
lean_dec_ref(v_x_19_);
lean_dec(v_n_17_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector___redArg(lean_object* v_inst_23_, lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = l_Array_instDecidableEqImpl___redArg(v_inst_23_, v_x_24_, v_x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector___redArg___boxed(lean_object* v_inst_27_, lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_instDecidableEqVector___redArg(v_inst_27_, v_x_28_, v_x_29_);
lean_dec_ref(v_x_29_);
lean_dec_ref(v_x_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector(lean_object* v_00_u03b1_32_, lean_object* v_n_33_, lean_object* v_inst_34_, lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = l_Array_instDecidableEqImpl___redArg(v_inst_34_, v_x_35_, v_x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector___boxed(lean_object* v_00_u03b1_38_, lean_object* v_n_39_, lean_object* v_inst_40_, lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_instDecidableEqVector(v_00_u03b1_38_, v_n_39_, v_inst_40_, v_x_41_, v_x_42_);
lean_dec_ref(v_x_42_);
lean_dec_ref(v_x_41_);
lean_dec(v_n_39_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___redArg(lean_object* v_xs_45_){
_start:
{
lean_inc_ref(v_xs_45_);
return v_xs_45_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___redArg___boxed(lean_object* v_xs_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Array_toVector___redArg(v_xs_46_);
lean_dec_ref(v_xs_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector(lean_object* v_00_u03b1_48_, lean_object* v_xs_49_){
_start:
{
lean_inc_ref(v_xs_49_);
return v_xs_49_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___boxed(lean_object* v_00_u03b1_50_, lean_object* v_xs_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Array_toVector(v_00_u03b1_50_, v_xs_51_);
lean_dec_ref(v_xs_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___redArg(lean_object* v_n_53_){
_start:
{
lean_inc(v_n_53_);
return v_n_53_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___redArg___boxed(lean_object* v_n_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Vector_size___redArg(v_n_54_);
lean_dec(v_n_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Vector_size(lean_object* v_00_u03b1_56_, lean_object* v_n_57_, lean_object* v_x_58_){
_start:
{
lean_inc(v_n_57_);
return v_n_57_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___boxed(lean_object* v_00_u03b1_59_, lean_object* v_n_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Vector_size(v_00_u03b1_59_, v_n_60_, v_x_61_);
lean_dec_ref(v_x_61_);
lean_dec(v_n_60_);
return v_res_62_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5));
v___x_122_ = l_String_toRawSubstring_x27(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18));
v___x_150_ = l_String_toRawSubstring_x27(v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26(void){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Array_mkArray0___redArg();
return v___x_159_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27));
v___x_162_ = l_String_toRawSubstring_x27(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(lean_object* v_x_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__2));
lean_inc(v_x_171_);
v___x_175_ = l_Lean_Syntax_isOfKind(v_x_171_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_x_171_);
v___x_176_ = lean_box(1);
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v_a_173_);
return v___x_177_;
}
else
{
lean_object* v_quotContext_178_; lean_object* v_currMacroScope_179_; lean_object* v_ref_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_elems_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_quotContext_178_ = lean_ctor_get(v_a_172_, 1);
v_currMacroScope_179_ = lean_ctor_get(v_a_172_, 2);
v_ref_180_ = lean_ctor_get(v_a_172_, 5);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = l_Lean_Syntax_getArg(v_x_171_, v___x_181_);
lean_dec(v_x_171_);
v_elems_183_ = l_Lean_Syntax_getArgs(v___x_182_);
lean_dec(v___x_182_);
v___x_184_ = 0;
v___x_185_ = l_Lean_SourceInfo_fromRef(v_ref_180_, v___x_184_);
v___x_186_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4));
v___x_187_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6);
v___x_188_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8));
lean_inc_n(v_currMacroScope_179_, 3);
lean_inc_n(v_quotContext_178_, 3);
v___x_189_ = l_Lean_addMacroScope(v_quotContext_178_, v___x_188_, v_currMacroScope_179_);
v___x_190_ = lean_box(0);
v___x_191_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12));
lean_inc_n(v___x_185_, 12);
v___x_192_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_192_, 0, v___x_185_);
lean_ctor_set(v___x_192_, 1, v___x_187_);
lean_ctor_set(v___x_192_, 2, v___x_189_);
lean_ctor_set(v___x_192_, 3, v___x_191_);
v___x_193_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_194_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16));
v___x_195_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_185_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19);
v___x_198_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20));
v___x_199_ = l_Lean_addMacroScope(v_quotContext_178_, v___x_198_, v_currMacroScope_179_);
v___x_200_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_200_, 0, v___x_185_);
lean_ctor_set(v___x_200_, 1, v___x_197_);
lean_ctor_set(v___x_200_, 2, v___x_199_);
lean_ctor_set(v___x_200_, 3, v___x_190_);
v___x_201_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21));
v___x_202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_185_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_elems_183_);
v___x_204_ = lean_array_get_size(v___x_203_);
lean_dec_ref(v___x_203_);
v___x_205_ = l_Nat_reprFast(v___x_204_);
v___x_206_ = lean_box(2);
v___x_207_ = l_Lean_Syntax_mkNumLit(v___x_205_, v___x_206_);
v___x_208_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_185_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = l_Lean_Syntax_node5(v___x_185_, v___x_194_, v___x_196_, v___x_200_, v___x_202_, v___x_207_, v___x_209_);
v___x_211_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24));
v___x_212_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25));
v___x_213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_185_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
v___x_215_ = l_Array_append___redArg(v___x_214_, v_elems_183_);
lean_dec_ref(v_elems_183_);
v___x_216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_216_, 0, v___x_185_);
lean_ctor_set(v___x_216_, 1, v___x_193_);
lean_ctor_set(v___x_216_, 2, v___x_215_);
v___x_217_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__18));
v___x_218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_185_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = l_Lean_Syntax_node3(v___x_185_, v___x_211_, v___x_213_, v___x_216_, v___x_218_);
v___x_220_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28);
v___x_221_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29));
v___x_222_ = l_Lean_addMacroScope(v_quotContext_178_, v___x_221_, v_currMacroScope_179_);
v___x_223_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31));
v___x_224_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_224_, 0, v___x_185_);
lean_ctor_set(v___x_224_, 1, v___x_220_);
lean_ctor_set(v___x_224_, 2, v___x_222_);
lean_ctor_set(v___x_224_, 3, v___x_223_);
v___x_225_ = l_Lean_Syntax_node3(v___x_185_, v___x_193_, v___x_210_, v___x_219_, v___x_224_);
v___x_226_ = l_Lean_Syntax_node2(v___x_185_, v___x_186_, v___x_192_, v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_a_173_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___boxed(lean_object* v_x_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(v_x_228_, v_a_229_, v_a_230_);
lean_dec_ref(v_a_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Vector_unexpandMk(lean_object* v_x_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4));
lean_inc(v_x_232_);
v___x_236_ = l_Lean_Syntax_isOfKind(v_x_232_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v_x_232_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_a_234_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = l_Lean_Syntax_getArg(v_x_232_, v___x_239_);
lean_dec(v_x_232_);
v___x_241_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_240_);
v___x_242_ = l_Lean_Syntax_matchesNull(v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v_a_234_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = l_Lean_Syntax_getArg(v___x_240_, v___x_245_);
lean_dec(v___x_240_);
v___x_247_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24));
lean_inc(v___x_246_);
v___x_248_ = l_Lean_Syntax_isOfKind(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v_a_234_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_251_ = l_Lean_Syntax_getArg(v___x_246_, v___x_239_);
lean_dec(v___x_246_);
v___x_252_ = l_Lean_Syntax_getArgs(v___x_251_);
lean_dec(v___x_251_);
v___x_253_ = 0;
v___x_254_ = l_Lean_SourceInfo_fromRef(v_a_233_, v___x_253_);
v___x_255_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__2));
v___x_256_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__5));
lean_inc_n(v___x_254_, 3);
v___x_257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_254_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_259_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
v___x_260_ = l_Array_append___redArg(v___x_259_, v___x_252_);
lean_dec_ref(v___x_252_);
v___x_261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_261_, 0, v___x_254_);
lean_ctor_set(v___x_261_, 1, v___x_258_);
lean_ctor_set(v___x_261_, 2, v___x_260_);
v___x_262_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__18));
v___x_263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_254_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = l_Lean_Syntax_node3(v___x_254_, v___x_255_, v___x_257_, v___x_261_, v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_a_234_);
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unexpandMk___boxed(lean_object* v_x_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Vector_unexpandMk(v_x_266_, v_a_267_, v_a_268_);
lean_dec(v_a_267_);
return v_res_269_;
}
}
static lean_object* _init_l_Vector_Vector_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__5));
v___x_276_ = lean_string_length(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Vector_Vector_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_obj_once(&l_Vector_Vector_repr___redArg___closed__2, &l_Vector_Vector_repr___redArg___closed__2_once, _init_l_Vector_Vector_repr___redArg___closed__2);
v___x_278_ = lean_nat_to_int(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr___redArg(lean_object* v_inst_286_, lean_object* v_n_287_, lean_object* v_xs_288_){
_start:
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_nat_dec_eq(v_n_287_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v_x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_x_291_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_291_, 0, lean_box(0));
lean_closure_set(v_x_291_, 1, v_inst_286_);
v___x_292_ = lean_array_to_list(v_xs_288_);
v___x_293_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__1));
v___x_294_ = l_Std_Format_joinSep___redArg(v_x_291_, v___x_292_, v___x_293_);
v___x_295_ = lean_obj_once(&l_Vector_Vector_repr___redArg___closed__3, &l_Vector_Vector_repr___redArg___closed__3_once, _init_l_Vector_Vector_repr___redArg___closed__3);
v___x_296_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__4));
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_294_);
v___x_298_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__5));
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_295_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Std_Format_fill(v___x_300_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
lean_dec_ref(v_xs_288_);
lean_dec_ref(v_inst_286_);
v___x_302_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__7));
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr___redArg___boxed(lean_object* v_inst_303_, lean_object* v_n_304_, lean_object* v_xs_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Vector_Vector_repr___redArg(v_inst_303_, v_n_304_, v_xs_305_);
lean_dec(v_n_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr(lean_object* v_00_u03b1_307_, lean_object* v_inst_308_, lean_object* v_n_309_, lean_object* v_xs_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Vector_Vector_repr___redArg(v_inst_308_, v_n_309_, v_xs_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr___boxed(lean_object* v_00_u03b1_312_, lean_object* v_inst_313_, lean_object* v_n_314_, lean_object* v_xs_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Vector_Vector_repr(v_00_u03b1_312_, v_inst_313_, v_n_314_, v_xs_315_);
lean_dec(v_n_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg___lam__0(lean_object* v_inst_317_, lean_object* v_n_318_, lean_object* v_xs_319_, lean_object* v_x_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Vector_Vector_repr___redArg(v_inst_317_, v_n_318_, v_xs_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg___lam__0___boxed(lean_object* v_inst_322_, lean_object* v_n_323_, lean_object* v_xs_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Vector_Vector_instRepr___redArg___lam__0(v_inst_322_, v_n_323_, v_xs_324_, v_x_325_);
lean_dec(v_x_325_);
lean_dec(v_n_323_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg(lean_object* v_inst_327_, lean_object* v_n_328_){
_start:
{
lean_object* v___f_329_; 
v___f_329_ = lean_alloc_closure((void*)(l_Vector_Vector_instRepr___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_329_, 0, v_inst_327_);
lean_closure_set(v___f_329_, 1, v_n_328_);
return v___f_329_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr(lean_object* v_00_u03b1_330_, lean_object* v_inst_331_, lean_object* v_n_332_){
_start:
{
lean_object* v___f_333_; 
v___f_333_ = lean_alloc_closure((void*)(l_Vector_Vector_instRepr___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_333_, 0, v_inst_331_);
lean_closure_set(v___f_333_, 1, v_n_332_);
return v___f_333_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList___redArg(lean_object* v_xs_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_array_to_list(v_xs_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList(lean_object* v_00_u03b1_336_, lean_object* v_n_337_, lean_object* v_xs_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_array_to_list(v_xs_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList___boxed(lean_object* v_00_u03b1_340_, lean_object* v_n_341_, lean_object* v_xs_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Vector_toList(v_00_u03b1_340_, v_n_341_, v_xs_342_);
lean_dec(v_n_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray___redArg(lean_object* v_mk_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = lean_apply_2(v_mk_344_, v_x_345_, lean_box(0));
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray(lean_object* v_00_u03b1_347_, lean_object* v_n_348_, lean_object* v_motive_349_, lean_object* v_mk_350_, lean_object* v_x_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_apply_2(v_mk_350_, v_x_351_, lean_box(0));
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray___boxed(lean_object* v_00_u03b1_353_, lean_object* v_n_354_, lean_object* v_motive_355_, lean_object* v_mk_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Vector_elimAsArray(v_00_u03b1_353_, v_n_354_, v_motive_355_, v_mk_356_, v_x_357_);
lean_dec(v_n_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList___redArg(lean_object* v_mk_359_, lean_object* v_x_360_){
_start:
{
lean_object* v_toList_361_; lean_object* v___x_362_; 
v_toList_361_ = lean_array_to_list(v_x_360_);
v___x_362_ = lean_apply_2(v_mk_359_, v_toList_361_, lean_box(0));
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList(lean_object* v_00_u03b1_363_, lean_object* v_n_364_, lean_object* v_motive_365_, lean_object* v_mk_366_, lean_object* v_x_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Vector_elimAsList___redArg(v_mk_366_, v_x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList___boxed(lean_object* v_00_u03b1_369_, lean_object* v_n_370_, lean_object* v_motive_371_, lean_object* v_mk_372_, lean_object* v_x_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Vector_elimAsList(v_00_u03b1_369_, v_n_370_, v_motive_371_, v_mk_372_, v_x_373_);
lean_dec(v_n_370_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg(lean_object* v_capacity_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_mk_empty_array_with_capacity(v_capacity_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Vector_emptyWithCapacity___redArg(v_capacity_377_);
lean_dec(v_capacity_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity(lean_object* v_00_u03b1_379_, lean_object* v_capacity_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_mk_empty_array_with_capacity(v_capacity_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___boxed(lean_object* v_00_u03b1_382_, lean_object* v_capacity_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Vector_emptyWithCapacity(v_00_u03b1_382_, v_capacity_383_);
lean_dec(v_capacity_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Vector_replicate___redArg(lean_object* v_n_385_, lean_object* v_v_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_mk_array(v_n_385_, v_v_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Vector_replicate(lean_object* v_00_u03b1_388_, lean_object* v_n_389_, lean_object* v_v_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_mk_array(v_n_389_, v_v_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Vector_singleton___redArg(lean_object* v_v_392_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_mk_empty_array_with_capacity(v___x_393_);
v___x_395_ = lean_array_push(v___x_394_, v_v_392_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Vector_singleton(lean_object* v_00_u03b1_396_, lean_object* v_v_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_mk_empty_array_with_capacity(v___x_398_);
v___x_400_ = lean_array_push(v___x_399_, v_v_397_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Vector_instInhabited___redArg(lean_object* v_n_401_, lean_object* v_inst_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_mk_array(v_n_401_, v_inst_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Vector_instInhabited(lean_object* v_00_u03b1_404_, lean_object* v_n_405_, lean_object* v_inst_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_mk_array(v_n_405_, v_inst_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___redArg(lean_object* v_xs_408_, lean_object* v_i_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_array_fget_borrowed(v_xs_408_, v_i_409_);
lean_inc(v___x_410_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___redArg___boxed(lean_object* v_xs_411_, lean_object* v_i_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Vector_get___redArg(v_xs_411_, v_i_412_);
lean_dec(v_i_412_);
lean_dec_ref(v_xs_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Vector_get(lean_object* v_00_u03b1_414_, lean_object* v_n_415_, lean_object* v_xs_416_, lean_object* v_i_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_array_fget_borrowed(v_xs_416_, v_i_417_);
lean_inc(v___x_418_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___boxed(lean_object* v_00_u03b1_419_, lean_object* v_n_420_, lean_object* v_xs_421_, lean_object* v_i_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Vector_get(v_00_u03b1_419_, v_n_420_, v_xs_421_, v_i_422_);
lean_dec(v_i_422_);
lean_dec_ref(v_xs_421_);
lean_dec(v_n_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___redArg(lean_object* v_xs_424_, size_t v_i_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_array_uget_borrowed(v_xs_424_, v_i_425_);
lean_inc(v___x_426_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___redArg___boxed(lean_object* v_xs_427_, lean_object* v_i_428_){
_start:
{
size_t v_i_boxed_429_; lean_object* v_res_430_; 
v_i_boxed_429_ = lean_unbox_usize(v_i_428_);
lean_dec(v_i_428_);
v_res_430_ = l_Vector_uget___redArg(v_xs_427_, v_i_boxed_429_);
lean_dec_ref(v_xs_427_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget(lean_object* v_00_u03b1_431_, lean_object* v_n_432_, lean_object* v_xs_433_, size_t v_i_434_, lean_object* v_h_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_array_uget_borrowed(v_xs_433_, v_i_434_);
lean_inc(v___x_436_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___boxed(lean_object* v_00_u03b1_437_, lean_object* v_n_438_, lean_object* v_xs_439_, lean_object* v_i_440_, lean_object* v_h_441_){
_start:
{
size_t v_i_boxed_442_; lean_object* v_res_443_; 
v_i_boxed_442_ = lean_unbox_usize(v_i_440_);
lean_dec(v_i_440_);
v_res_443_ = l_Vector_uget(v_00_u03b1_437_, v_n_438_, v_xs_439_, v_i_boxed_442_, v_h_441_);
lean_dec_ref(v_xs_439_);
lean_dec(v_n_438_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___lam__0(lean_object* v_xs_444_, lean_object* v_i_445_, lean_object* v_h_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_array_fget_borrowed(v_xs_444_, v_i_445_);
lean_inc(v___x_447_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___lam__0___boxed(lean_object* v_xs_448_, lean_object* v_i_449_, lean_object* v_h_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Vector_instGetElemNatLt___redArg___lam__0(v_xs_448_, v_i_449_, v_h_450_);
lean_dec(v_i_449_);
lean_dec_ref(v_xs_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg(){
_start:
{
lean_object* v___f_454_; 
v___f_454_ = ((lean_object*)(l_Vector_instGetElemNatLt___redArg___closed__0));
return v___f_454_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___boxed(lean_object* v___dummy_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Vector_instGetElemNatLt___redArg();
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt(lean_object* v_00_u03b1_457_, lean_object* v_n_458_){
_start:
{
lean_object* v___f_459_; 
v___f_459_ = ((lean_object*)(l_Vector_instGetElemNatLt___redArg___closed__0));
return v___f_459_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___boxed(lean_object* v_00_u03b1_460_, lean_object* v_n_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Vector_instGetElemNatLt(v_00_u03b1_460_, v_n_461_);
lean_dec(v_n_461_);
return v_res_462_;
}
}
LEAN_EXPORT uint8_t l_Vector_contains___redArg(lean_object* v_inst_463_, lean_object* v_xs_464_, lean_object* v_a_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = l_Array_contains___redArg(v_inst_463_, v_xs_464_, v_a_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Vector_contains___redArg___boxed(lean_object* v_inst_467_, lean_object* v_xs_468_, lean_object* v_a_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Vector_contains___redArg(v_inst_467_, v_xs_468_, v_a_469_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT uint8_t l_Vector_contains(lean_object* v_00_u03b1_472_, lean_object* v_n_473_, lean_object* v_inst_474_, lean_object* v_xs_475_, lean_object* v_a_476_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = l_Array_contains___redArg(v_inst_474_, v_xs_475_, v_a_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Vector_contains___boxed(lean_object* v_00_u03b1_478_, lean_object* v_n_479_, lean_object* v_inst_480_, lean_object* v_xs_481_, lean_object* v_a_482_){
_start:
{
uint8_t v_res_483_; lean_object* v_r_484_; 
v_res_483_ = l_Vector_contains(v_00_u03b1_478_, v_n_479_, v_inst_480_, v_xs_481_, v_a_482_);
lean_dec(v_n_479_);
v_r_484_ = lean_box(v_res_483_);
return v_r_484_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership___redArg(){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = lean_box(0);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership___redArg___boxed(lean_object* v___dummy_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Vector_instMembership___redArg();
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership(lean_object* v_00_u03b1_489_, lean_object* v_n_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = lean_box(0);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership___boxed(lean_object* v_00_u03b1_492_, lean_object* v_n_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Vector_instMembership(v_00_u03b1_492_, v_n_493_);
lean_dec(v_n_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg(lean_object* v_xs_495_, lean_object* v_i_496_, lean_object* v_default_497_){
_start:
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = lean_array_get_size(v_xs_495_);
v___x_499_ = lean_nat_dec_lt(v_i_496_, v___x_498_);
if (v___x_499_ == 0)
{
lean_inc(v_default_497_);
return v_default_497_;
}
else
{
lean_object* v___x_500_; 
v___x_500_ = lean_array_fget_borrowed(v_xs_495_, v_i_496_);
lean_inc(v___x_500_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg___boxed(lean_object* v_xs_501_, lean_object* v_i_502_, lean_object* v_default_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Vector_getD___redArg(v_xs_501_, v_i_502_, v_default_503_);
lean_dec(v_default_503_);
lean_dec(v_i_502_);
lean_dec_ref(v_xs_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD(lean_object* v_00_u03b1_505_, lean_object* v_n_506_, lean_object* v_xs_507_, lean_object* v_i_508_, lean_object* v_default_509_){
_start:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_array_get_size(v_xs_507_);
v___x_511_ = lean_nat_dec_lt(v_i_508_, v___x_510_);
if (v___x_511_ == 0)
{
lean_inc(v_default_509_);
return v_default_509_;
}
else
{
lean_object* v___x_512_; 
v___x_512_ = lean_array_fget_borrowed(v_xs_507_, v_i_508_);
lean_inc(v___x_512_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___boxed(lean_object* v_00_u03b1_513_, lean_object* v_n_514_, lean_object* v_xs_515_, lean_object* v_i_516_, lean_object* v_default_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Vector_getD(v_00_u03b1_513_, v_n_514_, v_xs_515_, v_i_516_, v_default_517_);
lean_dec(v_default_517_);
lean_dec(v_i_516_);
lean_dec_ref(v_xs_515_);
lean_dec(v_n_514_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg(lean_object* v_inst_519_, lean_object* v_xs_520_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_521_ = lean_array_get_size(v_xs_520_);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_sub(v___x_521_, v___x_522_);
v___x_524_ = lean_array_get_borrowed(v_inst_519_, v_xs_520_, v___x_523_);
lean_dec(v___x_523_);
lean_inc(v___x_524_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg___boxed(lean_object* v_inst_525_, lean_object* v_xs_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Vector_back_x21___redArg(v_inst_525_, v_xs_526_);
lean_dec_ref(v_xs_526_);
lean_dec(v_inst_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21(lean_object* v_00_u03b1_528_, lean_object* v_n_529_, lean_object* v_inst_530_, lean_object* v_xs_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_532_ = lean_array_get_size(v_xs_531_);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_sub(v___x_532_, v___x_533_);
v___x_535_ = lean_array_get_borrowed(v_inst_530_, v_xs_531_, v___x_534_);
lean_dec(v___x_534_);
lean_inc(v___x_535_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___boxed(lean_object* v_00_u03b1_536_, lean_object* v_n_537_, lean_object* v_inst_538_, lean_object* v_xs_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Vector_back_x21(v_00_u03b1_536_, v_n_537_, v_inst_538_, v_xs_539_);
lean_dec_ref(v_xs_539_);
lean_dec(v_inst_538_);
lean_dec(v_n_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg(lean_object* v_xs_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_542_ = lean_array_get_size(v_xs_541_);
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_sub(v___x_542_, v___x_543_);
v___x_545_ = lean_nat_dec_lt(v___x_544_, v___x_542_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec(v___x_544_);
v___x_546_ = lean_box(0);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_array_fget_borrowed(v_xs_541_, v___x_544_);
lean_dec(v___x_544_);
lean_inc(v___x_547_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg___boxed(lean_object* v_xs_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Vector_back_x3f___redArg(v_xs_549_);
lean_dec_ref(v_xs_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f(lean_object* v_00_u03b1_551_, lean_object* v_n_552_, lean_object* v_xs_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_554_ = lean_array_get_size(v_xs_553_);
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_sub(v___x_554_, v___x_555_);
v___x_557_ = lean_nat_dec_lt(v___x_556_, v___x_554_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec(v___x_556_);
v___x_558_ = lean_box(0);
return v___x_558_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_array_fget_borrowed(v_xs_553_, v___x_556_);
lean_dec(v___x_556_);
lean_inc(v___x_559_);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___boxed(lean_object* v_00_u03b1_561_, lean_object* v_n_562_, lean_object* v_xs_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Vector_back_x3f(v_00_u03b1_561_, v_n_562_, v_xs_563_);
lean_dec_ref(v_xs_563_);
lean_dec(v_n_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg(lean_object* v_n_565_, lean_object* v_xs_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_sub(v_n_565_, v___x_567_);
v___x_569_ = lean_array_fget_borrowed(v_xs_566_, v___x_568_);
lean_dec(v___x_568_);
lean_inc(v___x_569_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg___boxed(lean_object* v_n_570_, lean_object* v_xs_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Vector_back___redArg(v_n_570_, v_xs_571_);
lean_dec_ref(v_xs_571_);
lean_dec(v_n_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Vector_back(lean_object* v_n_573_, lean_object* v_00_u03b1_574_, lean_object* v_inst_575_, lean_object* v_xs_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_sub(v_n_573_, v___x_577_);
v___x_579_ = lean_array_fget_borrowed(v_xs_576_, v___x_578_);
lean_dec(v___x_578_);
lean_inc(v___x_579_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___boxed(lean_object* v_n_580_, lean_object* v_00_u03b1_581_, lean_object* v_inst_582_, lean_object* v_xs_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Vector_back(v_n_580_, v_00_u03b1_581_, v_inst_582_, v_xs_583_);
lean_dec_ref(v_xs_583_);
lean_dec(v_n_580_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg(lean_object* v_xs_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_array_fget_borrowed(v_xs_585_, v___x_586_);
lean_inc(v___x_587_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg___boxed(lean_object* v_xs_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Vector_head___redArg(v_xs_588_);
lean_dec_ref(v_xs_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Vector_head(lean_object* v_n_590_, lean_object* v_00_u03b1_591_, lean_object* v_inst_592_, lean_object* v_xs_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_array_fget_borrowed(v_xs_593_, v___x_594_);
lean_inc(v___x_595_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___boxed(lean_object* v_n_596_, lean_object* v_00_u03b1_597_, lean_object* v_inst_598_, lean_object* v_xs_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Vector_head(v_n_596_, v_00_u03b1_597_, v_inst_598_, v_xs_599_);
lean_dec_ref(v_xs_599_);
lean_dec(v_n_596_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___redArg(lean_object* v_xs_601_, lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_array_push(v_xs_601_, v_x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Vector_push(lean_object* v_00_u03b1_604_, lean_object* v_n_605_, lean_object* v_xs_606_, lean_object* v_x_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_array_push(v_xs_606_, v_x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___boxed(lean_object* v_00_u03b1_609_, lean_object* v_n_610_, lean_object* v_xs_611_, lean_object* v_x_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Vector_push(v_00_u03b1_609_, v_n_610_, v_xs_611_, v_x_612_);
lean_dec(v_n_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___redArg(lean_object* v_xs_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_pop(v_xs_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop(lean_object* v_00_u03b1_616_, lean_object* v_n_617_, lean_object* v_xs_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = lean_array_pop(v_xs_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___boxed(lean_object* v_00_u03b1_620_, lean_object* v_n_621_, lean_object* v_xs_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Vector_pop(v_00_u03b1_620_, v_n_621_, v_xs_622_);
lean_dec(v_n_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear___redArg(lean_object* v_xs_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_array_mark_linear(v_xs_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear(lean_object* v_00_u03b1_626_, lean_object* v_n_627_, lean_object* v_xs_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_array_mark_linear(v_xs_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear___boxed(lean_object* v_00_u03b1_630_, lean_object* v_n_631_, lean_object* v_xs_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Vector_markLinear(v_00_u03b1_630_, v_n_631_, v_xs_632_);
lean_dec(v_n_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg(lean_object* v_xs_634_, lean_object* v_ys_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = lean_array_propagate_mark(v_xs_634_, v_ys_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg___boxed(lean_object* v_xs_637_, lean_object* v_ys_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Vector_propagateMark___redArg(v_xs_637_, v_ys_638_);
lean_dec_ref(v_xs_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark(lean_object* v_n_640_, lean_object* v_m_641_, lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_xs_644_, lean_object* v_ys_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_array_propagate_mark(v_xs_644_, v_ys_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___boxed(lean_object* v_n_647_, lean_object* v_m_648_, lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_xs_651_, lean_object* v_ys_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Vector_propagateMark(v_n_647_, v_m_648_, v_00_u03b1_649_, v_00_u03b2_650_, v_xs_651_, v_ys_652_);
lean_dec_ref(v_xs_651_);
lean_dec(v_m_648_);
lean_dec(v_n_647_);
return v_res_653_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__9(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Vector_set___auto__1___closed__8));
v___x_674_ = l_Lean_mkAtom(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__10(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_obj_once(&l_Vector_set___auto__1___closed__9, &l_Vector_set___auto__1___closed__9_once, _init_l_Vector_set___auto__1___closed__9);
v___x_676_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_677_ = lean_array_push(v___x_676_, v___x_675_);
return v___x_677_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__11(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_678_ = lean_obj_once(&l_Vector_set___auto__1___closed__10, &l_Vector_set___auto__1___closed__10_once, _init_l_Vector_set___auto__1___closed__10);
v___x_679_ = ((lean_object*)(l_Vector_set___auto__1___closed__7));
v___x_680_ = lean_box(2);
v___x_681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
lean_ctor_set(v___x_681_, 2, v___x_678_);
return v___x_681_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__12(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_obj_once(&l_Vector_set___auto__1___closed__11, &l_Vector_set___auto__1___closed__11_once, _init_l_Vector_set___auto__1___closed__11);
v___x_683_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_684_ = lean_array_push(v___x_683_, v___x_682_);
return v___x_684_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__13(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = lean_obj_once(&l_Vector_set___auto__1___closed__12, &l_Vector_set___auto__1___closed__12_once, _init_l_Vector_set___auto__1___closed__12);
v___x_686_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_687_ = lean_box(2);
v___x_688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_686_);
lean_ctor_set(v___x_688_, 2, v___x_685_);
return v___x_688_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__14(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_obj_once(&l_Vector_set___auto__1___closed__13, &l_Vector_set___auto__1___closed__13_once, _init_l_Vector_set___auto__1___closed__13);
v___x_690_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_691_ = lean_array_push(v___x_690_, v___x_689_);
return v___x_691_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__15(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_692_ = lean_obj_once(&l_Vector_set___auto__1___closed__14, &l_Vector_set___auto__1___closed__14_once, _init_l_Vector_set___auto__1___closed__14);
v___x_693_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_694_ = lean_box(2);
v___x_695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_693_);
lean_ctor_set(v___x_695_, 2, v___x_692_);
return v___x_695_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__16(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_obj_once(&l_Vector_set___auto__1___closed__15, &l_Vector_set___auto__1___closed__15_once, _init_l_Vector_set___auto__1___closed__15);
v___x_697_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_698_ = lean_array_push(v___x_697_, v___x_696_);
return v___x_698_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__17(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = lean_obj_once(&l_Vector_set___auto__1___closed__16, &l_Vector_set___auto__1___closed__16_once, _init_l_Vector_set___auto__1___closed__16);
v___x_700_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_701_ = lean_box(2);
v___x_702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
lean_ctor_set(v___x_702_, 2, v___x_699_);
return v___x_702_;
}
}
static lean_object* _init_l_Vector_set___auto__1(void){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg(lean_object* v_xs_704_, lean_object* v_i_705_, lean_object* v_x_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_array_fset(v_xs_704_, v_i_705_, v_x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg___boxed(lean_object* v_xs_708_, lean_object* v_i_709_, lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Vector_set___redArg(v_xs_708_, v_i_709_, v_x_710_);
lean_dec(v_i_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Vector_set(lean_object* v_00_u03b1_712_, lean_object* v_n_713_, lean_object* v_xs_714_, lean_object* v_i_715_, lean_object* v_x_716_, lean_object* v_h_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_array_fset(v_xs_714_, v_i_715_, v_x_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___boxed(lean_object* v_00_u03b1_719_, lean_object* v_n_720_, lean_object* v_xs_721_, lean_object* v_i_722_, lean_object* v_x_723_, lean_object* v_h_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Vector_set(v_00_u03b1_719_, v_n_720_, v_xs_721_, v_i_722_, v_x_723_, v_h_724_);
lean_dec(v_i_722_);
lean_dec(v_n_720_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg(lean_object* v_xs_726_, lean_object* v_i_727_, lean_object* v_x_728_){
_start:
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = lean_array_get_size(v_xs_726_);
v___x_730_ = lean_nat_dec_lt(v_i_727_, v___x_729_);
if (v___x_730_ == 0)
{
lean_dec(v_x_728_);
return v_xs_726_;
}
else
{
lean_object* v___x_731_; 
v___x_731_ = lean_array_fset(v_xs_726_, v_i_727_, v_x_728_);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg___boxed(lean_object* v_xs_732_, lean_object* v_i_733_, lean_object* v_x_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Vector_setIfInBounds___redArg(v_xs_732_, v_i_733_, v_x_734_);
lean_dec(v_i_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds(lean_object* v_00_u03b1_736_, lean_object* v_n_737_, lean_object* v_xs_738_, lean_object* v_i_739_, lean_object* v_x_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_xs_738_);
v___x_742_ = lean_nat_dec_lt(v_i_739_, v___x_741_);
if (v___x_742_ == 0)
{
lean_dec(v_x_740_);
return v_xs_738_;
}
else
{
lean_object* v___x_743_; 
v___x_743_ = lean_array_fset(v_xs_738_, v_i_739_, v_x_740_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___boxed(lean_object* v_00_u03b1_744_, lean_object* v_n_745_, lean_object* v_xs_746_, lean_object* v_i_747_, lean_object* v_x_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Vector_setIfInBounds(v_00_u03b1_744_, v_n_745_, v_xs_746_, v_i_747_, v_x_748_);
lean_dec(v_i_747_);
lean_dec(v_n_745_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg(lean_object* v_xs_750_, lean_object* v_i_751_, lean_object* v_x_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = lean_array_set(v_xs_750_, v_i_751_, v_x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg___boxed(lean_object* v_xs_754_, lean_object* v_i_755_, lean_object* v_x_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Vector_set_x21___redArg(v_xs_754_, v_i_755_, v_x_756_);
lean_dec(v_i_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21(lean_object* v_00_u03b1_758_, lean_object* v_n_759_, lean_object* v_xs_760_, lean_object* v_i_761_, lean_object* v_x_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = lean_array_set(v_xs_760_, v_i_761_, v_x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___boxed(lean_object* v_00_u03b1_764_, lean_object* v_n_765_, lean_object* v_xs_766_, lean_object* v_i_767_, lean_object* v_x_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Vector_set_x21(v_00_u03b1_764_, v_n_765_, v_xs_766_, v_i_767_, v_x_768_);
lean_dec(v_i_767_);
lean_dec(v_n_765_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___redArg(lean_object* v_inst_770_, lean_object* v_f_771_, lean_object* v_b_772_, lean_object* v_xs_773_){
_start:
{
lean_object* v_toApplicative_774_; lean_object* v_toPure_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_toApplicative_774_ = lean_ctor_get(v_inst_770_, 0);
v_toPure_775_ = lean_ctor_get(v_toApplicative_774_, 1);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_array_get_size(v_xs_773_);
v___x_778_ = lean_nat_dec_lt(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
lean_inc(v_toPure_775_);
lean_dec_ref(v_xs_773_);
lean_dec(v_f_771_);
lean_dec_ref(v_inst_770_);
v___x_779_ = lean_apply_2(v_toPure_775_, lean_box(0), v_b_772_);
return v___x_779_;
}
else
{
uint8_t v___x_780_; 
v___x_780_ = lean_nat_dec_le(v___x_777_, v___x_777_);
if (v___x_780_ == 0)
{
if (v___x_778_ == 0)
{
lean_object* v___x_781_; 
lean_inc(v_toPure_775_);
lean_dec_ref(v_xs_773_);
lean_dec(v_f_771_);
lean_dec_ref(v_inst_770_);
v___x_781_ = lean_apply_2(v_toPure_775_, lean_box(0), v_b_772_);
return v___x_781_;
}
else
{
size_t v___x_782_; size_t v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((size_t)0ULL);
v___x_783_ = lean_usize_of_nat(v___x_777_);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_770_, v_f_771_, v_xs_773_, v___x_782_, v___x_783_, v_b_772_);
return v___x_784_;
}
}
else
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_of_nat(v___x_777_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_770_, v_f_771_, v_xs_773_, v___x_785_, v___x_786_, v_b_772_);
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM(lean_object* v_m_788_, lean_object* v_00_u03b2_789_, lean_object* v_00_u03b1_790_, lean_object* v_n_791_, lean_object* v_inst_792_, lean_object* v_f_793_, lean_object* v_b_794_, lean_object* v_xs_795_){
_start:
{
lean_object* v_toApplicative_796_; lean_object* v_toPure_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_toApplicative_796_ = lean_ctor_get(v_inst_792_, 0);
v_toPure_797_ = lean_ctor_get(v_toApplicative_796_, 1);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_array_get_size(v_xs_795_);
v___x_800_ = lean_nat_dec_lt(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
lean_inc(v_toPure_797_);
lean_dec_ref(v_xs_795_);
lean_dec(v_f_793_);
lean_dec_ref(v_inst_792_);
v___x_801_ = lean_apply_2(v_toPure_797_, lean_box(0), v_b_794_);
return v___x_801_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = lean_nat_dec_le(v___x_799_, v___x_799_);
if (v___x_802_ == 0)
{
if (v___x_800_ == 0)
{
lean_object* v___x_803_; 
lean_inc(v_toPure_797_);
lean_dec_ref(v_xs_795_);
lean_dec(v_f_793_);
lean_dec_ref(v_inst_792_);
v___x_803_ = lean_apply_2(v_toPure_797_, lean_box(0), v_b_794_);
return v___x_803_;
}
else
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((size_t)0ULL);
v___x_805_ = lean_usize_of_nat(v___x_799_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_792_, v_f_793_, v_xs_795_, v___x_804_, v___x_805_, v_b_794_);
return v___x_806_;
}
}
else
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_807_ = ((size_t)0ULL);
v___x_808_ = lean_usize_of_nat(v___x_799_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_792_, v_f_793_, v_xs_795_, v___x_807_, v___x_808_, v_b_794_);
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___boxed(lean_object* v_m_810_, lean_object* v_00_u03b2_811_, lean_object* v_00_u03b1_812_, lean_object* v_n_813_, lean_object* v_inst_814_, lean_object* v_f_815_, lean_object* v_b_816_, lean_object* v_xs_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Vector_foldlM(v_m_810_, v_00_u03b2_811_, v_00_u03b1_812_, v_n_813_, v_inst_814_, v_f_815_, v_b_816_, v_xs_817_);
lean_dec(v_n_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___redArg(lean_object* v_inst_819_, lean_object* v_f_820_, lean_object* v_b_821_, lean_object* v_xs_822_){
_start:
{
lean_object* v_toApplicative_823_; lean_object* v_toPure_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_toApplicative_823_ = lean_ctor_get(v_inst_819_, 0);
v_toPure_824_ = lean_ctor_get(v_toApplicative_823_, 1);
v___x_825_ = lean_array_get_size(v_xs_822_);
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_nat_dec_lt(v___x_826_, v___x_825_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_inc(v_toPure_824_);
lean_dec_ref(v_xs_822_);
lean_dec(v_f_820_);
lean_dec_ref(v_inst_819_);
v___x_828_ = lean_apply_2(v_toPure_824_, lean_box(0), v_b_821_);
return v___x_828_;
}
else
{
size_t v___x_829_; size_t v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_usize_of_nat(v___x_825_);
v___x_830_ = ((size_t)0ULL);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_819_, v_f_820_, v_xs_822_, v___x_829_, v___x_830_, v_b_821_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM(lean_object* v_m_832_, lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_n_835_, lean_object* v_inst_836_, lean_object* v_f_837_, lean_object* v_b_838_, lean_object* v_xs_839_){
_start:
{
lean_object* v_toApplicative_840_; lean_object* v_toPure_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_toApplicative_840_ = lean_ctor_get(v_inst_836_, 0);
v_toPure_841_ = lean_ctor_get(v_toApplicative_840_, 1);
v___x_842_ = lean_array_get_size(v_xs_839_);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_nat_dec_lt(v___x_843_, v___x_842_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
lean_inc(v_toPure_841_);
lean_dec_ref(v_xs_839_);
lean_dec(v_f_837_);
lean_dec_ref(v_inst_836_);
v___x_845_ = lean_apply_2(v_toPure_841_, lean_box(0), v_b_838_);
return v___x_845_;
}
else
{
size_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_usize_of_nat(v___x_842_);
v___x_847_ = ((size_t)0ULL);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_836_, v_f_837_, v_xs_839_, v___x_846_, v___x_847_, v_b_838_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___boxed(lean_object* v_m_849_, lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_n_852_, lean_object* v_inst_853_, lean_object* v_f_854_, lean_object* v_b_855_, lean_object* v_xs_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Vector_foldrM(v_m_849_, v_00_u03b1_850_, v_00_u03b2_851_, v_n_852_, v_inst_853_, v_f_854_, v_b_855_, v_xs_856_);
lean_dec(v_n_852_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg___lam__0(lean_object* v_f_858_, lean_object* v_x1_859_, lean_object* v_x2_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = lean_apply_2(v_f_858_, v_x1_859_, v_x2_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg(lean_object* v_f_881_, lean_object* v_b_882_, lean_object* v_xs_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_array_get_size(v_xs_883_);
v___x_886_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_887_ = lean_nat_dec_lt(v___x_884_, v___x_885_);
if (v___x_887_ == 0)
{
lean_dec_ref(v_xs_883_);
lean_dec(v_f_881_);
return v_b_882_;
}
else
{
lean_object* v___f_888_; uint8_t v___x_889_; 
v___f_888_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_888_, 0, v_f_881_);
v___x_889_ = lean_nat_dec_le(v___x_885_, v___x_885_);
if (v___x_889_ == 0)
{
if (v___x_887_ == 0)
{
lean_dec_ref(v___f_888_);
lean_dec_ref(v_xs_883_);
return v_b_882_;
}
else
{
size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v___x_890_ = ((size_t)0ULL);
v___x_891_ = lean_usize_of_nat(v___x_885_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_886_, v___f_888_, v_xs_883_, v___x_890_, v___x_891_, v_b_882_);
return v___x_892_;
}
}
else
{
size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; 
v___x_893_ = ((size_t)0ULL);
v___x_894_ = lean_usize_of_nat(v___x_885_);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_886_, v___f_888_, v_xs_883_, v___x_893_, v___x_894_, v_b_882_);
return v___x_895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl(lean_object* v_00_u03b2_896_, lean_object* v_00_u03b1_897_, lean_object* v_n_898_, lean_object* v_f_899_, lean_object* v_b_900_, lean_object* v_xs_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_array_get_size(v_xs_901_);
v___x_904_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_905_ = lean_nat_dec_lt(v___x_902_, v___x_903_);
if (v___x_905_ == 0)
{
lean_dec_ref(v_xs_901_);
lean_dec(v_f_899_);
return v_b_900_;
}
else
{
lean_object* v___f_906_; uint8_t v___x_907_; 
v___f_906_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_906_, 0, v_f_899_);
v___x_907_ = lean_nat_dec_le(v___x_903_, v___x_903_);
if (v___x_907_ == 0)
{
if (v___x_905_ == 0)
{
lean_dec_ref(v___f_906_);
lean_dec_ref(v_xs_901_);
return v_b_900_;
}
else
{
size_t v___x_908_; size_t v___x_909_; lean_object* v___x_910_; 
v___x_908_ = ((size_t)0ULL);
v___x_909_ = lean_usize_of_nat(v___x_903_);
v___x_910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_904_, v___f_906_, v_xs_901_, v___x_908_, v___x_909_, v_b_900_);
return v___x_910_;
}
}
else
{
size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v___x_911_ = ((size_t)0ULL);
v___x_912_ = lean_usize_of_nat(v___x_903_);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_904_, v___f_906_, v_xs_901_, v___x_911_, v___x_912_, v_b_900_);
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___boxed(lean_object* v_00_u03b2_914_, lean_object* v_00_u03b1_915_, lean_object* v_n_916_, lean_object* v_f_917_, lean_object* v_b_918_, lean_object* v_xs_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Vector_foldl(v_00_u03b2_914_, v_00_u03b1_915_, v_n_916_, v_f_917_, v_b_918_, v_xs_919_);
lean_dec(v_n_916_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___redArg(lean_object* v_f_921_, lean_object* v_b_922_, lean_object* v_xs_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_924_ = lean_array_get_size(v_xs_923_);
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_927_ = lean_nat_dec_lt(v___x_925_, v___x_924_);
if (v___x_927_ == 0)
{
lean_dec_ref(v_xs_923_);
lean_dec(v_f_921_);
return v_b_922_;
}
else
{
lean_object* v___f_928_; size_t v___x_929_; size_t v___x_930_; lean_object* v___x_931_; 
v___f_928_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_928_, 0, v_f_921_);
v___x_929_ = lean_usize_of_nat(v___x_924_);
v___x_930_ = ((size_t)0ULL);
v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_926_, v___f_928_, v_xs_923_, v___x_929_, v___x_930_, v_b_922_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr(lean_object* v_00_u03b1_932_, lean_object* v_00_u03b2_933_, lean_object* v_n_934_, lean_object* v_f_935_, lean_object* v_b_936_, lean_object* v_xs_937_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_938_ = lean_array_get_size(v_xs_937_);
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_941_ = lean_nat_dec_lt(v___x_939_, v___x_938_);
if (v___x_941_ == 0)
{
lean_dec_ref(v_xs_937_);
lean_dec(v_f_935_);
return v_b_936_;
}
else
{
lean_object* v___f_942_; size_t v___x_943_; size_t v___x_944_; lean_object* v___x_945_; 
v___f_942_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_942_, 0, v_f_935_);
v___x_943_ = lean_usize_of_nat(v___x_938_);
v___x_944_ = ((size_t)0ULL);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_940_, v___f_942_, v_xs_937_, v___x_943_, v___x_944_, v_b_936_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___boxed(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_n_948_, lean_object* v_f_949_, lean_object* v_b_950_, lean_object* v_xs_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Vector_foldr(v_00_u03b1_946_, v_00_u03b2_947_, v_n_948_, v_f_949_, v_b_950_, v_xs_951_);
lean_dec(v_n_948_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg(lean_object* v_xs_953_, lean_object* v_ys_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Array_append___redArg(v_xs_953_, v_ys_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg___boxed(lean_object* v_xs_956_, lean_object* v_ys_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Vector_append___redArg(v_xs_956_, v_ys_957_);
lean_dec_ref(v_ys_957_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Vector_append(lean_object* v_00_u03b1_959_, lean_object* v_n_960_, lean_object* v_m_961_, lean_object* v_xs_962_, lean_object* v_ys_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Array_append___redArg(v_xs_962_, v_ys_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___boxed(lean_object* v_00_u03b1_965_, lean_object* v_n_966_, lean_object* v_m_967_, lean_object* v_xs_968_, lean_object* v_ys_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Vector_append(v_00_u03b1_965_, v_n_966_, v_m_967_, v_xs_968_, v_ys_969_);
lean_dec_ref(v_ys_969_);
lean_dec(v_m_967_);
lean_dec(v_n_966_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat___redArg(lean_object* v_n_971_, lean_object* v_m_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_973_, 0, lean_box(0));
lean_closure_set(v___x_973_, 1, v_n_971_);
lean_closure_set(v___x_973_, 2, v_m_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat(lean_object* v_00_u03b1_974_, lean_object* v_n_975_, lean_object* v_m_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_977_, 0, lean_box(0));
lean_closure_set(v___x_977_, 1, v_n_975_);
lean_closure_set(v___x_977_, 2, v_m_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg(lean_object* v_xs_978_){
_start:
{
lean_inc_ref(v_xs_978_);
return v_xs_978_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg___boxed(lean_object* v_xs_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Vector_cast___redArg(v_xs_979_);
lean_dec_ref(v_xs_979_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast(lean_object* v_n_981_, lean_object* v_m_982_, lean_object* v_00_u03b1_983_, lean_object* v_h_984_, lean_object* v_xs_985_){
_start:
{
lean_inc_ref(v_xs_985_);
return v_xs_985_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___boxed(lean_object* v_n_986_, lean_object* v_m_987_, lean_object* v_00_u03b1_988_, lean_object* v_h_989_, lean_object* v_xs_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Vector_cast(v_n_986_, v_m_987_, v_00_u03b1_988_, v_h_989_, v_xs_990_);
lean_dec_ref(v_xs_990_);
lean_dec(v_m_987_);
lean_dec(v_n_986_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg(lean_object* v_xs_992_, lean_object* v_start_993_, lean_object* v_stop_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Array_extract___redArg(v_xs_992_, v_start_993_, v_stop_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg___boxed(lean_object* v_xs_996_, lean_object* v_start_997_, lean_object* v_stop_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Vector_extract___redArg(v_xs_996_, v_start_997_, v_stop_998_);
lean_dec_ref(v_xs_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract(lean_object* v_00_u03b1_1000_, lean_object* v_n_1001_, lean_object* v_xs_1002_, lean_object* v_start_1003_, lean_object* v_stop_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Array_extract___redArg(v_xs_1002_, v_start_1003_, v_stop_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___boxed(lean_object* v_00_u03b1_1006_, lean_object* v_n_1007_, lean_object* v_xs_1008_, lean_object* v_start_1009_, lean_object* v_stop_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Vector_extract(v_00_u03b1_1006_, v_n_1007_, v_xs_1008_, v_start_1009_, v_stop_1010_);
lean_dec_ref(v_xs_1008_);
lean_dec(v_n_1007_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg(lean_object* v_n_1012_, lean_object* v_xs_1013_, lean_object* v_i_1014_){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = l_Array_extract___redArg(v_xs_1013_, v___x_1015_, v_i_1014_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg___boxed(lean_object* v_n_1017_, lean_object* v_xs_1018_, lean_object* v_i_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Vector_take___redArg(v_n_1017_, v_xs_1018_, v_i_1019_);
lean_dec_ref(v_xs_1018_);
lean_dec(v_n_1017_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Vector_take(lean_object* v_00_u03b1_1021_, lean_object* v_n_1022_, lean_object* v_xs_1023_, lean_object* v_i_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = l_Array_extract___redArg(v_xs_1023_, v___x_1025_, v_i_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___boxed(lean_object* v_00_u03b1_1027_, lean_object* v_n_1028_, lean_object* v_xs_1029_, lean_object* v_i_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Vector_take(v_00_u03b1_1027_, v_n_1028_, v_xs_1029_, v_i_1030_);
lean_dec_ref(v_xs_1029_);
lean_dec(v_n_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg(lean_object* v_xs_1032_, lean_object* v_i_1033_){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_array_get_size(v_xs_1032_);
v___x_1035_ = l_Array_extract___redArg(v_xs_1032_, v_i_1033_, v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg___boxed(lean_object* v_xs_1036_, lean_object* v_i_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Vector_drop___redArg(v_xs_1036_, v_i_1037_);
lean_dec_ref(v_xs_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop(lean_object* v_00_u03b1_1039_, lean_object* v_n_1040_, lean_object* v_xs_1041_, lean_object* v_i_1042_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_array_get_size(v_xs_1041_);
v___x_1044_ = l_Array_extract___redArg(v_xs_1041_, v_i_1042_, v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_n_1046_, lean_object* v_xs_1047_, lean_object* v_i_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Vector_drop(v_00_u03b1_1045_, v_n_1046_, v_xs_1047_, v_i_1048_);
lean_dec_ref(v_xs_1047_);
lean_dec(v_n_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg(lean_object* v_xs_1050_, lean_object* v_i_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Array_shrink___redArg(v_xs_1050_, v_i_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg___boxed(lean_object* v_xs_1053_, lean_object* v_i_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Vector_shrink___redArg(v_xs_1053_, v_i_1054_);
lean_dec(v_i_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink(lean_object* v_00_u03b1_1056_, lean_object* v_n_1057_, lean_object* v_xs_1058_, lean_object* v_i_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Array_shrink___redArg(v_xs_1058_, v_i_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_n_1062_, lean_object* v_xs_1063_, lean_object* v_i_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Vector_shrink(v_00_u03b1_1061_, v_n_1062_, v_xs_1063_, v_i_1064_);
lean_dec(v_i_1064_);
lean_dec(v_n_1062_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg___lam__0(lean_object* v_f_1066_, lean_object* v_x_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_apply_1(v_f_1066_, v_x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg(lean_object* v_f_1069_, lean_object* v_xs_1070_){
_start:
{
lean_object* v___f_1071_; lean_object* v___x_1072_; size_t v_sz_1073_; size_t v___x_1074_; lean_object* v___x_1075_; 
v___f_1071_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1071_, 0, v_f_1069_);
v___x_1072_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1073_ = lean_array_size(v_xs_1070_);
v___x_1074_ = ((size_t)0ULL);
v___x_1075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1072_, v___f_1071_, v_sz_1073_, v___x_1074_, v_xs_1070_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Vector_map(lean_object* v_00_u03b1_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_n_1078_, lean_object* v_f_1079_, lean_object* v_xs_1080_){
_start:
{
lean_object* v___f_1081_; lean_object* v___x_1082_; size_t v_sz_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v___f_1081_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1081_, 0, v_f_1079_);
v___x_1082_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1083_ = lean_array_size(v_xs_1080_);
v___x_1084_ = ((size_t)0ULL);
v___x_1085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1082_, v___f_1081_, v_sz_1083_, v___x_1084_, v_xs_1080_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___boxed(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_n_1088_, lean_object* v_f_1089_, lean_object* v_xs_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Vector_map(v_00_u03b1_1086_, v_00_u03b2_1087_, v_n_1088_, v_f_1089_, v_xs_1090_);
lean_dec(v_n_1088_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg___lam__0(lean_object* v_f_1092_, lean_object* v_i_1093_, lean_object* v_a_1094_, lean_object* v_x_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_apply_2(v_f_1092_, v_i_1093_, v_a_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg(lean_object* v_f_1097_, lean_object* v_xs_1098_){
_start:
{
lean_object* v___f_1099_; lean_object* v___x_1100_; size_t v_sz_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v___f_1099_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1099_, 0, v_f_1097_);
v___x_1100_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1101_ = lean_array_size(v_xs_1098_);
v___x_1102_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1098_);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1100_, v_xs_1098_, v___f_1099_, v_sz_1101_, v___x_1102_, v_xs_1098_);
lean_dec_ref(v_xs_1098_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_n_1106_, lean_object* v_f_1107_, lean_object* v_xs_1108_){
_start:
{
lean_object* v___f_1109_; lean_object* v___x_1110_; size_t v_sz_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v___f_1109_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1109_, 0, v_f_1107_);
v___x_1110_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1111_ = lean_array_size(v_xs_1108_);
v___x_1112_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1108_);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1110_, v_xs_1108_, v___f_1109_, v_sz_1111_, v___x_1112_, v_xs_1108_);
lean_dec_ref(v_xs_1108_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___boxed(lean_object* v_00_u03b1_1114_, lean_object* v_00_u03b2_1115_, lean_object* v_n_1116_, lean_object* v_f_1117_, lean_object* v_xs_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Vector_mapIdx(v_00_u03b1_1114_, v_00_u03b2_1115_, v_n_1116_, v_f_1117_, v_xs_1118_);
lean_dec(v_n_1116_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg___lam__0(lean_object* v_f_1120_, lean_object* v_x1_1121_, lean_object* v_x2_1122_, lean_object* v_x3_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_apply_3(v_f_1120_, v_x1_1121_, v_x2_1122_, lean_box(0));
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg(lean_object* v_xs_1125_, lean_object* v_f_1126_){
_start:
{
lean_object* v___f_1127_; lean_object* v___x_1128_; size_t v_sz_1129_; size_t v___x_1130_; lean_object* v___x_1131_; 
v___f_1127_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1127_, 0, v_f_1126_);
v___x_1128_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1129_ = lean_array_size(v_xs_1125_);
v___x_1130_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1125_);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1128_, v_xs_1125_, v___f_1127_, v_sz_1129_, v___x_1130_, v_xs_1125_);
lean_dec_ref(v_xs_1125_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx(lean_object* v_00_u03b1_1132_, lean_object* v_n_1133_, lean_object* v_00_u03b2_1134_, lean_object* v_xs_1135_, lean_object* v_f_1136_){
_start:
{
lean_object* v___f_1137_; lean_object* v___x_1138_; size_t v_sz_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
v___f_1137_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1137_, 0, v_f_1136_);
v___x_1138_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1139_ = lean_array_size(v_xs_1135_);
v___x_1140_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1135_);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1138_, v_xs_1135_, v___f_1137_, v_sz_1139_, v___x_1140_, v_xs_1135_);
lean_dec_ref(v_xs_1135_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___boxed(lean_object* v_00_u03b1_1142_, lean_object* v_n_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_xs_1145_, lean_object* v_f_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Vector_mapFinIdx(v_00_u03b1_1142_, v_n_1143_, v_00_u03b2_1144_, v_xs_1145_, v_f_1146_);
lean_dec(v_n_1143_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(lean_object* v_k_1148_, lean_object* v_acc_1149_, lean_object* v_n_1150_, lean_object* v_inst_1151_, lean_object* v_f_1152_, lean_object* v_xs_1153_, lean_object* v_____do__lift_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(v_k_1148_, v_acc_1149_, v_n_1150_, v_inst_1151_, v_f_1152_, v_xs_1153_, v_____do__lift_1154_);
lean_dec(v_k_1148_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(lean_object* v_n_1156_, lean_object* v_inst_1157_, lean_object* v_f_1158_, lean_object* v_xs_1159_, lean_object* v_k_1160_, lean_object* v_acc_1161_){
_start:
{
lean_object* v_toApplicative_1162_; lean_object* v_toBind_1163_; lean_object* v_toPure_1164_; uint8_t v___x_1165_; 
v_toApplicative_1162_ = lean_ctor_get(v_inst_1157_, 0);
v_toBind_1163_ = lean_ctor_get(v_inst_1157_, 1);
lean_inc(v_toBind_1163_);
v_toPure_1164_ = lean_ctor_get(v_toApplicative_1162_, 1);
v___x_1165_ = lean_nat_dec_lt(v_k_1160_, v_n_1156_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_inc(v_toPure_1164_);
lean_dec(v_toBind_1163_);
lean_dec(v_k_1160_);
lean_dec_ref(v_xs_1159_);
lean_dec(v_f_1158_);
lean_dec_ref(v_inst_1157_);
lean_dec(v_n_1156_);
v___x_1166_ = lean_apply_2(v_toPure_1164_, lean_box(0), v_acc_1161_);
return v___x_1166_;
}
else
{
lean_object* v___f_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_inc_ref(v_xs_1159_);
lean_inc(v_f_1158_);
lean_inc(v_k_1160_);
v___f_1167_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1167_, 0, v_k_1160_);
lean_closure_set(v___f_1167_, 1, v_acc_1161_);
lean_closure_set(v___f_1167_, 2, v_n_1156_);
lean_closure_set(v___f_1167_, 3, v_inst_1157_);
lean_closure_set(v___f_1167_, 4, v_f_1158_);
lean_closure_set(v___f_1167_, 5, v_xs_1159_);
v___x_1168_ = lean_array_fget(v_xs_1159_, v_k_1160_);
lean_dec(v_k_1160_);
lean_dec_ref(v_xs_1159_);
v___x_1169_ = lean_apply_1(v_f_1158_, v___x_1168_);
v___x_1170_ = lean_apply_4(v_toBind_1163_, lean_box(0), lean_box(0), v___x_1169_, v___f_1167_);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(lean_object* v_k_1171_, lean_object* v_acc_1172_, lean_object* v_n_1173_, lean_object* v_inst_1174_, lean_object* v_f_1175_, lean_object* v_xs_1176_, lean_object* v_____do__lift_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = lean_nat_add(v_k_1171_, v___x_1178_);
v___x_1180_ = lean_array_push(v_acc_1172_, v_____do__lift_1177_);
v___x_1181_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1173_, v_inst_1174_, v_f_1175_, v_xs_1176_, v___x_1179_, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(lean_object* v_m_1182_, lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_n_1185_, lean_object* v_inst_1186_, lean_object* v_f_1187_, lean_object* v_xs_1188_, lean_object* v_k_1189_, lean_object* v_h_1190_, lean_object* v_acc_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1185_, v_inst_1186_, v_f_1187_, v_xs_1188_, v_k_1189_, v_acc_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM___redArg(lean_object* v_n_1195_, lean_object* v_inst_1196_, lean_object* v_f_1197_, lean_object* v_xs_1198_){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_unsigned_to_nat(0u);
v___x_1200_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1201_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1195_, v_inst_1196_, v_f_1197_, v_xs_1198_, v___x_1199_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM(lean_object* v_m_1202_, lean_object* v_00_u03b1_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_n_1205_, lean_object* v_inst_1206_, lean_object* v_f_1207_, lean_object* v_xs_1208_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1211_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1205_, v_inst_1206_, v_f_1207_, v_xs_1208_, v___x_1209_, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg___lam__0(lean_object* v_f_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_apply_1(v_f_1212_, v___y_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg(lean_object* v_inst_1216_, lean_object* v_xs_1217_, lean_object* v_f_1218_){
_start:
{
lean_object* v_toApplicative_1219_; lean_object* v_toPure_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_toApplicative_1219_ = lean_ctor_get(v_inst_1216_, 0);
v_toPure_1220_ = lean_ctor_get(v_toApplicative_1219_, 1);
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_array_get_size(v_xs_1217_);
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_nat_dec_lt(v___x_1221_, v___x_1222_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
lean_inc(v_toPure_1220_);
lean_dec(v_f_1218_);
lean_dec_ref(v_xs_1217_);
lean_dec_ref(v_inst_1216_);
v___x_1225_ = lean_apply_2(v_toPure_1220_, lean_box(0), v___x_1223_);
return v___x_1225_;
}
else
{
lean_object* v___f_1226_; uint8_t v___x_1227_; 
v___f_1226_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1226_, 0, v_f_1218_);
v___x_1227_ = lean_nat_dec_le(v___x_1222_, v___x_1222_);
if (v___x_1227_ == 0)
{
if (v___x_1224_ == 0)
{
lean_object* v___x_1228_; 
lean_inc(v_toPure_1220_);
lean_dec_ref(v___f_1226_);
lean_dec_ref(v_xs_1217_);
lean_dec_ref(v_inst_1216_);
v___x_1228_ = lean_apply_2(v_toPure_1220_, lean_box(0), v___x_1223_);
return v___x_1228_;
}
else
{
size_t v___x_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = lean_usize_of_nat(v___x_1222_);
v___x_1231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1216_, v___f_1226_, v_xs_1217_, v___x_1229_, v___x_1230_, v___x_1223_);
return v___x_1231_;
}
}
else
{
size_t v___x_1232_; size_t v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = ((size_t)0ULL);
v___x_1233_ = lean_usize_of_nat(v___x_1222_);
v___x_1234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1216_, v___f_1226_, v_xs_1217_, v___x_1232_, v___x_1233_, v___x_1223_);
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM(lean_object* v_m_1235_, lean_object* v_00_u03b1_1236_, lean_object* v_n_1237_, lean_object* v_inst_1238_, lean_object* v_xs_1239_, lean_object* v_f_1240_){
_start:
{
lean_object* v_toApplicative_1241_; lean_object* v_toPure_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_toApplicative_1241_ = lean_ctor_get(v_inst_1238_, 0);
v_toPure_1242_ = lean_ctor_get(v_toApplicative_1241_, 1);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_array_get_size(v_xs_1239_);
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_nat_dec_lt(v___x_1243_, v___x_1244_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
lean_inc(v_toPure_1242_);
lean_dec(v_f_1240_);
lean_dec_ref(v_xs_1239_);
lean_dec_ref(v_inst_1238_);
v___x_1247_ = lean_apply_2(v_toPure_1242_, lean_box(0), v___x_1245_);
return v___x_1247_;
}
else
{
lean_object* v___f_1248_; uint8_t v___x_1249_; 
v___f_1248_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1248_, 0, v_f_1240_);
v___x_1249_ = lean_nat_dec_le(v___x_1244_, v___x_1244_);
if (v___x_1249_ == 0)
{
if (v___x_1246_ == 0)
{
lean_object* v___x_1250_; 
lean_inc(v_toPure_1242_);
lean_dec_ref(v___f_1248_);
lean_dec_ref(v_xs_1239_);
lean_dec_ref(v_inst_1238_);
v___x_1250_ = lean_apply_2(v_toPure_1242_, lean_box(0), v___x_1245_);
return v___x_1250_;
}
else
{
size_t v___x_1251_; size_t v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = ((size_t)0ULL);
v___x_1252_ = lean_usize_of_nat(v___x_1244_);
v___x_1253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1238_, v___f_1248_, v_xs_1239_, v___x_1251_, v___x_1252_, v___x_1245_);
return v___x_1253_;
}
}
else
{
size_t v___x_1254_; size_t v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = ((size_t)0ULL);
v___x_1255_ = lean_usize_of_nat(v___x_1244_);
v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1238_, v___f_1248_, v_xs_1239_, v___x_1254_, v___x_1255_, v___x_1245_);
return v___x_1256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM___boxed(lean_object* v_m_1257_, lean_object* v_00_u03b1_1258_, lean_object* v_n_1259_, lean_object* v_inst_1260_, lean_object* v_xs_1261_, lean_object* v_f_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Vector_forM(v_m_1257_, v_00_u03b1_1258_, v_n_1259_, v_inst_1260_, v_xs_1261_, v_f_1262_);
lean_dec(v_n_1259_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(lean_object* v_i_1264_, lean_object* v_acc_1265_, lean_object* v_n_1266_, lean_object* v_inst_1267_, lean_object* v_xs_1268_, lean_object* v_f_1269_, lean_object* v_____do__lift_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(v_i_1264_, v_acc_1265_, v_n_1266_, v_inst_1267_, v_xs_1268_, v_f_1269_, v_____do__lift_1270_);
lean_dec_ref(v_____do__lift_1270_);
lean_dec(v_i_1264_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(lean_object* v_n_1272_, lean_object* v_inst_1273_, lean_object* v_xs_1274_, lean_object* v_f_1275_, lean_object* v_i_1276_, lean_object* v_acc_1277_){
_start:
{
lean_object* v_toApplicative_1278_; lean_object* v_toBind_1279_; lean_object* v_toPure_1280_; uint8_t v___x_1281_; 
v_toApplicative_1278_ = lean_ctor_get(v_inst_1273_, 0);
v_toBind_1279_ = lean_ctor_get(v_inst_1273_, 1);
lean_inc(v_toBind_1279_);
v_toPure_1280_ = lean_ctor_get(v_toApplicative_1278_, 1);
v___x_1281_ = lean_nat_dec_lt(v_i_1276_, v_n_1272_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_inc(v_toPure_1280_);
lean_dec(v_toBind_1279_);
lean_dec(v_i_1276_);
lean_dec(v_f_1275_);
lean_dec_ref(v_xs_1274_);
lean_dec_ref(v_inst_1273_);
lean_dec(v_n_1272_);
v___x_1282_ = lean_apply_2(v_toPure_1280_, lean_box(0), v_acc_1277_);
return v___x_1282_;
}
else
{
lean_object* v___f_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_inc(v_f_1275_);
lean_inc_ref(v_xs_1274_);
lean_inc(v_i_1276_);
v___f_1283_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1283_, 0, v_i_1276_);
lean_closure_set(v___f_1283_, 1, v_acc_1277_);
lean_closure_set(v___f_1283_, 2, v_n_1272_);
lean_closure_set(v___f_1283_, 3, v_inst_1273_);
lean_closure_set(v___f_1283_, 4, v_xs_1274_);
lean_closure_set(v___f_1283_, 5, v_f_1275_);
v___x_1284_ = lean_array_fget(v_xs_1274_, v_i_1276_);
lean_dec(v_i_1276_);
lean_dec_ref(v_xs_1274_);
v___x_1285_ = lean_apply_1(v_f_1275_, v___x_1284_);
v___x_1286_ = lean_apply_4(v_toBind_1279_, lean_box(0), lean_box(0), v___x_1285_, v___f_1283_);
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(lean_object* v_i_1287_, lean_object* v_acc_1288_, lean_object* v_n_1289_, lean_object* v_inst_1290_, lean_object* v_xs_1291_, lean_object* v_f_1292_, lean_object* v_____do__lift_1293_){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_nat_add(v_i_1287_, v___x_1294_);
v___x_1296_ = l_Array_append___redArg(v_acc_1288_, v_____do__lift_1293_);
v___x_1297_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1289_, v_inst_1290_, v_xs_1291_, v_f_1292_, v___x_1295_, v___x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(lean_object* v_m_1298_, lean_object* v_00_u03b1_1299_, lean_object* v_n_1300_, lean_object* v_00_u03b2_1301_, lean_object* v_k_1302_, lean_object* v_inst_1303_, lean_object* v_xs_1304_, lean_object* v_f_1305_, lean_object* v_i_1306_, lean_object* v_h_1307_, lean_object* v_acc_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1300_, v_inst_1303_, v_xs_1304_, v_f_1305_, v_i_1306_, v_acc_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(lean_object* v_m_1310_, lean_object* v_00_u03b1_1311_, lean_object* v_n_1312_, lean_object* v_00_u03b2_1313_, lean_object* v_k_1314_, lean_object* v_inst_1315_, lean_object* v_xs_1316_, lean_object* v_f_1317_, lean_object* v_i_1318_, lean_object* v_h_1319_, lean_object* v_acc_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(v_m_1310_, v_00_u03b1_1311_, v_n_1312_, v_00_u03b2_1313_, v_k_1314_, v_inst_1315_, v_xs_1316_, v_f_1317_, v_i_1318_, v_h_1319_, v_acc_1320_);
lean_dec(v_k_1314_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___redArg(lean_object* v_n_1322_, lean_object* v_inst_1323_, lean_object* v_xs_1324_, lean_object* v_f_1325_){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = lean_unsigned_to_nat(0u);
v___x_1327_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1328_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1322_, v_inst_1323_, v_xs_1324_, v_f_1325_, v___x_1326_, v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM(lean_object* v_m_1329_, lean_object* v_00_u03b1_1330_, lean_object* v_n_1331_, lean_object* v_00_u03b2_1332_, lean_object* v_k_1333_, lean_object* v_inst_1334_, lean_object* v_xs_1335_, lean_object* v_f_1336_){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1339_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1331_, v_inst_1334_, v_xs_1335_, v_f_1336_, v___x_1337_, v___x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___boxed(lean_object* v_m_1340_, lean_object* v_00_u03b1_1341_, lean_object* v_n_1342_, lean_object* v_00_u03b2_1343_, lean_object* v_k_1344_, lean_object* v_inst_1345_, lean_object* v_xs_1346_, lean_object* v_f_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Vector_flatMapM(v_m_1340_, v_00_u03b1_1341_, v_n_1342_, v_00_u03b2_1343_, v_k_1344_, v_inst_1345_, v_xs_1346_, v_f_1347_);
lean_dec(v_k_1344_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1349_, lean_object* v_ys_1350_, lean_object* v_inst_1351_, lean_object* v_xs_1352_, lean_object* v_f_1353_, lean_object* v_n_1354_, lean_object* v_____do__lift_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Vector_mapFinIdxM_map___redArg___lam__0(v_j_1349_, v_ys_1350_, v_inst_1351_, v_xs_1352_, v_f_1353_, v_n_1354_, v_____do__lift_1355_);
lean_dec(v_n_1354_);
lean_dec(v_j_1349_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg(lean_object* v_inst_1357_, lean_object* v_xs_1358_, lean_object* v_f_1359_, lean_object* v_i_1360_, lean_object* v_j_1361_, lean_object* v_ys_1362_){
_start:
{
lean_object* v_toApplicative_1363_; lean_object* v_toBind_1364_; lean_object* v_toPure_1365_; lean_object* v_zero_1366_; uint8_t v_isZero_1367_; 
v_toApplicative_1363_ = lean_ctor_get(v_inst_1357_, 0);
v_toBind_1364_ = lean_ctor_get(v_inst_1357_, 1);
lean_inc(v_toBind_1364_);
v_toPure_1365_ = lean_ctor_get(v_toApplicative_1363_, 1);
v_zero_1366_ = lean_unsigned_to_nat(0u);
v_isZero_1367_ = lean_nat_dec_eq(v_i_1360_, v_zero_1366_);
if (v_isZero_1367_ == 1)
{
lean_object* v___x_1368_; 
lean_inc(v_toPure_1365_);
lean_dec(v_toBind_1364_);
lean_dec(v_j_1361_);
lean_dec(v_f_1359_);
lean_dec_ref(v_xs_1358_);
lean_dec_ref(v_inst_1357_);
v___x_1368_ = lean_apply_2(v_toPure_1365_, lean_box(0), v_ys_1362_);
return v___x_1368_;
}
else
{
lean_object* v_one_1369_; lean_object* v_n_1370_; lean_object* v___f_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_one_1369_ = lean_unsigned_to_nat(1u);
v_n_1370_ = lean_nat_sub(v_i_1360_, v_one_1369_);
lean_inc(v_f_1359_);
lean_inc_ref(v_xs_1358_);
lean_inc(v_j_1361_);
v___f_1371_ = lean_alloc_closure((void*)(l_Vector_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1371_, 0, v_j_1361_);
lean_closure_set(v___f_1371_, 1, v_ys_1362_);
lean_closure_set(v___f_1371_, 2, v_inst_1357_);
lean_closure_set(v___f_1371_, 3, v_xs_1358_);
lean_closure_set(v___f_1371_, 4, v_f_1359_);
lean_closure_set(v___f_1371_, 5, v_n_1370_);
v___x_1372_ = lean_array_fget(v_xs_1358_, v_j_1361_);
lean_dec_ref(v_xs_1358_);
v___x_1373_ = lean_apply_3(v_f_1359_, v_j_1361_, v___x_1372_, lean_box(0));
v___x_1374_ = lean_apply_4(v_toBind_1364_, lean_box(0), lean_box(0), v___x_1373_, v___f_1371_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1375_, lean_object* v_ys_1376_, lean_object* v_inst_1377_, lean_object* v_xs_1378_, lean_object* v_f_1379_, lean_object* v_n_1380_, lean_object* v_____do__lift_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1382_ = lean_unsigned_to_nat(1u);
v___x_1383_ = lean_nat_add(v_j_1375_, v___x_1382_);
v___x_1384_ = lean_array_push(v_ys_1376_, v_____do__lift_1381_);
v___x_1385_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1377_, v_xs_1378_, v_f_1379_, v_n_1380_, v___x_1383_, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1386_, lean_object* v_xs_1387_, lean_object* v_f_1388_, lean_object* v_i_1389_, lean_object* v_j_1390_, lean_object* v_ys_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1386_, v_xs_1387_, v_f_1388_, v_i_1389_, v_j_1390_, v_ys_1391_);
lean_dec(v_i_1389_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map(lean_object* v_n_1393_, lean_object* v_00_u03b1_1394_, lean_object* v_00_u03b2_1395_, lean_object* v_m_1396_, lean_object* v_inst_1397_, lean_object* v_xs_1398_, lean_object* v_f_1399_, lean_object* v_i_1400_, lean_object* v_j_1401_, lean_object* v_inv_1402_, lean_object* v_ys_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1397_, v_xs_1398_, v_f_1399_, v_i_1400_, v_j_1401_, v_ys_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___boxed(lean_object* v_n_1405_, lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_m_1408_, lean_object* v_inst_1409_, lean_object* v_xs_1410_, lean_object* v_f_1411_, lean_object* v_i_1412_, lean_object* v_j_1413_, lean_object* v_inv_1414_, lean_object* v_ys_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Vector_mapFinIdxM_map(v_n_1405_, v_00_u03b1_1406_, v_00_u03b2_1407_, v_m_1408_, v_inst_1409_, v_xs_1410_, v_f_1411_, v_i_1412_, v_j_1413_, v_inv_1414_, v_ys_1415_);
lean_dec(v_i_1412_);
lean_dec(v_n_1405_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg(lean_object* v_n_1417_, lean_object* v_inst_1418_, lean_object* v_xs_1419_, lean_object* v_f_1420_){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_unsigned_to_nat(0u);
v___x_1422_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1423_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1418_, v_xs_1419_, v_f_1420_, v_n_1417_, v___x_1421_, v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg___boxed(lean_object* v_n_1424_, lean_object* v_inst_1425_, lean_object* v_xs_1426_, lean_object* v_f_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Vector_mapFinIdxM___redArg(v_n_1424_, v_inst_1425_, v_xs_1426_, v_f_1427_);
lean_dec(v_n_1424_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM(lean_object* v_n_1429_, lean_object* v_00_u03b1_1430_, lean_object* v_00_u03b2_1431_, lean_object* v_m_1432_, lean_object* v_inst_1433_, lean_object* v_xs_1434_, lean_object* v_f_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1438_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1433_, v_xs_1434_, v_f_1435_, v_n_1429_, v___x_1436_, v___x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___boxed(lean_object* v_n_1439_, lean_object* v_00_u03b1_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_m_1442_, lean_object* v_inst_1443_, lean_object* v_xs_1444_, lean_object* v_f_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Vector_mapFinIdxM(v_n_1439_, v_00_u03b1_1440_, v_00_u03b2_1441_, v_m_1442_, v_inst_1443_, v_xs_1444_, v_f_1445_);
lean_dec(v_n_1439_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg(lean_object* v_n_1447_, lean_object* v_inst_1448_, lean_object* v_f_1449_, lean_object* v_xs_1450_){
_start:
{
lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___f_1451_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1451_, 0, v_f_1449_);
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1454_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1448_, v_xs_1450_, v___f_1451_, v_n_1447_, v___x_1452_, v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg___boxed(lean_object* v_n_1455_, lean_object* v_inst_1456_, lean_object* v_f_1457_, lean_object* v_xs_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Vector_mapIdxM___redArg(v_n_1455_, v_inst_1456_, v_f_1457_, v_xs_1458_);
lean_dec(v_n_1455_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM(lean_object* v_n_1460_, lean_object* v_00_u03b1_1461_, lean_object* v_00_u03b2_1462_, lean_object* v_m_1463_, lean_object* v_inst_1464_, lean_object* v_f_1465_, lean_object* v_xs_1466_){
_start:
{
lean_object* v___f_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___f_1467_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1467_, 0, v_f_1465_);
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1470_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1464_, v_xs_1466_, v___f_1467_, v_n_1460_, v___x_1468_, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___boxed(lean_object* v_n_1471_, lean_object* v_00_u03b1_1472_, lean_object* v_00_u03b2_1473_, lean_object* v_m_1474_, lean_object* v_inst_1475_, lean_object* v_f_1476_, lean_object* v_xs_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Vector_mapIdxM(v_n_1471_, v_00_u03b1_1472_, v_00_u03b2_1473_, v_m_1474_, v_inst_1475_, v_f_1476_, v_xs_1477_);
lean_dec(v_n_1471_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___redArg(lean_object* v_inst_1479_, lean_object* v_f_1480_, lean_object* v_xs_1481_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_unsigned_to_nat(0u);
v___x_1483_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1479_, v_f_1480_, v_xs_1481_, v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM(lean_object* v_00_u03b2_1484_, lean_object* v_n_1485_, lean_object* v_00_u03b1_1486_, lean_object* v_m_1487_, lean_object* v_inst_1488_, lean_object* v_f_1489_, lean_object* v_xs_1490_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1488_, v_f_1489_, v_xs_1490_, v___x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___boxed(lean_object* v_00_u03b2_1493_, lean_object* v_n_1494_, lean_object* v_00_u03b1_1495_, lean_object* v_m_1496_, lean_object* v_inst_1497_, lean_object* v_f_1498_, lean_object* v_xs_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Vector_firstM(v_00_u03b2_1493_, v_n_1494_, v_00_u03b1_1495_, v_m_1496_, v_inst_1497_, v_f_1498_, v_xs_1499_);
lean_dec(v_n_1494_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0(lean_object* v_x_1501_){
_start:
{
lean_inc_ref(v_x_1501_);
return v_x_1501_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0___boxed(lean_object* v_x_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Vector_flatten___redArg___lam__0(v_x_1502_);
lean_dec_ref(v_x_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg(lean_object* v_xs_1508_){
_start:
{
lean_object* v___f_1509_; lean_object* v___x_1510_; size_t v_sz_1511_; size_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___f_1509_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1510_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1511_ = lean_array_size(v_xs_1508_);
v___x_1512_ = ((size_t)0ULL);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1510_, v___f_1509_, v_sz_1511_, v___x_1512_, v_xs_1508_);
v___x_1514_ = lean_unsigned_to_nat(0u);
v___x_1515_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1516_ = lean_array_get_size(v___x_1513_);
v___x_1517_ = lean_nat_dec_lt(v___x_1514_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_dec(v___x_1513_);
return v___x_1515_;
}
else
{
lean_object* v___f_1518_; size_t v___x_1519_; lean_object* v___x_1520_; 
v___f_1518_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1519_ = lean_usize_of_nat(v___x_1516_);
v___x_1520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1510_, v___f_1518_, v___x_1513_, v___x_1512_, v___x_1519_, v___x_1515_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten(lean_object* v_00_u03b1_1521_, lean_object* v_n_1522_, lean_object* v_m_1523_, lean_object* v_xs_1524_){
_start:
{
lean_object* v___f_1525_; lean_object* v___x_1526_; size_t v_sz_1527_; size_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___f_1525_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1526_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1527_ = lean_array_size(v_xs_1524_);
v___x_1528_ = ((size_t)0ULL);
v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1526_, v___f_1525_, v_sz_1527_, v___x_1528_, v_xs_1524_);
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1532_ = lean_array_get_size(v___x_1529_);
v___x_1533_ = lean_nat_dec_lt(v___x_1530_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_dec(v___x_1529_);
return v___x_1531_;
}
else
{
lean_object* v___f_1534_; size_t v___x_1535_; lean_object* v___x_1536_; 
v___f_1534_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1535_ = lean_usize_of_nat(v___x_1532_);
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1526_, v___f_1534_, v___x_1529_, v___x_1528_, v___x_1535_, v___x_1531_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_n_1538_, lean_object* v_m_1539_, lean_object* v_xs_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Vector_flatten(v_00_u03b1_1537_, v_n_1538_, v_m_1539_, v_xs_1540_);
lean_dec(v_m_1539_);
lean_dec(v_n_1538_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg___lam__0(lean_object* v_f_1542_, lean_object* v_x1_1543_, lean_object* v_x2_1544_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_apply_1(v_f_1542_, v_x2_1544_);
v___x_1546_ = l_Array_append___redArg(v_x1_1543_, v___x_1545_);
lean_dec_ref(v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg(lean_object* v_xs_1547_, lean_object* v_f_1548_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1551_ = lean_array_get_size(v_xs_1547_);
v___x_1552_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1553_ = lean_nat_dec_lt(v___x_1549_, v___x_1551_);
if (v___x_1553_ == 0)
{
lean_dec_ref(v_f_1548_);
lean_dec_ref(v_xs_1547_);
return v___x_1550_;
}
else
{
lean_object* v___f_1554_; size_t v___x_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v___f_1554_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1554_, 0, v_f_1548_);
v___x_1555_ = ((size_t)0ULL);
v___x_1556_ = lean_usize_of_nat(v___x_1551_);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1552_, v___f_1554_, v_xs_1547_, v___x_1555_, v___x_1556_, v___x_1550_);
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap(lean_object* v_00_u03b1_1558_, lean_object* v_n_1559_, lean_object* v_00_u03b2_1560_, lean_object* v_m_1561_, lean_object* v_xs_1562_, lean_object* v_f_1563_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1566_ = lean_array_get_size(v_xs_1562_);
v___x_1567_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1568_ = lean_nat_dec_lt(v___x_1564_, v___x_1566_);
if (v___x_1568_ == 0)
{
lean_dec_ref(v_f_1563_);
lean_dec_ref(v_xs_1562_);
return v___x_1565_;
}
else
{
lean_object* v___f_1569_; size_t v___x_1570_; size_t v___x_1571_; lean_object* v___x_1572_; 
v___f_1569_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1569_, 0, v_f_1563_);
v___x_1570_ = ((size_t)0ULL);
v___x_1571_ = lean_usize_of_nat(v___x_1566_);
v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1567_, v___f_1569_, v_xs_1562_, v___x_1570_, v___x_1571_, v___x_1565_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_n_1574_, lean_object* v_00_u03b2_1575_, lean_object* v_m_1576_, lean_object* v_xs_1577_, lean_object* v_f_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Vector_flatMap(v_00_u03b1_1573_, v_n_1574_, v_00_u03b2_1575_, v_m_1576_, v_xs_1577_, v_f_1578_);
lean_dec(v_m_1576_);
lean_dec(v_n_1574_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg(lean_object* v_xs_1580_, lean_object* v_k_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Array_zipIdx___redArg(v_xs_1580_, v_k_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg___boxed(lean_object* v_xs_1583_, lean_object* v_k_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Vector_zipIdx___redArg(v_xs_1583_, v_k_1584_);
lean_dec(v_k_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx(lean_object* v_00_u03b1_1586_, lean_object* v_n_1587_, lean_object* v_xs_1588_, lean_object* v_k_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Array_zipIdx___redArg(v_xs_1588_, v_k_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___boxed(lean_object* v_00_u03b1_1591_, lean_object* v_n_1592_, lean_object* v_xs_1593_, lean_object* v_k_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Vector_zipIdx(v_00_u03b1_1591_, v_n_1592_, v_xs_1593_, v_k_1594_);
lean_dec(v_k_1594_);
lean_dec(v_n_1592_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg(lean_object* v_as_1596_, lean_object* v_bs_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Array_zip___redArg(v_as_1596_, v_bs_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg___boxed(lean_object* v_as_1599_, lean_object* v_bs_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Vector_zip___redArg(v_as_1599_, v_bs_1600_);
lean_dec_ref(v_bs_1600_);
lean_dec_ref(v_as_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip(lean_object* v_00_u03b1_1602_, lean_object* v_n_1603_, lean_object* v_00_u03b2_1604_, lean_object* v_as_1605_, lean_object* v_bs_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Array_zip___redArg(v_as_1605_, v_bs_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___boxed(lean_object* v_00_u03b1_1608_, lean_object* v_n_1609_, lean_object* v_00_u03b2_1610_, lean_object* v_as_1611_, lean_object* v_bs_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Vector_zip(v_00_u03b1_1608_, v_n_1609_, v_00_u03b2_1610_, v_as_1611_, v_bs_1612_);
lean_dec_ref(v_bs_1612_);
lean_dec_ref(v_as_1611_);
lean_dec(v_n_1609_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___redArg(lean_object* v_f_1614_, lean_object* v_as_1615_, lean_object* v_bs_1616_){
_start:
{
lean_object* v___f_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___f_1617_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1617_, 0, v_f_1614_);
v___x_1618_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1619_ = lean_unsigned_to_nat(0u);
v___x_1620_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1621_ = l_Array_zipWithMAux___redArg(v___x_1618_, v_as_1615_, v_bs_1616_, v___f_1617_, v___x_1619_, v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith(lean_object* v_00_u03b1_1622_, lean_object* v_00_u03b2_1623_, lean_object* v_00_u03c6_1624_, lean_object* v_n_1625_, lean_object* v_f_1626_, lean_object* v_as_1627_, lean_object* v_bs_1628_){
_start:
{
lean_object* v___f_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___f_1629_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1629_, 0, v_f_1626_);
v___x_1630_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1633_ = l_Array_zipWithMAux___redArg(v___x_1630_, v_as_1627_, v_bs_1628_, v___f_1629_, v___x_1631_, v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___boxed(lean_object* v_00_u03b1_1634_, lean_object* v_00_u03b2_1635_, lean_object* v_00_u03c6_1636_, lean_object* v_n_1637_, lean_object* v_f_1638_, lean_object* v_as_1639_, lean_object* v_bs_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Vector_zipWith(v_00_u03b1_1634_, v_00_u03b2_1635_, v_00_u03c6_1636_, v_n_1637_, v_f_1638_, v_as_1639_, v_bs_1640_);
lean_dec(v_n_1637_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg(lean_object* v_xs_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v_fst_1644_; lean_object* v_snd_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v___x_1643_ = l_Array_unzip___redArg(v_xs_1642_);
v_fst_1644_ = lean_ctor_get(v___x_1643_, 0);
v_snd_1645_ = lean_ctor_get(v___x_1643_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1643_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_snd_1645_);
lean_inc(v_fst_1644_);
lean_dec(v___x_1643_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_fst_1644_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_snd_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg___boxed(lean_object* v_xs_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Vector_unzip___redArg(v_xs_1653_);
lean_dec_ref(v_xs_1653_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip(lean_object* v_00_u03b1_1655_, lean_object* v_00_u03b2_1656_, lean_object* v_n_1657_, lean_object* v_xs_1658_){
_start:
{
lean_object* v___x_1659_; lean_object* v_fst_1660_; lean_object* v_snd_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v___x_1659_ = l_Array_unzip___redArg(v_xs_1658_);
v_fst_1660_ = lean_ctor_get(v___x_1659_, 0);
v_snd_1661_ = lean_ctor_get(v___x_1659_, 1);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1659_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_snd_1661_);
lean_inc(v_fst_1660_);
lean_dec(v___x_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_fst_1660_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_snd_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___boxed(lean_object* v_00_u03b1_1669_, lean_object* v_00_u03b2_1670_, lean_object* v_n_1671_, lean_object* v_xs_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Vector_unzip(v_00_u03b1_1669_, v_00_u03b2_1670_, v_n_1671_, v_xs_1672_);
lean_dec_ref(v_xs_1672_);
lean_dec(v_n_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn___redArg(lean_object* v_n_1674_, lean_object* v_f_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Array_ofFn___redArg(v_n_1674_, v_f_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn(lean_object* v_n_1677_, lean_object* v_00_u03b1_1678_, lean_object* v_f_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Array_ofFn___redArg(v_n_1677_, v_f_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l_Vector_swap___auto__1(void){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1681_;
}
}
static lean_object* _init_l_Vector_swap___auto__3(void){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg(lean_object* v_xs_1683_, lean_object* v_i_1684_, lean_object* v_j_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_array_fswap(v_xs_1683_, v_i_1684_, v_j_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg___boxed(lean_object* v_xs_1687_, lean_object* v_i_1688_, lean_object* v_j_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Vector_swap___redArg(v_xs_1687_, v_i_1688_, v_j_1689_);
lean_dec(v_j_1689_);
lean_dec(v_i_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap(lean_object* v_00_u03b1_1691_, lean_object* v_n_1692_, lean_object* v_xs_1693_, lean_object* v_i_1694_, lean_object* v_j_1695_, lean_object* v_hi_1696_, lean_object* v_hj_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_array_fswap(v_xs_1693_, v_i_1694_, v_j_1695_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___boxed(lean_object* v_00_u03b1_1699_, lean_object* v_n_1700_, lean_object* v_xs_1701_, lean_object* v_i_1702_, lean_object* v_j_1703_, lean_object* v_hi_1704_, lean_object* v_hj_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Vector_swap(v_00_u03b1_1699_, v_n_1700_, v_xs_1701_, v_i_1702_, v_j_1703_, v_hi_1704_, v_hj_1705_);
lean_dec(v_j_1703_);
lean_dec(v_i_1702_);
lean_dec(v_n_1700_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg(lean_object* v_xs_1707_, lean_object* v_i_1708_, lean_object* v_j_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_array_swap(v_xs_1707_, v_i_1708_, v_j_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg___boxed(lean_object* v_xs_1711_, lean_object* v_i_1712_, lean_object* v_j_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Vector_swapIfInBounds___redArg(v_xs_1711_, v_i_1712_, v_j_1713_);
lean_dec(v_j_1713_);
lean_dec(v_i_1712_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds(lean_object* v_00_u03b1_1715_, lean_object* v_n_1716_, lean_object* v_xs_1717_, lean_object* v_i_1718_, lean_object* v_j_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_array_swap(v_xs_1717_, v_i_1718_, v_j_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___boxed(lean_object* v_00_u03b1_1721_, lean_object* v_n_1722_, lean_object* v_xs_1723_, lean_object* v_i_1724_, lean_object* v_j_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Vector_swapIfInBounds(v_00_u03b1_1721_, v_n_1722_, v_xs_1723_, v_i_1724_, v_j_1725_);
lean_dec(v_j_1725_);
lean_dec(v_i_1724_);
lean_dec(v_n_1722_);
return v_res_1726_;
}
}
static lean_object* _init_l_Vector_swapAt___auto__1(void){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg(lean_object* v_xs_1728_, lean_object* v_i_1729_, lean_object* v_x_1730_){
_start:
{
lean_object* v_e_1731_; lean_object* v_xs_x27_1732_; lean_object* v___x_1733_; 
v_e_1731_ = lean_array_fget(v_xs_1728_, v_i_1729_);
v_xs_x27_1732_ = lean_array_fset(v_xs_1728_, v_i_1729_, v_x_1730_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_e_1731_);
lean_ctor_set(v___x_1733_, 1, v_xs_x27_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg___boxed(lean_object* v_xs_1734_, lean_object* v_i_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Vector_swapAt___redArg(v_xs_1734_, v_i_1735_, v_x_1736_);
lean_dec(v_i_1735_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt(lean_object* v_00_u03b1_1738_, lean_object* v_n_1739_, lean_object* v_xs_1740_, lean_object* v_i_1741_, lean_object* v_x_1742_, lean_object* v_hi_1743_){
_start:
{
lean_object* v_e_1744_; lean_object* v_xs_x27_1745_; lean_object* v___x_1746_; 
v_e_1744_ = lean_array_fget(v_xs_1740_, v_i_1741_);
v_xs_x27_1745_ = lean_array_fset(v_xs_1740_, v_i_1741_, v_x_1742_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_e_1744_);
lean_ctor_set(v___x_1746_, 1, v_xs_x27_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___boxed(lean_object* v_00_u03b1_1747_, lean_object* v_n_1748_, lean_object* v_xs_1749_, lean_object* v_i_1750_, lean_object* v_x_1751_, lean_object* v_hi_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Vector_swapAt(v_00_u03b1_1747_, v_n_1748_, v_xs_1749_, v_i_1750_, v_x_1751_, v_hi_1752_);
lean_dec(v_i_1750_);
lean_dec(v_n_1748_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___redArg(lean_object* v_xs_1758_, lean_object* v_i_1759_, lean_object* v_x_1760_){
_start:
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = lean_array_get_size(v_xs_1758_);
v___x_1762_ = lean_nat_dec_lt(v_i_1759_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v_this_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_fst_1775_; lean_object* v_snd_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_this_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1763_, 0, v_x_1760_);
lean_ctor_set(v_this_1763_, 1, v_xs_1758_);
v___x_1764_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1765_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1766_ = lean_unsigned_to_nat(463u);
v___x_1767_ = lean_unsigned_to_nat(4u);
v___x_1768_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1769_ = l_Nat_reprFast(v_i_1759_);
v___x_1770_ = lean_string_append(v___x_1768_, v___x_1769_);
lean_dec_ref(v___x_1769_);
v___x_1771_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1772_ = lean_string_append(v___x_1770_, v___x_1771_);
v___x_1773_ = l_mkPanicMessageWithDecl(v___x_1764_, v___x_1765_, v___x_1766_, v___x_1767_, v___x_1772_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = l_panic___redArg(v_this_1763_, v___x_1773_);
lean_dec_ref_known(v_this_1763_, 2);
v_fst_1775_ = lean_ctor_get(v___x_1774_, 0);
v_snd_1776_ = lean_ctor_get(v___x_1774_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1774_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_snd_1776_);
lean_inc(v_fst_1775_);
lean_dec(v___x_1774_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_fst_1775_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_snd_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v_e_1784_; lean_object* v_xs_x27_1785_; lean_object* v___x_1786_; 
v_e_1784_ = lean_array_fget(v_xs_1758_, v_i_1759_);
v_xs_x27_1785_ = lean_array_fset(v_xs_1758_, v_i_1759_, v_x_1760_);
lean_dec(v_i_1759_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v_e_1784_);
lean_ctor_set(v___x_1786_, 1, v_xs_x27_1785_);
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21(lean_object* v_00_u03b1_1787_, lean_object* v_n_1788_, lean_object* v_xs_1789_, lean_object* v_i_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_array_get_size(v_xs_1789_);
v___x_1793_ = lean_nat_dec_lt(v_i_1790_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v_this_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v_fst_1806_; lean_object* v_snd_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
v_this_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1794_, 0, v_x_1791_);
lean_ctor_set(v_this_1794_, 1, v_xs_1789_);
v___x_1795_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1796_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1797_ = lean_unsigned_to_nat(463u);
v___x_1798_ = lean_unsigned_to_nat(4u);
v___x_1799_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1800_ = l_Nat_reprFast(v_i_1790_);
v___x_1801_ = lean_string_append(v___x_1799_, v___x_1800_);
lean_dec_ref(v___x_1800_);
v___x_1802_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1803_ = lean_string_append(v___x_1801_, v___x_1802_);
v___x_1804_ = l_mkPanicMessageWithDecl(v___x_1795_, v___x_1796_, v___x_1797_, v___x_1798_, v___x_1803_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = l_panic___redArg(v_this_1794_, v___x_1804_);
lean_dec_ref_known(v_this_1794_, 2);
v_fst_1806_ = lean_ctor_get(v___x_1805_, 0);
v_snd_1807_ = lean_ctor_get(v___x_1805_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1805_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_snd_1807_);
lean_inc(v_fst_1806_);
lean_dec(v___x_1805_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_fst_1806_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_snd_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
else
{
lean_object* v_e_1815_; lean_object* v_xs_x27_1816_; lean_object* v___x_1817_; 
v_e_1815_ = lean_array_fget(v_xs_1789_, v_i_1790_);
v_xs_x27_1816_ = lean_array_fset(v_xs_1789_, v_i_1790_, v_x_1791_);
lean_dec(v_i_1790_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_e_1815_);
lean_ctor_set(v___x_1817_, 1, v_xs_x27_1816_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___boxed(lean_object* v_00_u03b1_1818_, lean_object* v_n_1819_, lean_object* v_xs_1820_, lean_object* v_i_1821_, lean_object* v_x_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Vector_swapAt_x21(v_00_u03b1_1818_, v_n_1819_, v_xs_1820_, v_i_1821_, v_x_1822_);
lean_dec(v_n_1819_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Vector_range(lean_object* v_n_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Array_range(v_n_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Vector_range_x27(lean_object* v_start_1826_, lean_object* v_size_1827_, lean_object* v_step_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Array_range_x27(v_start_1826_, v_size_1827_, v_step_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv___redArg(lean_object* v_n_1830_, lean_object* v_xs_1831_, lean_object* v_ys_1832_, lean_object* v_r_1833_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Array_isEqvAux___redArg(v_xs_1831_, v_ys_1832_, v_r_1833_, v_n_1830_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___redArg___boxed(lean_object* v_n_1835_, lean_object* v_xs_1836_, lean_object* v_ys_1837_, lean_object* v_r_1838_){
_start:
{
uint8_t v_res_1839_; lean_object* v_r_1840_; 
v_res_1839_ = l_Vector_isEqv___redArg(v_n_1835_, v_xs_1836_, v_ys_1837_, v_r_1838_);
lean_dec_ref(v_ys_1837_);
lean_dec_ref(v_xs_1836_);
v_r_1840_ = lean_box(v_res_1839_);
return v_r_1840_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv(lean_object* v_00_u03b1_1841_, lean_object* v_n_1842_, lean_object* v_xs_1843_, lean_object* v_ys_1844_, lean_object* v_r_1845_){
_start:
{
uint8_t v___x_1846_; 
v___x_1846_ = l_Array_isEqvAux___redArg(v_xs_1843_, v_ys_1844_, v_r_1845_, v_n_1842_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___boxed(lean_object* v_00_u03b1_1847_, lean_object* v_n_1848_, lean_object* v_xs_1849_, lean_object* v_ys_1850_, lean_object* v_r_1851_){
_start:
{
uint8_t v_res_1852_; lean_object* v_r_1853_; 
v_res_1852_ = l_Vector_isEqv(v_00_u03b1_1847_, v_n_1848_, v_xs_1849_, v_ys_1850_, v_r_1851_);
lean_dec_ref(v_ys_1850_);
lean_dec_ref(v_xs_1849_);
v_r_1853_ = lean_box(v_res_1852_);
return v_r_1853_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__0(lean_object* v_inst_1854_, lean_object* v_x1_1855_, lean_object* v_x2_1856_){
_start:
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = lean_apply_2(v_inst_1854_, v_x1_1855_, v_x2_1856_);
v___x_1858_ = lean_unbox(v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__0___boxed(lean_object* v_inst_1859_, lean_object* v_x1_1860_, lean_object* v_x2_1861_){
_start:
{
uint8_t v_res_1862_; lean_object* v_r_1863_; 
v_res_1862_ = l_Vector_instBEq___redArg___lam__0(v_inst_1859_, v_x1_1860_, v_x2_1861_);
v_r_1863_ = lean_box(v_res_1862_);
return v_r_1863_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__1(lean_object* v___f_1864_, lean_object* v_n_1865_, lean_object* v_xs_1866_, lean_object* v_ys_1867_){
_start:
{
uint8_t v___x_1868_; 
v___x_1868_ = l_Array_isEqvAux___redArg(v_xs_1866_, v_ys_1867_, v___f_1864_, v_n_1865_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__1___boxed(lean_object* v___f_1869_, lean_object* v_n_1870_, lean_object* v_xs_1871_, lean_object* v_ys_1872_){
_start:
{
uint8_t v_res_1873_; lean_object* v_r_1874_; 
v_res_1873_ = l_Vector_instBEq___redArg___lam__1(v___f_1869_, v_n_1870_, v_xs_1871_, v_ys_1872_);
lean_dec_ref(v_ys_1872_);
lean_dec_ref(v_xs_1871_);
v_r_1874_ = lean_box(v_res_1873_);
return v_r_1874_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg(lean_object* v_n_1875_, lean_object* v_inst_1876_){
_start:
{
lean_object* v___f_1877_; lean_object* v___f_1878_; 
v___f_1877_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1877_, 0, v_inst_1876_);
v___f_1878_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1878_, 0, v___f_1877_);
lean_closure_set(v___f_1878_, 1, v_n_1875_);
return v___f_1878_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq(lean_object* v_00_u03b1_1879_, lean_object* v_n_1880_, lean_object* v_inst_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Vector_instBEq___redArg(v_n_1880_, v_inst_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___redArg(lean_object* v_xs_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Array_reverse___redArg(v_xs_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse(lean_object* v_00_u03b1_1885_, lean_object* v_n_1886_, lean_object* v_xs_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Array_reverse___redArg(v_xs_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___boxed(lean_object* v_00_u03b1_1889_, lean_object* v_n_1890_, lean_object* v_xs_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Vector_reverse(v_00_u03b1_1889_, v_n_1890_, v_xs_1891_);
lean_dec(v_n_1890_);
return v_res_1892_;
}
}
static lean_object* _init_l_Vector_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___redArg(lean_object* v_xs_1894_, lean_object* v_i_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Array_eraseIdx___redArg(v_xs_1894_, v_i_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx(lean_object* v_00_u03b1_1897_, lean_object* v_n_1898_, lean_object* v_xs_1899_, lean_object* v_i_1900_, lean_object* v_h_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Array_eraseIdx___redArg(v_xs_1899_, v_i_1900_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_n_1904_, lean_object* v_xs_1905_, lean_object* v_i_1906_, lean_object* v_h_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Vector_eraseIdx(v_00_u03b1_1903_, v_n_1904_, v_xs_1905_, v_i_1906_, v_h_1907_);
lean_dec(v_n_1904_);
return v_res_1908_;
}
}
static lean_object* _init_l_Vector_eraseIdx_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1912_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1913_ = lean_unsigned_to_nat(4u);
v___x_1914_ = lean_unsigned_to_nat(433u);
v___x_1915_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__1));
v___x_1916_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1917_ = l_mkPanicMessageWithDecl(v___x_1916_, v___x_1915_, v___x_1914_, v___x_1913_, v___x_1912_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg(lean_object* v_n_1918_, lean_object* v_xs_1919_, lean_object* v_i_1920_){
_start:
{
uint8_t v___x_1921_; 
v___x_1921_ = lean_nat_dec_lt(v_i_1920_, v_n_1918_);
if (v___x_1921_ == 0)
{
lean_object* v_this_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
lean_dec(v_i_1920_);
v_this_1922_ = lean_array_pop(v_xs_1919_);
v___x_1923_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1924_ = l_panic___redArg(v_this_1922_, v___x_1923_);
lean_dec_ref(v_this_1922_);
return v___x_1924_;
}
else
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Array_eraseIdx___redArg(v_xs_1919_, v_i_1920_);
return v___x_1925_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg___boxed(lean_object* v_n_1926_, lean_object* v_xs_1927_, lean_object* v_i_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Vector_eraseIdx_x21___redArg(v_n_1926_, v_xs_1927_, v_i_1928_);
lean_dec(v_n_1926_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21(lean_object* v_00_u03b1_1930_, lean_object* v_n_1931_, lean_object* v_xs_1932_, lean_object* v_i_1933_){
_start:
{
uint8_t v___x_1934_; 
v___x_1934_ = lean_nat_dec_lt(v_i_1933_, v_n_1931_);
if (v___x_1934_ == 0)
{
lean_object* v_this_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v_i_1933_);
v_this_1935_ = lean_array_pop(v_xs_1932_);
v___x_1936_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1937_ = l_panic___redArg(v_this_1935_, v___x_1936_);
lean_dec_ref(v_this_1935_);
return v___x_1937_;
}
else
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Array_eraseIdx___redArg(v_xs_1932_, v_i_1933_);
return v___x_1938_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___boxed(lean_object* v_00_u03b1_1939_, lean_object* v_n_1940_, lean_object* v_xs_1941_, lean_object* v_i_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Vector_eraseIdx_x21(v_00_u03b1_1939_, v_n_1940_, v_xs_1941_, v_i_1942_);
lean_dec(v_n_1940_);
return v_res_1943_;
}
}
static lean_object* _init_l_Vector_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg(lean_object* v_xs_1945_, lean_object* v_i_1946_, lean_object* v_x_1947_){
_start:
{
lean_object* v_j_1948_; lean_object* v_as_1949_; lean_object* v___x_1950_; 
v_j_1948_ = lean_array_get_size(v_xs_1945_);
v_as_1949_ = lean_array_push(v_xs_1945_, v_x_1947_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1946_, v_as_1949_, v_j_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg___boxed(lean_object* v_xs_1951_, lean_object* v_i_1952_, lean_object* v_x_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Vector_insertIdx___redArg(v_xs_1951_, v_i_1952_, v_x_1953_);
lean_dec(v_i_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx(lean_object* v_00_u03b1_1955_, lean_object* v_n_1956_, lean_object* v_xs_1957_, lean_object* v_i_1958_, lean_object* v_x_1959_, lean_object* v_h_1960_){
_start:
{
lean_object* v_j_1961_; lean_object* v_as_1962_; lean_object* v___x_1963_; 
v_j_1961_ = lean_array_get_size(v_xs_1957_);
v_as_1962_ = lean_array_push(v_xs_1957_, v_x_1959_);
v___x_1963_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1958_, v_as_1962_, v_j_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___boxed(lean_object* v_00_u03b1_1964_, lean_object* v_n_1965_, lean_object* v_xs_1966_, lean_object* v_i_1967_, lean_object* v_x_1968_, lean_object* v_h_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Vector_insertIdx(v_00_u03b1_1964_, v_n_1965_, v_xs_1966_, v_i_1967_, v_x_1968_, v_h_1969_);
lean_dec(v_i_1967_);
lean_dec(v_n_1965_);
return v_res_1970_;
}
}
static lean_object* _init_l_Vector_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1972_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1973_ = lean_unsigned_to_nat(4u);
v___x_1974_ = lean_unsigned_to_nat(446u);
v___x_1975_ = ((lean_object*)(l_Vector_insertIdx_x21___redArg___closed__0));
v___x_1976_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1977_ = l_mkPanicMessageWithDecl(v___x_1976_, v___x_1975_, v___x_1974_, v___x_1973_, v___x_1972_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg(lean_object* v_n_1978_, lean_object* v_xs_1979_, lean_object* v_i_1980_, lean_object* v_x_1981_){
_start:
{
uint8_t v___x_1982_; 
v___x_1982_ = lean_nat_dec_le(v_i_1980_, v_n_1978_);
if (v___x_1982_ == 0)
{
lean_object* v_this_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_this_1983_ = lean_array_push(v_xs_1979_, v_x_1981_);
v___x_1984_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1985_ = l_panic___redArg(v_this_1983_, v___x_1984_);
lean_dec_ref(v_this_1983_);
return v___x_1985_;
}
else
{
lean_object* v_j_1986_; lean_object* v_as_1987_; lean_object* v___x_1988_; 
v_j_1986_ = lean_array_get_size(v_xs_1979_);
v_as_1987_ = lean_array_push(v_xs_1979_, v_x_1981_);
v___x_1988_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1980_, v_as_1987_, v_j_1986_);
return v___x_1988_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg___boxed(lean_object* v_n_1989_, lean_object* v_xs_1990_, lean_object* v_i_1991_, lean_object* v_x_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Vector_insertIdx_x21___redArg(v_n_1989_, v_xs_1990_, v_i_1991_, v_x_1992_);
lean_dec(v_i_1991_);
lean_dec(v_n_1989_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21(lean_object* v_00_u03b1_1994_, lean_object* v_n_1995_, lean_object* v_xs_1996_, lean_object* v_i_1997_, lean_object* v_x_1998_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_nat_dec_le(v_i_1997_, v_n_1995_);
if (v___x_1999_ == 0)
{
lean_object* v_this_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v_this_2000_ = lean_array_push(v_xs_1996_, v_x_1998_);
v___x_2001_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_2002_ = l_panic___redArg(v_this_2000_, v___x_2001_);
lean_dec_ref(v_this_2000_);
return v___x_2002_;
}
else
{
lean_object* v_j_2003_; lean_object* v_as_2004_; lean_object* v___x_2005_; 
v_j_2003_ = lean_array_get_size(v_xs_1996_);
v_as_2004_ = lean_array_push(v_xs_1996_, v_x_1998_);
v___x_2005_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1997_, v_as_2004_, v_j_2003_);
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___boxed(lean_object* v_00_u03b1_2006_, lean_object* v_n_2007_, lean_object* v_xs_2008_, lean_object* v_i_2009_, lean_object* v_x_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Vector_insertIdx_x21(v_00_u03b1_2006_, v_n_2007_, v_xs_2008_, v_i_2009_, v_x_2010_);
lean_dec(v_i_2009_);
lean_dec(v_n_2007_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg(lean_object* v_n_2012_, lean_object* v_xs_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = l_Array_extract___redArg(v_xs_2013_, v___x_2014_, v_n_2012_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg___boxed(lean_object* v_n_2016_, lean_object* v_xs_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Vector_tail___redArg(v_n_2016_, v_xs_2017_);
lean_dec_ref(v_xs_2017_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail(lean_object* v_00_u03b1_2019_, lean_object* v_n_2020_, lean_object* v_xs_2021_){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_unsigned_to_nat(1u);
v___x_2023_ = l_Array_extract___redArg(v_xs_2021_, v___x_2022_, v_n_2020_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___boxed(lean_object* v_00_u03b1_2024_, lean_object* v_n_2025_, lean_object* v_xs_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Vector_tail(v_00_u03b1_2024_, v_n_2025_, v_xs_2026_);
lean_dec_ref(v_xs_2026_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg(lean_object* v_inst_2028_, lean_object* v_xs_2029_, lean_object* v_x_2030_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Array_finIdxOf_x3f___redArg(v_inst_2028_, v_xs_2029_, v_x_2030_);
if (lean_obj_tag(v___x_2031_) == 0)
{
return v___x_2031_;
}
else
{
lean_object* v_val_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
v_val_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_val_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_val_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_2040_, lean_object* v_xs_2041_, lean_object* v_x_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Vector_finIdxOf_x3f___redArg(v_inst_2040_, v_xs_2041_, v_x_2042_);
lean_dec_ref(v_xs_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f(lean_object* v_00_u03b1_2044_, lean_object* v_n_2045_, lean_object* v_inst_2046_, lean_object* v_xs_2047_, lean_object* v_x_2048_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Array_finIdxOf_x3f___redArg(v_inst_2046_, v_xs_2047_, v_x_2048_);
if (lean_obj_tag(v___x_2049_) == 0)
{
return v___x_2049_;
}
else
{
lean_object* v_val_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
v_val_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_val_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_val_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_2058_, lean_object* v_n_2059_, lean_object* v_inst_2060_, lean_object* v_xs_2061_, lean_object* v_x_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Vector_finIdxOf_x3f(v_00_u03b1_2058_, v_n_2059_, v_inst_2060_, v_xs_2061_, v_x_2062_);
lean_dec_ref(v_xs_2061_);
lean_dec(v_n_2059_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg(lean_object* v_p_2064_, lean_object* v_xs_2065_){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = lean_unsigned_to_nat(0u);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2064_, v_xs_2065_, v___x_2066_);
if (lean_obj_tag(v___x_2067_) == 0)
{
return v___x_2067_;
}
else
{
lean_object* v_val_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v_val_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_val_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_val_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2076_, lean_object* v_xs_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Vector_findFinIdx_x3f___redArg(v_p_2076_, v_xs_2077_);
lean_dec_ref(v_xs_2077_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f(lean_object* v_00_u03b1_2079_, lean_object* v_n_2080_, lean_object* v_p_2081_, lean_object* v_xs_2082_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2081_, v_xs_2082_, v___x_2083_);
if (lean_obj_tag(v___x_2084_) == 0)
{
return v___x_2084_;
}
else
{
lean_object* v_val_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
v_val_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_val_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_val_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2093_, lean_object* v_n_2094_, lean_object* v_p_2095_, lean_object* v_xs_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Vector_findFinIdx_x3f(v_00_u03b1_2093_, v_n_2094_, v_p_2095_, v_xs_2096_);
lean_dec_ref(v_xs_2096_);
lean_dec(v_n_2094_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__0(lean_object* v_toPure_2098_, lean_object* v_____s_2099_){
_start:
{
lean_object* v_fst_2100_; 
v_fst_2100_ = lean_ctor_get(v_____s_2099_, 0);
lean_inc(v_fst_2100_);
lean_dec_ref(v_____s_2099_);
if (lean_obj_tag(v_fst_2100_) == 0)
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_box(0);
v___x_2102_ = lean_apply_2(v_toPure_2098_, lean_box(0), v___x_2101_);
return v___x_2102_;
}
else
{
lean_object* v_val_2103_; lean_object* v___x_2104_; 
v_val_2103_ = lean_ctor_get(v_fst_2100_, 0);
lean_inc(v_val_2103_);
lean_dec_ref_known(v_fst_2100_, 1);
v___x_2104_ = lean_apply_2(v_toPure_2098_, lean_box(0), v_val_2103_);
return v___x_2104_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1(lean_object* v___x_2105_, lean_object* v_toPure_2106_, lean_object* v_a_2107_, lean_object* v___x_2108_, uint8_t v_____do__lift_2109_){
_start:
{
if (v_____do__lift_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_dec(v_a_2107_);
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2105_);
v___x_2111_ = lean_apply_2(v_toPure_2106_, lean_box(0), v___x_2110_);
return v___x_2111_;
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref(v___x_2105_);
v___x_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_a_2107_);
v___x_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v___x_2108_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
v___x_2116_ = lean_apply_2(v_toPure_2106_, lean_box(0), v___x_2115_);
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_2117_, lean_object* v_toPure_2118_, lean_object* v_a_2119_, lean_object* v___x_2120_, lean_object* v_____do__lift_2121_){
_start:
{
uint8_t v_____do__lift_124__boxed_2122_; lean_object* v_res_2123_; 
v_____do__lift_124__boxed_2122_ = lean_unbox(v_____do__lift_2121_);
v_res_2123_ = l_Vector_findM_x3f___redArg___lam__1(v___x_2117_, v_toPure_2118_, v_a_2119_, v___x_2120_, v_____do__lift_124__boxed_2122_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2(lean_object* v___x_2124_, lean_object* v_toPure_2125_, lean_object* v___x_2126_, lean_object* v_f_2127_, lean_object* v_toBind_2128_, lean_object* v_a_2129_, lean_object* v_x_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___f_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_inc(v_a_2129_);
v___f_2132_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2132_, 0, v___x_2124_);
lean_closure_set(v___f_2132_, 1, v_toPure_2125_);
lean_closure_set(v___f_2132_, 2, v_a_2129_);
lean_closure_set(v___f_2132_, 3, v___x_2126_);
v___x_2133_ = lean_apply_1(v_f_2127_, v_a_2129_);
v___x_2134_ = lean_apply_4(v_toBind_2128_, lean_box(0), lean_box(0), v___x_2133_, v___f_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2___boxed(lean_object* v___x_2135_, lean_object* v_toPure_2136_, lean_object* v___x_2137_, lean_object* v_f_2138_, lean_object* v_toBind_2139_, lean_object* v_a_2140_, lean_object* v_x_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Vector_findM_x3f___redArg___lam__2(v___x_2135_, v_toPure_2136_, v___x_2137_, v_f_2138_, v_toBind_2139_, v_a_2140_, v_x_2141_, v___y_2142_);
lean_dec_ref(v___y_2142_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg(lean_object* v_inst_2147_, lean_object* v_f_2148_, lean_object* v_as_2149_){
_start:
{
lean_object* v_toApplicative_2150_; lean_object* v_toBind_2151_; lean_object* v_toPure_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___f_2155_; lean_object* v___f_2156_; size_t v_sz_2157_; size_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_toApplicative_2150_ = lean_ctor_get(v_inst_2147_, 0);
v_toBind_2151_ = lean_ctor_get(v_inst_2147_, 1);
lean_inc_n(v_toBind_2151_, 2);
v_toPure_2152_ = lean_ctor_get(v_toApplicative_2150_, 1);
v___x_2153_ = lean_box(0);
v___x_2154_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2152_, 2);
v___f_2155_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2155_, 0, v_toPure_2152_);
v___f_2156_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2156_, 0, v___x_2154_);
lean_closure_set(v___f_2156_, 1, v_toPure_2152_);
lean_closure_set(v___f_2156_, 2, v___x_2153_);
lean_closure_set(v___f_2156_, 3, v_f_2148_);
lean_closure_set(v___f_2156_, 4, v_toBind_2151_);
v_sz_2157_ = lean_array_size(v_as_2149_);
v___x_2158_ = ((size_t)0ULL);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2147_, v_as_2149_, v___f_2156_, v_sz_2157_, v___x_2158_, v___x_2154_);
v___x_2160_ = lean_apply_4(v_toBind_2151_, lean_box(0), lean_box(0), v___x_2159_, v___f_2155_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f(lean_object* v_n_2161_, lean_object* v_00_u03b1_2162_, lean_object* v_m_2163_, lean_object* v_inst_2164_, lean_object* v_f_2165_, lean_object* v_as_2166_){
_start:
{
lean_object* v_toApplicative_2167_; lean_object* v_toBind_2168_; lean_object* v_toPure_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___f_2172_; lean_object* v___f_2173_; size_t v_sz_2174_; size_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_toApplicative_2167_ = lean_ctor_get(v_inst_2164_, 0);
v_toBind_2168_ = lean_ctor_get(v_inst_2164_, 1);
lean_inc_n(v_toBind_2168_, 2);
v_toPure_2169_ = lean_ctor_get(v_toApplicative_2167_, 1);
v___x_2170_ = lean_box(0);
v___x_2171_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2169_, 2);
v___f_2172_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2172_, 0, v_toPure_2169_);
v___f_2173_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2173_, 0, v___x_2171_);
lean_closure_set(v___f_2173_, 1, v_toPure_2169_);
lean_closure_set(v___f_2173_, 2, v___x_2170_);
lean_closure_set(v___f_2173_, 3, v_f_2165_);
lean_closure_set(v___f_2173_, 4, v_toBind_2168_);
v_sz_2174_ = lean_array_size(v_as_2166_);
v___x_2175_ = ((size_t)0ULL);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2164_, v_as_2166_, v___f_2173_, v_sz_2174_, v___x_2175_, v___x_2171_);
v___x_2177_ = lean_apply_4(v_toBind_2168_, lean_box(0), lean_box(0), v___x_2176_, v___f_2172_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___boxed(lean_object* v_n_2178_, lean_object* v_00_u03b1_2179_, lean_object* v_m_2180_, lean_object* v_inst_2181_, lean_object* v_f_2182_, lean_object* v_as_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Vector_findM_x3f(v_n_2178_, v_00_u03b1_2179_, v_m_2180_, v_inst_2181_, v_f_2182_, v_as_2183_);
lean_dec(v_n_2178_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__1(lean_object* v___x_2185_, lean_object* v_toPure_2186_, lean_object* v___x_2187_, lean_object* v_____do__lift_2188_){
_start:
{
if (lean_obj_tag(v_____do__lift_2188_) == 1)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec_ref(v___x_2187_);
v___x_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2189_, 0, v_____do__lift_2188_);
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v___x_2185_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
v___x_2192_ = lean_apply_2(v_toPure_2186_, lean_box(0), v___x_2191_);
return v___x_2192_;
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
lean_dec(v_____do__lift_2188_);
v___x_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2187_);
v___x_2194_ = lean_apply_2(v_toPure_2186_, lean_box(0), v___x_2193_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0(lean_object* v_f_2195_, lean_object* v_toBind_2196_, lean_object* v___f_2197_, lean_object* v_a_2198_, lean_object* v_x_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = lean_apply_1(v_f_2195_, v_a_2198_);
v___x_2202_ = lean_apply_4(v_toBind_2196_, lean_box(0), lean_box(0), v___x_2201_, v___f_2197_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0___boxed(lean_object* v_f_2203_, lean_object* v_toBind_2204_, lean_object* v___f_2205_, lean_object* v_a_2206_, lean_object* v_x_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Vector_findSomeM_x3f___redArg___lam__0(v_f_2203_, v_toBind_2204_, v___f_2205_, v_a_2206_, v_x_2207_, v___y_2208_);
lean_dec_ref(v___y_2208_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg(lean_object* v_inst_2210_, lean_object* v_f_2211_, lean_object* v_as_2212_){
_start:
{
lean_object* v_toApplicative_2213_; lean_object* v_toBind_2214_; lean_object* v_toPure_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___f_2218_; lean_object* v___f_2219_; lean_object* v___f_2220_; size_t v_sz_2221_; size_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_toApplicative_2213_ = lean_ctor_get(v_inst_2210_, 0);
v_toBind_2214_ = lean_ctor_get(v_inst_2210_, 1);
lean_inc_n(v_toBind_2214_, 2);
v_toPure_2215_ = lean_ctor_get(v_toApplicative_2213_, 1);
v___x_2216_ = lean_box(0);
v___x_2217_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2215_, 2);
v___f_2218_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2218_, 0, v_toPure_2215_);
v___f_2219_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2219_, 0, v___x_2216_);
lean_closure_set(v___f_2219_, 1, v_toPure_2215_);
lean_closure_set(v___f_2219_, 2, v___x_2217_);
v___f_2220_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2220_, 0, v_f_2211_);
lean_closure_set(v___f_2220_, 1, v_toBind_2214_);
lean_closure_set(v___f_2220_, 2, v___f_2219_);
v_sz_2221_ = lean_array_size(v_as_2212_);
v___x_2222_ = ((size_t)0ULL);
v___x_2223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2210_, v_as_2212_, v___f_2220_, v_sz_2221_, v___x_2222_, v___x_2217_);
v___x_2224_ = lean_apply_4(v_toBind_2214_, lean_box(0), lean_box(0), v___x_2223_, v___f_2218_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f(lean_object* v_m_2225_, lean_object* v_00_u03b1_2226_, lean_object* v_00_u03b2_2227_, lean_object* v_n_2228_, lean_object* v_inst_2229_, lean_object* v_f_2230_, lean_object* v_as_2231_){
_start:
{
lean_object* v_toApplicative_2232_; lean_object* v_toBind_2233_; lean_object* v_toPure_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___f_2237_; lean_object* v___f_2238_; lean_object* v___f_2239_; size_t v_sz_2240_; size_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v_toApplicative_2232_ = lean_ctor_get(v_inst_2229_, 0);
v_toBind_2233_ = lean_ctor_get(v_inst_2229_, 1);
lean_inc_n(v_toBind_2233_, 2);
v_toPure_2234_ = lean_ctor_get(v_toApplicative_2232_, 1);
v___x_2235_ = lean_box(0);
v___x_2236_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2234_, 2);
v___f_2237_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2237_, 0, v_toPure_2234_);
v___f_2238_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2238_, 0, v___x_2235_);
lean_closure_set(v___f_2238_, 1, v_toPure_2234_);
lean_closure_set(v___f_2238_, 2, v___x_2236_);
v___f_2239_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2239_, 0, v_f_2230_);
lean_closure_set(v___f_2239_, 1, v_toBind_2233_);
lean_closure_set(v___f_2239_, 2, v___f_2238_);
v_sz_2240_ = lean_array_size(v_as_2231_);
v___x_2241_ = ((size_t)0ULL);
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2229_, v_as_2231_, v___f_2239_, v_sz_2240_, v___x_2241_, v___x_2236_);
v___x_2243_ = lean_apply_4(v_toBind_2233_, lean_box(0), lean_box(0), v___x_2242_, v___f_2237_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___boxed(lean_object* v_m_2244_, lean_object* v_00_u03b1_2245_, lean_object* v_00_u03b2_2246_, lean_object* v_n_2247_, lean_object* v_inst_2248_, lean_object* v_f_2249_, lean_object* v_as_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Vector_findSomeM_x3f(v_m_2244_, v_00_u03b1_2245_, v_00_u03b2_2246_, v_n_2247_, v_inst_2248_, v_f_2249_, v_as_2250_);
lean_dec(v_n_2247_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2252_, lean_object* v_a_2253_, uint8_t v_____do__lift_2254_){
_start:
{
if (v_____do__lift_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec(v_a_2253_);
v___x_2255_ = lean_box(0);
v___x_2256_ = lean_apply_2(v_toPure_2252_, lean_box(0), v___x_2255_);
return v___x_2256_;
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v_a_2253_);
v___x_2258_ = lean_apply_2(v_toPure_2252_, lean_box(0), v___x_2257_);
return v___x_2258_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2259_, lean_object* v_a_2260_, lean_object* v_____do__lift_2261_){
_start:
{
uint8_t v_____do__lift_50__boxed_2262_; lean_object* v_res_2263_; 
v_____do__lift_50__boxed_2262_ = lean_unbox(v_____do__lift_2261_);
v_res_2263_ = l_Vector_findRevM_x3f___redArg___lam__0(v_toPure_2259_, v_a_2260_, v_____do__lift_50__boxed_2262_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2264_, lean_object* v_f_2265_, lean_object* v_toBind_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v___f_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_inc(v_a_2267_);
v___f_2268_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2268_, 0, v_toPure_2264_);
lean_closure_set(v___f_2268_, 1, v_a_2267_);
v___x_2269_ = lean_apply_1(v_f_2265_, v_a_2267_);
v___x_2270_ = lean_apply_4(v_toBind_2266_, lean_box(0), lean_box(0), v___x_2269_, v___f_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg(lean_object* v_inst_2271_, lean_object* v_f_2272_, lean_object* v_as_2273_){
_start:
{
lean_object* v_toApplicative_2274_; lean_object* v_toBind_2275_; lean_object* v_toPure_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_toApplicative_2274_ = lean_ctor_get(v_inst_2271_, 0);
v_toBind_2275_ = lean_ctor_get(v_inst_2271_, 1);
v_toPure_2276_ = lean_ctor_get(v_toApplicative_2274_, 1);
lean_inc(v_toBind_2275_);
lean_inc(v_toPure_2276_);
v___f_2277_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2277_, 0, v_toPure_2276_);
lean_closure_set(v___f_2277_, 1, v_f_2272_);
lean_closure_set(v___f_2277_, 2, v_toBind_2275_);
v___x_2278_ = lean_array_get_size(v_as_2273_);
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2271_, v___f_2277_, v_as_2273_, v___x_2278_, lean_box(0));
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f(lean_object* v_n_2280_, lean_object* v_00_u03b1_2281_, lean_object* v_m_2282_, lean_object* v_inst_2283_, lean_object* v_f_2284_, lean_object* v_as_2285_){
_start:
{
lean_object* v_toApplicative_2286_; lean_object* v_toBind_2287_; lean_object* v_toPure_2288_; lean_object* v___f_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_toApplicative_2286_ = lean_ctor_get(v_inst_2283_, 0);
v_toBind_2287_ = lean_ctor_get(v_inst_2283_, 1);
v_toPure_2288_ = lean_ctor_get(v_toApplicative_2286_, 1);
lean_inc(v_toBind_2287_);
lean_inc(v_toPure_2288_);
v___f_2289_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2289_, 0, v_toPure_2288_);
lean_closure_set(v___f_2289_, 1, v_f_2284_);
lean_closure_set(v___f_2289_, 2, v_toBind_2287_);
v___x_2290_ = lean_array_get_size(v_as_2285_);
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2283_, v___f_2289_, v_as_2285_, v___x_2290_, lean_box(0));
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___boxed(lean_object* v_n_2292_, lean_object* v_00_u03b1_2293_, lean_object* v_m_2294_, lean_object* v_inst_2295_, lean_object* v_f_2296_, lean_object* v_as_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Vector_findRevM_x3f(v_n_2292_, v_00_u03b1_2293_, v_m_2294_, v_inst_2295_, v_f_2296_, v_as_2297_);
lean_dec(v_n_2292_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___redArg(lean_object* v_inst_2299_, lean_object* v_f_2300_, lean_object* v_as_2301_){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = lean_array_get_size(v_as_2301_);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2299_, v_f_2300_, v_as_2301_, v___x_2302_, lean_box(0));
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f(lean_object* v_m_2304_, lean_object* v_00_u03b1_2305_, lean_object* v_00_u03b2_2306_, lean_object* v_n_2307_, lean_object* v_inst_2308_, lean_object* v_f_2309_, lean_object* v_as_2310_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_array_get_size(v_as_2310_);
v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2308_, v_f_2309_, v_as_2310_, v___x_2311_, lean_box(0));
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___boxed(lean_object* v_m_2313_, lean_object* v_00_u03b1_2314_, lean_object* v_00_u03b2_2315_, lean_object* v_n_2316_, lean_object* v_inst_2317_, lean_object* v_f_2318_, lean_object* v_as_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Vector_findSomeRevM_x3f(v_m_2313_, v_00_u03b1_2314_, v_00_u03b2_2315_, v_n_2316_, v_inst_2317_, v_f_2318_, v_as_2319_);
lean_dec(v_n_2316_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0(lean_object* v_f_2321_, lean_object* v___x_2322_, lean_object* v___x_2323_, lean_object* v_a_2324_, lean_object* v_x_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
lean_inc(v_a_2324_);
v___x_2327_ = lean_apply_1(v_f_2321_, v_a_2324_);
v___x_2328_ = lean_unbox(v___x_2327_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; 
lean_dec(v_a_2324_);
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2322_);
return v___x_2329_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_dec_ref(v___x_2322_);
v___x_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2330_, 0, v_a_2324_);
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___x_2323_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
return v___x_2333_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0___boxed(lean_object* v_f_2334_, lean_object* v___x_2335_, lean_object* v___x_2336_, lean_object* v_a_2337_, lean_object* v_x_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Vector_find_x3f___redArg___lam__0(v_f_2334_, v___x_2335_, v___x_2336_, v_a_2337_, v_x_2338_, v___y_2339_);
lean_dec_ref(v___y_2339_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg(lean_object* v_f_2341_, lean_object* v_as_2342_){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___f_2347_; size_t v_sz_2348_; size_t v___x_2349_; lean_object* v___x_2350_; lean_object* v_fst_2351_; 
v___x_2343_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_box(0);
v___x_2346_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2347_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2347_, 0, v_f_2341_);
lean_closure_set(v___f_2347_, 1, v___x_2346_);
lean_closure_set(v___f_2347_, 2, v___x_2345_);
v_sz_2348_ = lean_array_size(v_as_2342_);
v___x_2349_ = ((size_t)0ULL);
v___x_2350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2343_, v_as_2342_, v___f_2347_, v_sz_2348_, v___x_2349_, v___x_2346_);
v_fst_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_fst_2351_);
lean_dec(v___x_2350_);
if (lean_obj_tag(v_fst_2351_) == 0)
{
return v___x_2344_;
}
else
{
lean_object* v_val_2352_; 
v_val_2352_ = lean_ctor_get(v_fst_2351_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v_fst_2351_, 1);
return v_val_2352_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f(lean_object* v_n_2353_, lean_object* v_00_u03b1_2354_, lean_object* v_f_2355_, lean_object* v_as_2356_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___f_2361_; size_t v_sz_2362_; size_t v___x_2363_; lean_object* v___x_2364_; lean_object* v_fst_2365_; 
v___x_2357_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_box(0);
v___x_2360_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2361_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2361_, 0, v_f_2355_);
lean_closure_set(v___f_2361_, 1, v___x_2360_);
lean_closure_set(v___f_2361_, 2, v___x_2359_);
v_sz_2362_ = lean_array_size(v_as_2356_);
v___x_2363_ = ((size_t)0ULL);
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2357_, v_as_2356_, v___f_2361_, v_sz_2362_, v___x_2363_, v___x_2360_);
v_fst_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_fst_2365_);
lean_dec(v___x_2364_);
if (lean_obj_tag(v_fst_2365_) == 0)
{
return v___x_2358_;
}
else
{
lean_object* v_val_2366_; 
v_val_2366_ = lean_ctor_get(v_fst_2365_, 0);
lean_inc(v_val_2366_);
lean_dec_ref_known(v_fst_2365_, 1);
return v_val_2366_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___boxed(lean_object* v_n_2367_, lean_object* v_00_u03b1_2368_, lean_object* v_f_2369_, lean_object* v_as_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Vector_find_x3f(v_n_2367_, v_00_u03b1_2368_, v_f_2369_, v_as_2370_);
lean_dec(v_n_2367_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg___lam__0(lean_object* v_f_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
lean_inc(v_a_2373_);
v___x_2374_ = lean_apply_1(v_f_2372_, v_a_2373_);
v___x_2375_ = lean_unbox(v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
lean_dec(v_a_2373_);
v___x_2376_ = lean_box(0);
return v___x_2376_;
}
else
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2377_, 0, v_a_2373_);
return v___x_2377_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg(lean_object* v_f_2378_, lean_object* v_as_2379_){
_start:
{
lean_object* v___f_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___f_2380_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2380_, 0, v_f_2378_);
v___x_2381_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2382_ = lean_array_get_size(v_as_2379_);
v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2381_, v___f_2380_, v_as_2379_, v___x_2382_, lean_box(0));
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f(lean_object* v_n_2384_, lean_object* v_00_u03b1_2385_, lean_object* v_f_2386_, lean_object* v_as_2387_){
_start:
{
lean_object* v___f_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___f_2388_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2388_, 0, v_f_2386_);
v___x_2389_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2390_ = lean_array_get_size(v_as_2387_);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2389_, v___f_2388_, v_as_2387_, v___x_2390_, lean_box(0));
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___boxed(lean_object* v_n_2392_, lean_object* v_00_u03b1_2393_, lean_object* v_f_2394_, lean_object* v_as_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Vector_findRev_x3f(v_n_2392_, v_00_u03b1_2393_, v_f_2394_, v_as_2395_);
lean_dec(v_n_2392_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0(lean_object* v_f_2397_, lean_object* v___x_2398_, lean_object* v___x_2399_, lean_object* v_a_2400_, lean_object* v_x_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = lean_apply_1(v_f_2397_, v_a_2400_);
if (lean_obj_tag(v___x_2403_) == 1)
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_dec_ref(v___x_2399_);
v___x_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
lean_ctor_set(v___x_2405_, 1, v___x_2398_);
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
else
{
lean_object* v___x_2407_; 
lean_dec(v___x_2403_);
v___x_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2399_);
return v___x_2407_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2408_, lean_object* v___x_2409_, lean_object* v___x_2410_, lean_object* v_a_2411_, lean_object* v_x_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Vector_findSome_x3f___redArg___lam__0(v_f_2408_, v___x_2409_, v___x_2410_, v_a_2411_, v_x_2412_, v___y_2413_);
lean_dec_ref(v___y_2413_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg(lean_object* v_f_2415_, lean_object* v_as_2416_){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___f_2421_; size_t v_sz_2422_; size_t v___x_2423_; lean_object* v___x_2424_; lean_object* v_fst_2425_; 
v___x_2417_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2418_ = lean_box(0);
v___x_2419_ = lean_box(0);
v___x_2420_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2421_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2421_, 0, v_f_2415_);
lean_closure_set(v___f_2421_, 1, v___x_2419_);
lean_closure_set(v___f_2421_, 2, v___x_2420_);
v_sz_2422_ = lean_array_size(v_as_2416_);
v___x_2423_ = ((size_t)0ULL);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2417_, v_as_2416_, v___f_2421_, v_sz_2422_, v___x_2423_, v___x_2420_);
v_fst_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_fst_2425_);
lean_dec(v___x_2424_);
if (lean_obj_tag(v_fst_2425_) == 0)
{
return v___x_2418_;
}
else
{
lean_object* v_val_2426_; 
v_val_2426_ = lean_ctor_get(v_fst_2425_, 0);
lean_inc(v_val_2426_);
lean_dec_ref_known(v_fst_2425_, 1);
return v_val_2426_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f(lean_object* v_00_u03b1_2427_, lean_object* v_00_u03b2_2428_, lean_object* v_n_2429_, lean_object* v_f_2430_, lean_object* v_as_2431_){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___f_2436_; size_t v_sz_2437_; size_t v___x_2438_; lean_object* v___x_2439_; lean_object* v_fst_2440_; 
v___x_2432_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2433_ = lean_box(0);
v___x_2434_ = lean_box(0);
v___x_2435_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2436_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2436_, 0, v_f_2430_);
lean_closure_set(v___f_2436_, 1, v___x_2434_);
lean_closure_set(v___f_2436_, 2, v___x_2435_);
v_sz_2437_ = lean_array_size(v_as_2431_);
v___x_2438_ = ((size_t)0ULL);
v___x_2439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2432_, v_as_2431_, v___f_2436_, v_sz_2437_, v___x_2438_, v___x_2435_);
v_fst_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_fst_2440_);
lean_dec(v___x_2439_);
if (lean_obj_tag(v_fst_2440_) == 0)
{
return v___x_2433_;
}
else
{
lean_object* v_val_2441_; 
v_val_2441_ = lean_ctor_get(v_fst_2440_, 0);
lean_inc(v_val_2441_);
lean_dec_ref_known(v_fst_2440_, 1);
return v_val_2441_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___boxed(lean_object* v_00_u03b1_2442_, lean_object* v_00_u03b2_2443_, lean_object* v_n_2444_, lean_object* v_f_2445_, lean_object* v_as_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Vector_findSome_x3f(v_00_u03b1_2442_, v_00_u03b2_2443_, v_n_2444_, v_f_2445_, v_as_2446_);
lean_dec(v_n_2444_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2448_, lean_object* v_x_2449_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_apply_1(v_f_2448_, v_x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg(lean_object* v_f_2451_, lean_object* v_as_2452_){
_start:
{
lean_object* v___f_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___f_2453_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2453_, 0, v_f_2451_);
v___x_2454_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2455_ = lean_array_get_size(v_as_2452_);
v___x_2456_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2454_, v___f_2453_, v_as_2452_, v___x_2455_, lean_box(0));
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f(lean_object* v_00_u03b1_2457_, lean_object* v_00_u03b2_2458_, lean_object* v_n_2459_, lean_object* v_f_2460_, lean_object* v_as_2461_){
_start:
{
lean_object* v___f_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___f_2462_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2462_, 0, v_f_2460_);
v___x_2463_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2464_ = lean_array_get_size(v_as_2461_);
v___x_2465_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2463_, v___f_2462_, v_as_2461_, v___x_2464_, lean_box(0));
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___boxed(lean_object* v_00_u03b1_2466_, lean_object* v_00_u03b2_2467_, lean_object* v_n_2468_, lean_object* v_f_2469_, lean_object* v_as_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Vector_findSomeRev_x3f(v_00_u03b1_2466_, v_00_u03b2_2467_, v_n_2468_, v_f_2469_, v_as_2470_);
lean_dec(v_n_2468_);
return v_res_2471_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf___redArg(lean_object* v_inst_2472_, lean_object* v_xs_2473_, lean_object* v_ys_2474_){
_start:
{
uint8_t v___x_2475_; 
v___x_2475_ = l_Array_isPrefixOf___redArg(v_inst_2472_, v_xs_2473_, v_ys_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___redArg___boxed(lean_object* v_inst_2476_, lean_object* v_xs_2477_, lean_object* v_ys_2478_){
_start:
{
uint8_t v_res_2479_; lean_object* v_r_2480_; 
v_res_2479_ = l_Vector_isPrefixOf___redArg(v_inst_2476_, v_xs_2477_, v_ys_2478_);
lean_dec_ref(v_ys_2478_);
lean_dec_ref(v_xs_2477_);
v_r_2480_ = lean_box(v_res_2479_);
return v_r_2480_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf(lean_object* v_00_u03b1_2481_, lean_object* v_m_2482_, lean_object* v_n_2483_, lean_object* v_inst_2484_, lean_object* v_xs_2485_, lean_object* v_ys_2486_){
_start:
{
uint8_t v___x_2487_; 
v___x_2487_ = l_Array_isPrefixOf___redArg(v_inst_2484_, v_xs_2485_, v_ys_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___boxed(lean_object* v_00_u03b1_2488_, lean_object* v_m_2489_, lean_object* v_n_2490_, lean_object* v_inst_2491_, lean_object* v_xs_2492_, lean_object* v_ys_2493_){
_start:
{
uint8_t v_res_2494_; lean_object* v_r_2495_; 
v_res_2494_ = l_Vector_isPrefixOf(v_00_u03b1_2488_, v_m_2489_, v_n_2490_, v_inst_2491_, v_xs_2492_, v_ys_2493_);
lean_dec_ref(v_ys_2493_);
lean_dec_ref(v_xs_2492_);
lean_dec(v_n_2490_);
lean_dec(v_m_2489_);
v_r_2495_ = lean_box(v_res_2494_);
return v_r_2495_;
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___redArg(lean_object* v_inst_2496_, lean_object* v_p_2497_, lean_object* v_xs_2498_){
_start:
{
lean_object* v_toApplicative_2499_; lean_object* v_toPure_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v_toApplicative_2499_ = lean_ctor_get(v_inst_2496_, 0);
v_toPure_2500_ = lean_ctor_get(v_toApplicative_2499_, 1);
v___x_2501_ = lean_unsigned_to_nat(0u);
v___x_2502_ = lean_array_get_size(v_xs_2498_);
v___x_2503_ = lean_nat_dec_lt(v___x_2501_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_inc(v_toPure_2500_);
lean_dec_ref(v_xs_2498_);
lean_dec(v_p_2497_);
lean_dec_ref(v_inst_2496_);
v___x_2504_ = lean_box(v___x_2503_);
v___x_2505_ = lean_apply_2(v_toPure_2500_, lean_box(0), v___x_2504_);
return v___x_2505_;
}
else
{
if (v___x_2503_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_inc(v_toPure_2500_);
lean_dec_ref(v_xs_2498_);
lean_dec(v_p_2497_);
lean_dec_ref(v_inst_2496_);
v___x_2506_ = lean_box(v___x_2503_);
v___x_2507_ = lean_apply_2(v_toPure_2500_, lean_box(0), v___x_2506_);
return v___x_2507_;
}
else
{
size_t v___x_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = ((size_t)0ULL);
v___x_2509_ = lean_usize_of_nat(v___x_2502_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2496_, v_p_2497_, v_xs_2498_, v___x_2508_, v___x_2509_);
return v___x_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM(lean_object* v_m_2511_, lean_object* v_00_u03b1_2512_, lean_object* v_n_2513_, lean_object* v_inst_2514_, lean_object* v_p_2515_, lean_object* v_xs_2516_){
_start:
{
lean_object* v_toApplicative_2517_; lean_object* v_toPure_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v_toApplicative_2517_ = lean_ctor_get(v_inst_2514_, 0);
v_toPure_2518_ = lean_ctor_get(v_toApplicative_2517_, 1);
v___x_2519_ = lean_unsigned_to_nat(0u);
v___x_2520_ = lean_array_get_size(v_xs_2516_);
v___x_2521_ = lean_nat_dec_lt(v___x_2519_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_inc(v_toPure_2518_);
lean_dec_ref(v_xs_2516_);
lean_dec(v_p_2515_);
lean_dec_ref(v_inst_2514_);
v___x_2522_ = lean_box(v___x_2521_);
v___x_2523_ = lean_apply_2(v_toPure_2518_, lean_box(0), v___x_2522_);
return v___x_2523_;
}
else
{
if (v___x_2521_ == 0)
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_inc(v_toPure_2518_);
lean_dec_ref(v_xs_2516_);
lean_dec(v_p_2515_);
lean_dec_ref(v_inst_2514_);
v___x_2524_ = lean_box(v___x_2521_);
v___x_2525_ = lean_apply_2(v_toPure_2518_, lean_box(0), v___x_2524_);
return v___x_2525_;
}
else
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((size_t)0ULL);
v___x_2527_ = lean_usize_of_nat(v___x_2520_);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2514_, v_p_2515_, v_xs_2516_, v___x_2526_, v___x_2527_);
return v___x_2528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___boxed(lean_object* v_m_2529_, lean_object* v_00_u03b1_2530_, lean_object* v_n_2531_, lean_object* v_inst_2532_, lean_object* v_p_2533_, lean_object* v_xs_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Vector_anyM(v_m_2529_, v_00_u03b1_2530_, v_n_2531_, v_inst_2532_, v_p_2533_, v_xs_2534_);
lean_dec(v_n_2531_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0(lean_object* v_toPure_2536_, uint8_t v_____do__lift_2537_){
_start:
{
if (v_____do__lift_2537_ == 0)
{
uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = 1;
v___x_2539_ = lean_box(v___x_2538_);
v___x_2540_ = lean_apply_2(v_toPure_2536_, lean_box(0), v___x_2539_);
return v___x_2540_;
}
else
{
uint8_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = 0;
v___x_2542_ = lean_box(v___x_2541_);
v___x_2543_ = lean_apply_2(v_toPure_2536_, lean_box(0), v___x_2542_);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0___boxed(lean_object* v_toPure_2544_, lean_object* v_____do__lift_2545_){
_start:
{
uint8_t v_____do__lift_112__boxed_2546_; lean_object* v_res_2547_; 
v_____do__lift_112__boxed_2546_ = lean_unbox(v_____do__lift_2545_);
v_res_2547_ = l_Vector_allM___redArg___lam__0(v_toPure_2544_, v_____do__lift_112__boxed_2546_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1(lean_object* v_toPure_2548_, uint8_t v___x_2549_, uint8_t v_____do__lift_2550_){
_start:
{
if (v_____do__lift_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_box(v___x_2549_);
v___x_2552_ = lean_apply_2(v_toPure_2548_, lean_box(0), v___x_2551_);
return v___x_2552_;
}
else
{
uint8_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = 0;
v___x_2554_ = lean_box(v___x_2553_);
v___x_2555_ = lean_apply_2(v_toPure_2548_, lean_box(0), v___x_2554_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1___boxed(lean_object* v_toPure_2556_, lean_object* v___x_2557_, lean_object* v_____do__lift_2558_){
_start:
{
uint8_t v___x_127__boxed_2559_; uint8_t v_____do__lift_128__boxed_2560_; lean_object* v_res_2561_; 
v___x_127__boxed_2559_ = lean_unbox(v___x_2557_);
v_____do__lift_128__boxed_2560_ = lean_unbox(v_____do__lift_2558_);
v_res_2561_ = l_Vector_allM___redArg___lam__1(v_toPure_2556_, v___x_127__boxed_2559_, v_____do__lift_128__boxed_2560_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__2(lean_object* v_p_2562_, lean_object* v_toBind_2563_, lean_object* v___f_2564_, lean_object* v_v_2565_){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = lean_apply_1(v_p_2562_, v_v_2565_);
v___x_2567_ = lean_apply_4(v_toBind_2563_, lean_box(0), lean_box(0), v___x_2566_, v___f_2564_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg(lean_object* v_inst_2568_, lean_object* v_p_2569_, lean_object* v_xs_2570_){
_start:
{
lean_object* v_toApplicative_2571_; lean_object* v_toBind_2572_; lean_object* v_toPure_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___f_2576_; uint8_t v___x_2577_; 
v_toApplicative_2571_ = lean_ctor_get(v_inst_2568_, 0);
v_toBind_2572_ = lean_ctor_get(v_inst_2568_, 1);
lean_inc(v_toBind_2572_);
v_toPure_2573_ = lean_ctor_get(v_toApplicative_2571_, 1);
v___x_2574_ = lean_unsigned_to_nat(0u);
v___x_2575_ = lean_array_get_size(v_xs_2570_);
lean_inc(v_toPure_2573_);
v___f_2576_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2576_, 0, v_toPure_2573_);
v___x_2577_ = lean_nat_dec_lt(v___x_2574_, v___x_2575_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_inc(v_toPure_2573_);
lean_dec_ref(v_xs_2570_);
lean_dec(v_p_2569_);
lean_dec_ref(v_inst_2568_);
v___x_2578_ = lean_box(v___x_2577_);
v___x_2579_ = lean_apply_2(v_toPure_2573_, lean_box(0), v___x_2578_);
v___x_2580_ = lean_apply_4(v_toBind_2572_, lean_box(0), lean_box(0), v___x_2579_, v___f_2576_);
return v___x_2580_;
}
else
{
if (v___x_2577_ == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_inc(v_toPure_2573_);
lean_dec_ref(v_xs_2570_);
lean_dec(v_p_2569_);
lean_dec_ref(v_inst_2568_);
v___x_2581_ = lean_box(v___x_2577_);
v___x_2582_ = lean_apply_2(v_toPure_2573_, lean_box(0), v___x_2581_);
v___x_2583_ = lean_apply_4(v_toBind_2572_, lean_box(0), lean_box(0), v___x_2582_, v___f_2576_);
return v___x_2583_;
}
else
{
lean_object* v___x_2584_; lean_object* v___f_2585_; lean_object* v___f_2586_; size_t v___x_2587_; size_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2584_ = lean_box(v___x_2577_);
lean_inc(v_toPure_2573_);
v___f_2585_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2585_, 0, v_toPure_2573_);
lean_closure_set(v___f_2585_, 1, v___x_2584_);
lean_inc(v_toBind_2572_);
v___f_2586_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2586_, 0, v_p_2569_);
lean_closure_set(v___f_2586_, 1, v_toBind_2572_);
lean_closure_set(v___f_2586_, 2, v___f_2585_);
v___x_2587_ = ((size_t)0ULL);
v___x_2588_ = lean_usize_of_nat(v___x_2575_);
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2568_, v___f_2586_, v_xs_2570_, v___x_2587_, v___x_2588_);
v___x_2590_ = lean_apply_4(v_toBind_2572_, lean_box(0), lean_box(0), v___x_2589_, v___f_2576_);
return v___x_2590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM(lean_object* v_m_2591_, lean_object* v_00_u03b1_2592_, lean_object* v_n_2593_, lean_object* v_inst_2594_, lean_object* v_p_2595_, lean_object* v_xs_2596_){
_start:
{
lean_object* v_toApplicative_2597_; lean_object* v_toBind_2598_; lean_object* v_toPure_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___f_2602_; uint8_t v___x_2603_; 
v_toApplicative_2597_ = lean_ctor_get(v_inst_2594_, 0);
v_toBind_2598_ = lean_ctor_get(v_inst_2594_, 1);
lean_inc(v_toBind_2598_);
v_toPure_2599_ = lean_ctor_get(v_toApplicative_2597_, 1);
v___x_2600_ = lean_unsigned_to_nat(0u);
v___x_2601_ = lean_array_get_size(v_xs_2596_);
lean_inc(v_toPure_2599_);
v___f_2602_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2602_, 0, v_toPure_2599_);
v___x_2603_ = lean_nat_dec_lt(v___x_2600_, v___x_2601_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_inc(v_toPure_2599_);
lean_dec_ref(v_xs_2596_);
lean_dec(v_p_2595_);
lean_dec_ref(v_inst_2594_);
v___x_2604_ = lean_box(v___x_2603_);
v___x_2605_ = lean_apply_2(v_toPure_2599_, lean_box(0), v___x_2604_);
v___x_2606_ = lean_apply_4(v_toBind_2598_, lean_box(0), lean_box(0), v___x_2605_, v___f_2602_);
return v___x_2606_;
}
else
{
if (v___x_2603_ == 0)
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_inc(v_toPure_2599_);
lean_dec_ref(v_xs_2596_);
lean_dec(v_p_2595_);
lean_dec_ref(v_inst_2594_);
v___x_2607_ = lean_box(v___x_2603_);
v___x_2608_ = lean_apply_2(v_toPure_2599_, lean_box(0), v___x_2607_);
v___x_2609_ = lean_apply_4(v_toBind_2598_, lean_box(0), lean_box(0), v___x_2608_, v___f_2602_);
return v___x_2609_;
}
else
{
lean_object* v___x_2610_; lean_object* v___f_2611_; lean_object* v___f_2612_; size_t v___x_2613_; size_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2610_ = lean_box(v___x_2603_);
lean_inc(v_toPure_2599_);
v___f_2611_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2611_, 0, v_toPure_2599_);
lean_closure_set(v___f_2611_, 1, v___x_2610_);
lean_inc(v_toBind_2598_);
v___f_2612_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2612_, 0, v_p_2595_);
lean_closure_set(v___f_2612_, 1, v_toBind_2598_);
lean_closure_set(v___f_2612_, 2, v___f_2611_);
v___x_2613_ = ((size_t)0ULL);
v___x_2614_ = lean_usize_of_nat(v___x_2601_);
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2594_, v___f_2612_, v_xs_2596_, v___x_2613_, v___x_2614_);
v___x_2616_ = lean_apply_4(v_toBind_2598_, lean_box(0), lean_box(0), v___x_2615_, v___f_2602_);
return v___x_2616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___boxed(lean_object* v_m_2617_, lean_object* v_00_u03b1_2618_, lean_object* v_n_2619_, lean_object* v_inst_2620_, lean_object* v_p_2621_, lean_object* v_xs_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Vector_allM(v_m_2617_, v_00_u03b1_2618_, v_n_2619_, v_inst_2620_, v_p_2621_, v_xs_2622_);
lean_dec(v_n_2619_);
return v_res_2623_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg___lam__0(lean_object* v_p_2624_, lean_object* v_x_2625_){
_start:
{
lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = lean_apply_1(v_p_2624_, v_x_2625_);
v___x_2627_ = lean_unbox(v___x_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___lam__0___boxed(lean_object* v_p_2628_, lean_object* v_x_2629_){
_start:
{
uint8_t v_res_2630_; lean_object* v_r_2631_; 
v_res_2630_ = l_Vector_any___redArg___lam__0(v_p_2628_, v_x_2629_);
v_r_2631_ = lean_box(v_res_2630_);
return v_r_2631_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg(lean_object* v_xs_2632_, lean_object* v_p_2633_){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = lean_array_get_size(v_xs_2632_);
v___x_2636_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2637_ = lean_nat_dec_lt(v___x_2634_, v___x_2635_);
if (v___x_2637_ == 0)
{
lean_dec_ref(v_p_2633_);
lean_dec_ref(v_xs_2632_);
return v___x_2637_;
}
else
{
if (v___x_2637_ == 0)
{
lean_dec_ref(v_p_2633_);
lean_dec_ref(v_xs_2632_);
return v___x_2637_;
}
else
{
lean_object* v___f_2638_; size_t v___x_2639_; size_t v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___f_2638_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2638_, 0, v_p_2633_);
v___x_2639_ = ((size_t)0ULL);
v___x_2640_ = lean_usize_of_nat(v___x_2635_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2636_, v___f_2638_, v_xs_2632_, v___x_2639_, v___x_2640_);
v___x_2642_ = lean_unbox(v___x_2641_);
lean_dec(v___x_2641_);
return v___x_2642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___boxed(lean_object* v_xs_2643_, lean_object* v_p_2644_){
_start:
{
uint8_t v_res_2645_; lean_object* v_r_2646_; 
v_res_2645_ = l_Vector_any___redArg(v_xs_2643_, v_p_2644_);
v_r_2646_ = lean_box(v_res_2645_);
return v_r_2646_;
}
}
LEAN_EXPORT uint8_t l_Vector_any(lean_object* v_00_u03b1_2647_, lean_object* v_n_2648_, lean_object* v_xs_2649_, lean_object* v_p_2650_){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v___x_2651_ = lean_unsigned_to_nat(0u);
v___x_2652_ = lean_array_get_size(v_xs_2649_);
v___x_2653_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2654_ = lean_nat_dec_lt(v___x_2651_, v___x_2652_);
if (v___x_2654_ == 0)
{
lean_dec_ref(v_p_2650_);
lean_dec_ref(v_xs_2649_);
return v___x_2654_;
}
else
{
if (v___x_2654_ == 0)
{
lean_dec_ref(v_p_2650_);
lean_dec_ref(v_xs_2649_);
return v___x_2654_;
}
else
{
lean_object* v___f_2655_; size_t v___x_2656_; size_t v___x_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v___f_2655_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2655_, 0, v_p_2650_);
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = lean_usize_of_nat(v___x_2652_);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2653_, v___f_2655_, v_xs_2649_, v___x_2656_, v___x_2657_);
v___x_2659_ = lean_unbox(v___x_2658_);
lean_dec(v___x_2658_);
return v___x_2659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___boxed(lean_object* v_00_u03b1_2660_, lean_object* v_n_2661_, lean_object* v_xs_2662_, lean_object* v_p_2663_){
_start:
{
uint8_t v_res_2664_; lean_object* v_r_2665_; 
v_res_2664_ = l_Vector_any(v_00_u03b1_2660_, v_n_2661_, v_xs_2662_, v_p_2663_);
lean_dec(v_n_2661_);
v_r_2665_ = lean_box(v_res_2664_);
return v_r_2665_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg___lam__0(lean_object* v_p_2666_, uint8_t v___x_2667_, lean_object* v_v_2668_){
_start:
{
lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2669_ = lean_apply_1(v_p_2666_, v_v_2668_);
v___x_2670_ = lean_unbox(v___x_2669_);
if (v___x_2670_ == 0)
{
return v___x_2667_;
}
else
{
uint8_t v___x_2671_; 
v___x_2671_ = 0;
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___lam__0___boxed(lean_object* v_p_2672_, lean_object* v___x_2673_, lean_object* v_v_2674_){
_start:
{
uint8_t v___x_75__boxed_2675_; uint8_t v_res_2676_; lean_object* v_r_2677_; 
v___x_75__boxed_2675_ = lean_unbox(v___x_2673_);
v_res_2676_ = l_Vector_all___redArg___lam__0(v_p_2672_, v___x_75__boxed_2675_, v_v_2674_);
v_r_2677_ = lean_box(v_res_2676_);
return v_r_2677_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg(lean_object* v_xs_2678_, lean_object* v_p_2679_){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2680_ = lean_unsigned_to_nat(0u);
v___x_2681_ = lean_array_get_size(v_xs_2678_);
v___x_2682_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2683_ = lean_nat_dec_lt(v___x_2680_, v___x_2681_);
if (v___x_2683_ == 0)
{
uint8_t v___x_2684_; 
lean_dec_ref(v_p_2679_);
lean_dec_ref(v_xs_2678_);
v___x_2684_ = 1;
return v___x_2684_;
}
else
{
if (v___x_2683_ == 0)
{
lean_dec_ref(v_p_2679_);
lean_dec_ref(v_xs_2678_);
return v___x_2683_;
}
else
{
lean_object* v___x_2685_; lean_object* v___f_2686_; size_t v___x_2687_; size_t v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2685_ = lean_box(v___x_2683_);
v___f_2686_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2686_, 0, v_p_2679_);
lean_closure_set(v___f_2686_, 1, v___x_2685_);
v___x_2687_ = ((size_t)0ULL);
v___x_2688_ = lean_usize_of_nat(v___x_2681_);
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2682_, v___f_2686_, v_xs_2678_, v___x_2687_, v___x_2688_);
v___x_2690_ = lean_unbox(v___x_2689_);
lean_dec(v___x_2689_);
if (v___x_2690_ == 0)
{
return v___x_2683_;
}
else
{
uint8_t v___x_2691_; 
v___x_2691_ = 0;
return v___x_2691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___boxed(lean_object* v_xs_2692_, lean_object* v_p_2693_){
_start:
{
uint8_t v_res_2694_; lean_object* v_r_2695_; 
v_res_2694_ = l_Vector_all___redArg(v_xs_2692_, v_p_2693_);
v_r_2695_ = lean_box(v_res_2694_);
return v_r_2695_;
}
}
LEAN_EXPORT uint8_t l_Vector_all(lean_object* v_00_u03b1_2696_, lean_object* v_n_2697_, lean_object* v_xs_2698_, lean_object* v_p_2699_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2700_ = lean_unsigned_to_nat(0u);
v___x_2701_ = lean_array_get_size(v_xs_2698_);
v___x_2702_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2703_ = lean_nat_dec_lt(v___x_2700_, v___x_2701_);
if (v___x_2703_ == 0)
{
uint8_t v___x_2704_; 
lean_dec_ref(v_p_2699_);
lean_dec_ref(v_xs_2698_);
v___x_2704_ = 1;
return v___x_2704_;
}
else
{
if (v___x_2703_ == 0)
{
lean_dec_ref(v_p_2699_);
lean_dec_ref(v_xs_2698_);
return v___x_2703_;
}
else
{
lean_object* v___x_2705_; lean_object* v___f_2706_; size_t v___x_2707_; size_t v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___x_2705_ = lean_box(v___x_2703_);
v___f_2706_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2706_, 0, v_p_2699_);
lean_closure_set(v___f_2706_, 1, v___x_2705_);
v___x_2707_ = ((size_t)0ULL);
v___x_2708_ = lean_usize_of_nat(v___x_2701_);
v___x_2709_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2702_, v___f_2706_, v_xs_2698_, v___x_2707_, v___x_2708_);
v___x_2710_ = lean_unbox(v___x_2709_);
lean_dec(v___x_2709_);
if (v___x_2710_ == 0)
{
return v___x_2703_;
}
else
{
uint8_t v___x_2711_; 
v___x_2711_ = 0;
return v___x_2711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___boxed(lean_object* v_00_u03b1_2712_, lean_object* v_n_2713_, lean_object* v_xs_2714_, lean_object* v_p_2715_){
_start:
{
uint8_t v_res_2716_; lean_object* v_r_2717_; 
v_res_2716_ = l_Vector_all(v_00_u03b1_2712_, v_n_2713_, v_xs_2714_, v_p_2715_);
lean_dec(v_n_2713_);
v_r_2717_ = lean_box(v_res_2716_);
return v_r_2717_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0(lean_object* v_p_2718_, lean_object* v_x1_2719_, lean_object* v_x2_2720_){
_start:
{
lean_object* v___x_2721_; uint8_t v___x_2722_; 
v___x_2721_ = lean_apply_1(v_p_2718_, v_x1_2719_);
v___x_2722_ = lean_unbox(v___x_2721_);
if (v___x_2722_ == 0)
{
lean_inc(v_x2_2720_);
return v_x2_2720_;
}
else
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = lean_unsigned_to_nat(1u);
v___x_2724_ = lean_nat_add(v_x2_2720_, v___x_2723_);
return v___x_2724_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0___boxed(lean_object* v_p_2725_, lean_object* v_x1_2726_, lean_object* v_x2_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Vector_countP___redArg___lam__0(v_p_2725_, v_x1_2726_, v_x2_2727_);
lean_dec(v_x2_2727_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg(lean_object* v_p_2729_, lean_object* v_xs_2730_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = lean_array_get_size(v_xs_2730_);
v___x_2733_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2734_ = lean_nat_dec_lt(v___x_2731_, v___x_2732_);
if (v___x_2734_ == 0)
{
lean_dec_ref(v_xs_2730_);
lean_dec_ref(v_p_2729_);
return v___x_2731_;
}
else
{
lean_object* v___f_2735_; size_t v___x_2736_; size_t v___x_2737_; lean_object* v___x_2738_; 
v___f_2735_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2735_, 0, v_p_2729_);
v___x_2736_ = lean_usize_of_nat(v___x_2732_);
v___x_2737_ = ((size_t)0ULL);
v___x_2738_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2733_, v___f_2735_, v_xs_2730_, v___x_2736_, v___x_2737_, v___x_2731_);
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP(lean_object* v_00_u03b1_2739_, lean_object* v_n_2740_, lean_object* v_p_2741_, lean_object* v_xs_2742_){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; 
v___x_2743_ = lean_unsigned_to_nat(0u);
v___x_2744_ = lean_array_get_size(v_xs_2742_);
v___x_2745_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2746_ = lean_nat_dec_lt(v___x_2743_, v___x_2744_);
if (v___x_2746_ == 0)
{
lean_dec_ref(v_xs_2742_);
lean_dec_ref(v_p_2741_);
return v___x_2743_;
}
else
{
lean_object* v___f_2747_; size_t v___x_2748_; size_t v___x_2749_; lean_object* v___x_2750_; 
v___f_2747_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2747_, 0, v_p_2741_);
v___x_2748_ = lean_usize_of_nat(v___x_2744_);
v___x_2749_ = ((size_t)0ULL);
v___x_2750_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2745_, v___f_2747_, v_xs_2742_, v___x_2748_, v___x_2749_, v___x_2743_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___boxed(lean_object* v_00_u03b1_2751_, lean_object* v_n_2752_, lean_object* v_p_2753_, lean_object* v_xs_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Vector_countP(v_00_u03b1_2751_, v_n_2752_, v_p_2753_, v_xs_2754_);
lean_dec(v_n_2752_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0(lean_object* v_inst_2756_, lean_object* v_a_2757_, lean_object* v_x1_2758_, lean_object* v_x2_2759_){
_start:
{
lean_object* v___x_2760_; uint8_t v___x_2761_; 
v___x_2760_ = lean_apply_2(v_inst_2756_, v_x1_2758_, v_a_2757_);
v___x_2761_ = lean_unbox(v___x_2760_);
if (v___x_2761_ == 0)
{
lean_inc(v_x2_2759_);
return v_x2_2759_;
}
else
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = lean_unsigned_to_nat(1u);
v___x_2763_ = lean_nat_add(v_x2_2759_, v___x_2762_);
return v___x_2763_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0___boxed(lean_object* v_inst_2764_, lean_object* v_a_2765_, lean_object* v_x1_2766_, lean_object* v_x2_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Vector_count___redArg___lam__0(v_inst_2764_, v_a_2765_, v_x1_2766_, v_x2_2767_);
lean_dec(v_x2_2767_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg(lean_object* v_inst_2769_, lean_object* v_a_2770_, lean_object* v_xs_2771_){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v___x_2772_ = lean_unsigned_to_nat(0u);
v___x_2773_ = lean_array_get_size(v_xs_2771_);
v___x_2774_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2775_ = lean_nat_dec_lt(v___x_2772_, v___x_2773_);
if (v___x_2775_ == 0)
{
lean_dec_ref(v_xs_2771_);
lean_dec(v_a_2770_);
lean_dec_ref(v_inst_2769_);
return v___x_2772_;
}
else
{
lean_object* v___f_2776_; size_t v___x_2777_; size_t v___x_2778_; lean_object* v___x_2779_; 
v___f_2776_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2776_, 0, v_inst_2769_);
lean_closure_set(v___f_2776_, 1, v_a_2770_);
v___x_2777_ = lean_usize_of_nat(v___x_2773_);
v___x_2778_ = ((size_t)0ULL);
v___x_2779_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2774_, v___f_2776_, v_xs_2771_, v___x_2777_, v___x_2778_, v___x_2772_);
return v___x_2779_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count(lean_object* v_00_u03b1_2780_, lean_object* v_n_2781_, lean_object* v_inst_2782_, lean_object* v_a_2783_, lean_object* v_xs_2784_){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2785_ = lean_unsigned_to_nat(0u);
v___x_2786_ = lean_array_get_size(v_xs_2784_);
v___x_2787_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2788_ = lean_nat_dec_lt(v___x_2785_, v___x_2786_);
if (v___x_2788_ == 0)
{
lean_dec_ref(v_xs_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_inst_2782_);
return v___x_2785_;
}
else
{
lean_object* v___f_2789_; size_t v___x_2790_; size_t v___x_2791_; lean_object* v___x_2792_; 
v___f_2789_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2789_, 0, v_inst_2782_);
lean_closure_set(v___f_2789_, 1, v_a_2783_);
v___x_2790_ = lean_usize_of_nat(v___x_2786_);
v___x_2791_ = ((size_t)0ULL);
v___x_2792_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2787_, v___f_2789_, v_xs_2784_, v___x_2790_, v___x_2791_, v___x_2785_);
return v___x_2792_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___boxed(lean_object* v_00_u03b1_2793_, lean_object* v_n_2794_, lean_object* v_inst_2795_, lean_object* v_a_2796_, lean_object* v_xs_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Vector_count(v_00_u03b1_2793_, v_n_2794_, v_inst_2795_, v_a_2796_, v_xs_2797_);
lean_dec(v_n_2794_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___redArg(lean_object* v_inst_2799_, lean_object* v_xs_2800_, lean_object* v_a_2801_, lean_object* v_b_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Array_replace___redArg(v_inst_2799_, v_xs_2800_, v_a_2801_, v_b_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace(lean_object* v_00_u03b1_2804_, lean_object* v_n_2805_, lean_object* v_inst_2806_, lean_object* v_xs_2807_, lean_object* v_a_2808_, lean_object* v_b_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Array_replace___redArg(v_inst_2806_, v_xs_2807_, v_a_2808_, v_b_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___boxed(lean_object* v_00_u03b1_2811_, lean_object* v_n_2812_, lean_object* v_inst_2813_, lean_object* v_xs_2814_, lean_object* v_a_2815_, lean_object* v_b_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Vector_replace(v_00_u03b1_2811_, v_n_2812_, v_inst_2813_, v_xs_2814_, v_a_2815_, v_b_2816_);
lean_dec(v_n_2812_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg___lam__0(lean_object* v_inst_2818_, lean_object* v_x1_2819_, lean_object* v_x2_2820_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = lean_apply_2(v_inst_2818_, v_x1_2819_, v_x2_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg(lean_object* v_inst_2822_, lean_object* v_inst_2823_, lean_object* v_xs_2824_){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2825_ = lean_array_get_size(v_xs_2824_);
v___x_2826_ = lean_unsigned_to_nat(0u);
v___x_2827_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2828_ = lean_nat_dec_lt(v___x_2826_, v___x_2825_);
if (v___x_2828_ == 0)
{
lean_dec_ref(v_xs_2824_);
lean_dec(v_inst_2822_);
return v_inst_2823_;
}
else
{
lean_object* v___f_2829_; size_t v___x_2830_; size_t v___x_2831_; lean_object* v___x_2832_; 
v___f_2829_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2829_, 0, v_inst_2822_);
v___x_2830_ = lean_usize_of_nat(v___x_2825_);
v___x_2831_ = ((size_t)0ULL);
v___x_2832_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2827_, v___f_2829_, v_xs_2824_, v___x_2830_, v___x_2831_, v_inst_2823_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum(lean_object* v_00_u03b1_2833_, lean_object* v_n_2834_, lean_object* v_inst_2835_, lean_object* v_inst_2836_, lean_object* v_xs_2837_){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; uint8_t v___x_2841_; 
v___x_2838_ = lean_array_get_size(v_xs_2837_);
v___x_2839_ = lean_unsigned_to_nat(0u);
v___x_2840_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2841_ = lean_nat_dec_lt(v___x_2839_, v___x_2838_);
if (v___x_2841_ == 0)
{
lean_dec_ref(v_xs_2837_);
lean_dec(v_inst_2835_);
return v_inst_2836_;
}
else
{
lean_object* v___f_2842_; size_t v___x_2843_; size_t v___x_2844_; lean_object* v___x_2845_; 
v___f_2842_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2842_, 0, v_inst_2835_);
v___x_2843_ = lean_usize_of_nat(v___x_2838_);
v___x_2844_ = ((size_t)0ULL);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2840_, v___f_2842_, v_xs_2837_, v___x_2843_, v___x_2844_, v_inst_2836_);
return v___x_2845_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum___boxed(lean_object* v_00_u03b1_2846_, lean_object* v_n_2847_, lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_xs_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Vector_sum(v_00_u03b1_2846_, v_n_2847_, v_inst_2848_, v_inst_2849_, v_xs_2850_);
lean_dec(v_n_2847_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Vector_prod___redArg(lean_object* v_inst_2852_, lean_object* v_inst_2853_, lean_object* v_xs_2854_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2855_ = lean_array_get_size(v_xs_2854_);
v___x_2856_ = lean_unsigned_to_nat(0u);
v___x_2857_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2858_ = lean_nat_dec_lt(v___x_2856_, v___x_2855_);
if (v___x_2858_ == 0)
{
lean_dec_ref(v_xs_2854_);
lean_dec(v_inst_2852_);
return v_inst_2853_;
}
else
{
lean_object* v___f_2859_; size_t v___x_2860_; size_t v___x_2861_; lean_object* v___x_2862_; 
v___f_2859_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2859_, 0, v_inst_2852_);
v___x_2860_ = lean_usize_of_nat(v___x_2855_);
v___x_2861_ = ((size_t)0ULL);
v___x_2862_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2857_, v___f_2859_, v_xs_2854_, v___x_2860_, v___x_2861_, v_inst_2853_);
return v___x_2862_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod(lean_object* v_00_u03b1_2863_, lean_object* v_n_2864_, lean_object* v_inst_2865_, lean_object* v_inst_2866_, lean_object* v_xs_2867_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2868_ = lean_array_get_size(v_xs_2867_);
v___x_2869_ = lean_unsigned_to_nat(0u);
v___x_2870_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2871_ = lean_nat_dec_lt(v___x_2869_, v___x_2868_);
if (v___x_2871_ == 0)
{
lean_dec_ref(v_xs_2867_);
lean_dec(v_inst_2865_);
return v_inst_2866_;
}
else
{
lean_object* v___f_2872_; size_t v___x_2873_; size_t v___x_2874_; lean_object* v___x_2875_; 
v___f_2872_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2872_, 0, v_inst_2865_);
v___x_2873_ = lean_usize_of_nat(v___x_2868_);
v___x_2874_ = ((size_t)0ULL);
v___x_2875_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2870_, v___f_2872_, v_xs_2867_, v___x_2873_, v___x_2874_, v_inst_2866_);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod___boxed(lean_object* v_00_u03b1_2876_, lean_object* v_n_2877_, lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_xs_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Vector_prod(v_00_u03b1_2876_, v_n_2877_, v_inst_2878_, v_inst_2879_, v_xs_2880_);
lean_dec(v_n_2877_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg(lean_object* v_m_2882_, lean_object* v_n_2883_, lean_object* v_a_2884_, lean_object* v_xs_2885_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2886_ = lean_nat_sub(v_n_2883_, v_m_2882_);
v___x_2887_ = lean_mk_array(v___x_2886_, v_a_2884_);
v___x_2888_ = l_Array_append___redArg(v___x_2887_, v_xs_2885_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg___boxed(lean_object* v_m_2889_, lean_object* v_n_2890_, lean_object* v_a_2891_, lean_object* v_xs_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Vector_leftpad___redArg(v_m_2889_, v_n_2890_, v_a_2891_, v_xs_2892_);
lean_dec_ref(v_xs_2892_);
lean_dec(v_n_2890_);
lean_dec(v_m_2889_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad(lean_object* v_00_u03b1_2894_, lean_object* v_m_2895_, lean_object* v_n_2896_, lean_object* v_a_2897_, lean_object* v_xs_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = lean_nat_sub(v_n_2896_, v_m_2895_);
v___x_2900_ = lean_mk_array(v___x_2899_, v_a_2897_);
v___x_2901_ = l_Array_append___redArg(v___x_2900_, v_xs_2898_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___boxed(lean_object* v_00_u03b1_2902_, lean_object* v_m_2903_, lean_object* v_n_2904_, lean_object* v_a_2905_, lean_object* v_xs_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Vector_leftpad(v_00_u03b1_2902_, v_m_2903_, v_n_2904_, v_a_2905_, v_xs_2906_);
lean_dec_ref(v_xs_2906_);
lean_dec(v_n_2904_);
lean_dec(v_m_2903_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg(lean_object* v_m_2908_, lean_object* v_n_2909_, lean_object* v_a_2910_, lean_object* v_xs_2911_){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = lean_nat_sub(v_n_2909_, v_m_2908_);
v___x_2913_ = lean_mk_array(v___x_2912_, v_a_2910_);
v___x_2914_ = l_Array_append___redArg(v_xs_2911_, v___x_2913_);
lean_dec_ref(v___x_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg___boxed(lean_object* v_m_2915_, lean_object* v_n_2916_, lean_object* v_a_2917_, lean_object* v_xs_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Vector_rightpad___redArg(v_m_2915_, v_n_2916_, v_a_2917_, v_xs_2918_);
lean_dec(v_n_2916_);
lean_dec(v_m_2915_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad(lean_object* v_00_u03b1_2920_, lean_object* v_m_2921_, lean_object* v_n_2922_, lean_object* v_a_2923_, lean_object* v_xs_2924_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = lean_nat_sub(v_n_2922_, v_m_2921_);
v___x_2926_ = lean_mk_array(v___x_2925_, v_a_2923_);
v___x_2927_ = l_Array_append___redArg(v_xs_2924_, v___x_2926_);
lean_dec_ref(v___x_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___boxed(lean_object* v_00_u03b1_2928_, lean_object* v_m_2929_, lean_object* v_n_2930_, lean_object* v_a_2931_, lean_object* v_xs_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Vector_rightpad(v_00_u03b1_2928_, v_m_2929_, v_n_2930_, v_a_2931_, v_xs_2932_);
lean_dec(v_n_2930_);
lean_dec(v_m_2929_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_f_2934_, lean_object* v_a_2935_, lean_object* v_h_2936_, lean_object* v_b_2937_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = lean_apply_3(v_f_2934_, v_a_2935_, lean_box(0), v_b_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_inst_2939_, lean_object* v_00_u03b2_2940_, lean_object* v_xs_2941_, lean_object* v_b_2942_, lean_object* v_f_2943_){
_start:
{
lean_object* v___f_2944_; size_t v_sz_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v___f_2944_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2944_, 0, v_f_2943_);
v_sz_2945_ = lean_array_size(v_xs_2941_);
v___x_2946_ = ((size_t)0ULL);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2939_, v_xs_2941_, v___f_2944_, v_sz_2945_, v___x_2946_, v_b_2942_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_2948_){
_start:
{
lean_object* v___f_2949_; 
v___f_2949_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2949_, 0, v_inst_2948_);
return v___f_2949_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_2950_, lean_object* v_00_u03b1_2951_, lean_object* v_n_2952_, lean_object* v_inst_2953_){
_start:
{
lean_object* v___f_2954_; 
v___f_2954_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2954_, 0, v_inst_2953_);
return v___f_2954_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(lean_object* v_m_2955_, lean_object* v_00_u03b1_2956_, lean_object* v_n_2957_, lean_object* v_inst_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Vector_instForIn_x27InferInstanceMembershipOfMonad(v_m_2955_, v_00_u03b1_2956_, v_n_2957_, v_inst_2958_);
lean_dec(v_n_2957_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad___redArg(lean_object* v_n_2960_, lean_object* v_inst_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2962_, 0, lean_box(0));
lean_closure_set(v___x_2962_, 1, lean_box(0));
lean_closure_set(v___x_2962_, 2, v_n_2960_);
lean_closure_set(v___x_2962_, 3, v_inst_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad(lean_object* v_m_2963_, lean_object* v_00_u03b1_2964_, lean_object* v_n_2965_, lean_object* v_inst_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2967_, 0, lean_box(0));
lean_closure_set(v___x_2967_, 1, lean_box(0));
lean_closure_set(v___x_2967_, 2, v_n_2965_);
lean_closure_set(v___x_2967_, 3, v_inst_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___redArg(){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_box(0);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___redArg___boxed(lean_object* v___dummy_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Vector_instLT___redArg();
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object* v_00_u03b1_2972_, lean_object* v_n_2973_, lean_object* v_inst_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_box(0);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object* v_00_u03b1_2976_, lean_object* v_n_2977_, lean_object* v_inst_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Vector_instLT(v_00_u03b1_2976_, v_n_2977_, v_inst_2978_);
lean_dec(v_n_2977_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___redArg(){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_box(0);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___redArg___boxed(lean_object* v___dummy_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Vector_instLE___redArg();
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE(lean_object* v_00_u03b1_2984_, lean_object* v_n_2985_, lean_object* v_inst_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_box(0);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___boxed(lean_object* v_00_u03b1_2988_, lean_object* v_n_2989_, lean_object* v_inst_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Vector_instLE(v_00_u03b1_2988_, v_n_2989_, v_inst_2990_);
lean_dec(v_n_2989_);
return v_res_2991_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__2(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = ((lean_object*)(l_Vector_lex___auto__1___closed__0));
v___x_2999_ = l_Lean_mkAtom(v___x_2998_);
return v___x_2999_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3000_ = lean_obj_once(&l_Vector_lex___auto__1___closed__2, &l_Vector_lex___auto__1___closed__2_once, _init_l_Vector_lex___auto__1___closed__2);
v___x_3001_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3002_ = lean_array_push(v___x_3001_, v___x_3000_);
return v___x_3002_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_3016_ = l_Lean_mkAtom(v___x_3015_);
return v___x_3016_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = lean_obj_once(&l_Vector_lex___auto__1___closed__8, &l_Vector_lex___auto__1___closed__8_once, _init_l_Vector_lex___auto__1___closed__8);
v___x_3018_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3019_ = lean_array_push(v___x_3018_, v___x_3017_);
return v___x_3019_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_3025_ = lean_string_utf8_byte_size(v___x_3024_);
return v___x_3025_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3026_ = lean_obj_once(&l_Vector_lex___auto__1___closed__13, &l_Vector_lex___auto__1___closed__13_once, _init_l_Vector_lex___auto__1___closed__13);
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_3029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3027_);
lean_ctor_set(v___x_3029_, 2, v___x_3026_);
return v___x_3029_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3030_ = lean_box(0);
v___x_3031_ = lean_box(0);
v___x_3032_ = lean_obj_once(&l_Vector_lex___auto__1___closed__14, &l_Vector_lex___auto__1___closed__14_once, _init_l_Vector_lex___auto__1___closed__14);
v___x_3033_ = lean_box(2);
v___x_3034_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v___x_3032_);
lean_ctor_set(v___x_3034_, 2, v___x_3031_);
lean_ctor_set(v___x_3034_, 3, v___x_3030_);
return v___x_3034_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = lean_obj_once(&l_Vector_lex___auto__1___closed__15, &l_Vector_lex___auto__1___closed__15_once, _init_l_Vector_lex___auto__1___closed__15);
v___x_3036_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3037_ = lean_array_push(v___x_3036_, v___x_3035_);
return v___x_3037_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3038_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_3039_ = ((lean_object*)(l_Vector_lex___auto__1___closed__11));
v___x_3040_ = lean_box(2);
v___x_3041_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
lean_ctor_set(v___x_3041_, 1, v___x_3039_);
lean_ctor_set(v___x_3041_, 2, v___x_3038_);
return v___x_3041_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3043_ = lean_obj_once(&l_Vector_lex___auto__1___closed__9, &l_Vector_lex___auto__1___closed__9_once, _init_l_Vector_lex___auto__1___closed__9);
v___x_3044_ = lean_array_push(v___x_3043_, v___x_3042_);
return v___x_3044_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3045_ = lean_obj_once(&l_Vector_lex___auto__1___closed__18, &l_Vector_lex___auto__1___closed__18_once, _init_l_Vector_lex___auto__1___closed__18);
v___x_3046_ = ((lean_object*)(l_Vector_lex___auto__1___closed__7));
v___x_3047_ = lean_box(2);
v___x_3048_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
lean_ctor_set(v___x_3048_, 1, v___x_3046_);
lean_ctor_set(v___x_3048_, 2, v___x_3045_);
return v___x_3048_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = lean_obj_once(&l_Vector_lex___auto__1___closed__19, &l_Vector_lex___auto__1___closed__19_once, _init_l_Vector_lex___auto__1___closed__19);
v___x_3050_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3051_ = lean_array_push(v___x_3050_, v___x_3049_);
return v___x_3051_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = ((lean_object*)(l_Vector_lex___auto__1___closed__25));
v___x_3063_ = l_Lean_mkAtom(v___x_3062_);
return v___x_3063_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = lean_obj_once(&l_Vector_lex___auto__1___closed__26, &l_Vector_lex___auto__1___closed__26_once, _init_l_Vector_lex___auto__1___closed__26);
v___x_3065_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3066_ = lean_array_push(v___x_3065_, v___x_3064_);
return v___x_3066_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3067_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3068_ = lean_obj_once(&l_Vector_lex___auto__1___closed__27, &l_Vector_lex___auto__1___closed__27_once, _init_l_Vector_lex___auto__1___closed__27);
v___x_3069_ = lean_array_push(v___x_3068_, v___x_3067_);
return v___x_3069_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3070_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3071_ = ((lean_object*)(l_Vector_lex___auto__1___closed__24));
v___x_3072_ = lean_box(2);
v___x_3073_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3071_);
lean_ctor_set(v___x_3073_, 2, v___x_3070_);
return v___x_3073_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3075_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3076_ = lean_array_push(v___x_3075_, v___x_3074_);
return v___x_3076_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l_Vector_lex___auto__1___closed__31));
v___x_3079_ = l_Lean_mkAtom(v___x_3078_);
return v___x_3079_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__33(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_obj_once(&l_Vector_lex___auto__1___closed__32, &l_Vector_lex___auto__1___closed__32_once, _init_l_Vector_lex___auto__1___closed__32);
v___x_3081_ = lean_obj_once(&l_Vector_lex___auto__1___closed__30, &l_Vector_lex___auto__1___closed__30_once, _init_l_Vector_lex___auto__1___closed__30);
v___x_3082_ = lean_array_push(v___x_3081_, v___x_3080_);
return v___x_3082_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__34(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3084_ = lean_obj_once(&l_Vector_lex___auto__1___closed__33, &l_Vector_lex___auto__1___closed__33_once, _init_l_Vector_lex___auto__1___closed__33);
v___x_3085_ = lean_array_push(v___x_3084_, v___x_3083_);
return v___x_3085_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__35(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3086_ = lean_obj_once(&l_Vector_lex___auto__1___closed__34, &l_Vector_lex___auto__1___closed__34_once, _init_l_Vector_lex___auto__1___closed__34);
v___x_3087_ = ((lean_object*)(l_Vector_lex___auto__1___closed__22));
v___x_3088_ = lean_box(2);
v___x_3089_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
lean_ctor_set(v___x_3089_, 1, v___x_3087_);
lean_ctor_set(v___x_3089_, 2, v___x_3086_);
return v___x_3089_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__36(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_obj_once(&l_Vector_lex___auto__1___closed__35, &l_Vector_lex___auto__1___closed__35_once, _init_l_Vector_lex___auto__1___closed__35);
v___x_3091_ = lean_obj_once(&l_Vector_lex___auto__1___closed__20, &l_Vector_lex___auto__1___closed__20_once, _init_l_Vector_lex___auto__1___closed__20);
v___x_3092_ = lean_array_push(v___x_3091_, v___x_3090_);
return v___x_3092_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_3094_ = l_Lean_mkAtom(v___x_3093_);
return v___x_3094_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = lean_obj_once(&l_Vector_lex___auto__1___closed__37, &l_Vector_lex___auto__1___closed__37_once, _init_l_Vector_lex___auto__1___closed__37);
v___x_3096_ = lean_obj_once(&l_Vector_lex___auto__1___closed__36, &l_Vector_lex___auto__1___closed__36_once, _init_l_Vector_lex___auto__1___closed__36);
v___x_3097_ = lean_array_push(v___x_3096_, v___x_3095_);
return v___x_3097_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3098_ = lean_obj_once(&l_Vector_lex___auto__1___closed__38, &l_Vector_lex___auto__1___closed__38_once, _init_l_Vector_lex___auto__1___closed__38);
v___x_3099_ = ((lean_object*)(l_Vector_lex___auto__1___closed__5));
v___x_3100_ = lean_box(2);
v___x_3101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
lean_ctor_set(v___x_3101_, 1, v___x_3099_);
lean_ctor_set(v___x_3101_, 2, v___x_3098_);
return v___x_3101_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_obj_once(&l_Vector_lex___auto__1___closed__39, &l_Vector_lex___auto__1___closed__39_once, _init_l_Vector_lex___auto__1___closed__39);
v___x_3103_ = lean_obj_once(&l_Vector_lex___auto__1___closed__3, &l_Vector_lex___auto__1___closed__3_once, _init_l_Vector_lex___auto__1___closed__3);
v___x_3104_ = lean_array_push(v___x_3103_, v___x_3102_);
return v___x_3104_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3105_ = lean_obj_once(&l_Vector_lex___auto__1___closed__40, &l_Vector_lex___auto__1___closed__40_once, _init_l_Vector_lex___auto__1___closed__40);
v___x_3106_ = ((lean_object*)(l_Vector_lex___auto__1___closed__1));
v___x_3107_ = lean_box(2);
v___x_3108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
lean_ctor_set(v___x_3108_, 1, v___x_3106_);
lean_ctor_set(v___x_3108_, 2, v___x_3105_);
return v___x_3108_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = lean_obj_once(&l_Vector_lex___auto__1___closed__41, &l_Vector_lex___auto__1___closed__41_once, _init_l_Vector_lex___auto__1___closed__41);
v___x_3110_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3111_ = lean_array_push(v___x_3110_, v___x_3109_);
return v___x_3111_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3112_ = lean_obj_once(&l_Vector_lex___auto__1___closed__42, &l_Vector_lex___auto__1___closed__42_once, _init_l_Vector_lex___auto__1___closed__42);
v___x_3113_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_3114_ = lean_box(2);
v___x_3115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
lean_ctor_set(v___x_3115_, 1, v___x_3113_);
lean_ctor_set(v___x_3115_, 2, v___x_3112_);
return v___x_3115_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3116_ = lean_obj_once(&l_Vector_lex___auto__1___closed__43, &l_Vector_lex___auto__1___closed__43_once, _init_l_Vector_lex___auto__1___closed__43);
v___x_3117_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3118_ = lean_array_push(v___x_3117_, v___x_3116_);
return v___x_3118_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3119_ = lean_obj_once(&l_Vector_lex___auto__1___closed__44, &l_Vector_lex___auto__1___closed__44_once, _init_l_Vector_lex___auto__1___closed__44);
v___x_3120_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_3121_ = lean_box(2);
v___x_3122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
lean_ctor_set(v___x_3122_, 1, v___x_3120_);
lean_ctor_set(v___x_3122_, 2, v___x_3119_);
return v___x_3122_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = lean_obj_once(&l_Vector_lex___auto__1___closed__45, &l_Vector_lex___auto__1___closed__45_once, _init_l_Vector_lex___auto__1___closed__45);
v___x_3124_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3125_ = lean_array_push(v___x_3124_, v___x_3123_);
return v___x_3125_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3126_ = lean_obj_once(&l_Vector_lex___auto__1___closed__46, &l_Vector_lex___auto__1___closed__46_once, _init_l_Vector_lex___auto__1___closed__46);
v___x_3127_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_3128_ = lean_box(2);
v___x_3129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
lean_ctor_set(v___x_3129_, 1, v___x_3127_);
lean_ctor_set(v___x_3129_, 2, v___x_3126_);
return v___x_3129_;
}
}
static lean_object* _init_l_Vector_lex___auto__1(void){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = lean_obj_once(&l_Vector_lex___auto__1___closed__47, &l_Vector_lex___auto__1___closed__47_once, _init_l_Vector_lex___auto__1___closed__47);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0(lean_object* v_n_3131_, lean_object* v_xs_3132_, lean_object* v_ys_3133_, lean_object* v_lt_3134_, lean_object* v_inst_3135_, lean_object* v___x_3136_, lean_object* v___x_3137_, lean_object* v_next_3138_, lean_object* v_acc_3139_, lean_object* v_h_3140_, lean_object* v_G_3141_){
_start:
{
uint8_t v___x_3142_; 
v___x_3142_ = lean_nat_dec_lt(v_next_3138_, v_n_3131_);
if (v___x_3142_ == 0)
{
lean_dec_ref(v_G_3141_);
lean_dec_ref(v___x_3137_);
lean_dec_ref(v_inst_3135_);
lean_dec_ref(v_lt_3134_);
lean_inc_ref(v_acc_3139_);
return v_acc_3139_;
}
else
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3143_ = lean_array_fget_borrowed(v_xs_3132_, v_next_3138_);
v___x_3144_ = lean_array_fget_borrowed(v_ys_3133_, v_next_3138_);
lean_inc(v___x_3144_);
lean_inc(v___x_3143_);
v___x_3145_ = lean_apply_2(v_lt_3134_, v___x_3143_, v___x_3144_);
v___x_3146_ = lean_unbox(v___x_3145_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; uint8_t v___x_3148_; 
lean_inc(v___x_3144_);
lean_inc(v___x_3143_);
v___x_3147_ = lean_apply_2(v_inst_3135_, v___x_3143_, v___x_3144_);
v___x_3148_ = lean_unbox(v___x_3147_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec_ref(v_G_3141_);
lean_dec_ref(v___x_3137_);
v___x_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3145_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
lean_ctor_set(v___x_3150_, 1, v___x_3136_);
return v___x_3150_;
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3151_ = lean_unsigned_to_nat(1u);
v___x_3152_ = lean_nat_add(v_next_3138_, v___x_3151_);
v___x_3153_ = lean_apply_4(v_G_3141_, v___x_3152_, v___x_3137_, lean_box(0), lean_box(0));
return v___x_3153_;
}
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
lean_dec_ref(v_G_3141_);
lean_dec_ref(v___x_3137_);
lean_dec_ref(v_inst_3135_);
v___x_3154_ = lean_box(v___x_3142_);
v___x_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
lean_ctor_set(v___x_3156_, 1, v___x_3136_);
return v___x_3156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0___boxed(lean_object* v_n_3157_, lean_object* v_xs_3158_, lean_object* v_ys_3159_, lean_object* v_lt_3160_, lean_object* v_inst_3161_, lean_object* v___x_3162_, lean_object* v___x_3163_, lean_object* v_next_3164_, lean_object* v_acc_3165_, lean_object* v_h_3166_, lean_object* v_G_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_Vector_lex___redArg___lam__0(v_n_3157_, v_xs_3158_, v_ys_3159_, v_lt_3160_, v_inst_3161_, v___x_3162_, v___x_3163_, v_next_3164_, v_acc_3165_, v_h_3166_, v_G_3167_);
lean_dec_ref(v_acc_3165_);
lean_dec(v_next_3164_);
lean_dec_ref(v_ys_3159_);
lean_dec_ref(v_xs_3158_);
lean_dec(v_n_3157_);
return v_res_3168_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object* v_n_3172_, lean_object* v_inst_3173_, lean_object* v_xs_3174_, lean_object* v_ys_3175_, lean_object* v_lt_3176_){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___f_3180_; lean_object* v___x_3181_; lean_object* v_fst_3182_; 
v___x_3177_ = lean_unsigned_to_nat(0u);
v___x_3178_ = lean_box(0);
v___x_3179_ = ((lean_object*)(l_Vector_lex___redArg___closed__0));
v___f_3180_ = lean_alloc_closure((void*)(l_Vector_lex___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_3180_, 0, v_n_3172_);
lean_closure_set(v___f_3180_, 1, v_xs_3174_);
lean_closure_set(v___f_3180_, 2, v_ys_3175_);
lean_closure_set(v___f_3180_, 3, v_lt_3176_);
lean_closure_set(v___f_3180_, 4, v_inst_3173_);
lean_closure_set(v___f_3180_, 5, v___x_3178_);
lean_closure_set(v___f_3180_, 6, v___x_3179_);
v___x_3181_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3180_, v___x_3177_, v___x_3179_, lean_box(0));
v_fst_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_fst_3182_);
lean_dec(v___x_3181_);
if (lean_obj_tag(v_fst_3182_) == 0)
{
uint8_t v___x_3183_; 
v___x_3183_ = 0;
return v___x_3183_;
}
else
{
lean_object* v_val_3184_; uint8_t v___x_3185_; 
v_val_3184_ = lean_ctor_get(v_fst_3182_, 0);
lean_inc(v_val_3184_);
lean_dec_ref_known(v_fst_3182_, 1);
v___x_3185_ = lean_unbox(v_val_3184_);
lean_dec(v_val_3184_);
return v___x_3185_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object* v_n_3186_, lean_object* v_inst_3187_, lean_object* v_xs_3188_, lean_object* v_ys_3189_, lean_object* v_lt_3190_){
_start:
{
uint8_t v_res_3191_; lean_object* v_r_3192_; 
v_res_3191_ = l_Vector_lex___redArg(v_n_3186_, v_inst_3187_, v_xs_3188_, v_ys_3189_, v_lt_3190_);
v_r_3192_ = lean_box(v_res_3191_);
return v_r_3192_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex(lean_object* v_00_u03b1_3193_, lean_object* v_n_3194_, lean_object* v_inst_3195_, lean_object* v_xs_3196_, lean_object* v_ys_3197_, lean_object* v_lt_3198_){
_start:
{
uint8_t v___x_3199_; 
v___x_3199_ = l_Vector_lex___redArg(v_n_3194_, v_inst_3195_, v_xs_3196_, v_ys_3197_, v_lt_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object* v_00_u03b1_3200_, lean_object* v_n_3201_, lean_object* v_inst_3202_, lean_object* v_xs_3203_, lean_object* v_ys_3204_, lean_object* v_lt_3205_){
_start:
{
uint8_t v_res_3206_; lean_object* v_r_3207_; 
v_res_3206_ = l_Vector_lex(v_00_u03b1_3200_, v_n_3201_, v_inst_3202_, v_xs_3203_, v_ys_3204_, v_lt_3205_);
v_r_3207_ = lean_box(v_res_3206_);
return v_r_3207_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_InsertIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Vector_set___auto__1 = _init_l_Vector_set___auto__1();
lean_mark_persistent(l_Vector_set___auto__1);
l_Vector_swap___auto__1 = _init_l_Vector_swap___auto__1();
lean_mark_persistent(l_Vector_swap___auto__1);
l_Vector_swap___auto__3 = _init_l_Vector_swap___auto__3();
lean_mark_persistent(l_Vector_swap___auto__3);
l_Vector_swapAt___auto__1 = _init_l_Vector_swapAt___auto__1();
lean_mark_persistent(l_Vector_swapAt___auto__1);
l_Vector_eraseIdx___auto__1 = _init_l_Vector_eraseIdx___auto__1();
lean_mark_persistent(l_Vector_eraseIdx___auto__1);
l_Vector_insertIdx___auto__1 = _init_l_Vector_insertIdx___auto__1();
lean_mark_persistent(l_Vector_insertIdx___auto__1);
l_Vector_lex___auto__1 = _init_l_Vector_lex___auto__1();
lean_mark_persistent(l_Vector_lex___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* initialize_Init_Data_Array_InsertIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
