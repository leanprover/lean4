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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Vector_instGetElemNatLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Vector_instGetElemNatLt___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_instGetElemNatLt___closed__0 = (const lean_object*)&l_Vector_instGetElemNatLt___closed__0_value;
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object*, lean_object*, lean_object*);
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
v___x_159_ = l_Array_mkArray0(lean_box(0));
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
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___lam__0(lean_object* v_xs_444_, lean_object* v_i_445_, lean_object* v_h_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_array_fget_borrowed(v_xs_444_, v_i_445_);
lean_inc(v___x_447_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___lam__0___boxed(lean_object* v_xs_448_, lean_object* v_i_449_, lean_object* v_h_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Vector_instGetElemNatLt___lam__0(v_xs_448_, v_i_449_, v_h_450_);
lean_dec(v_i_449_);
lean_dec_ref(v_xs_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt(lean_object* v_00_u03b1_453_, lean_object* v_n_454_){
_start:
{
lean_object* v___f_455_; 
v___f_455_ = ((lean_object*)(l_Vector_instGetElemNatLt___closed__0));
return v___f_455_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___boxed(lean_object* v_00_u03b1_456_, lean_object* v_n_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Vector_instGetElemNatLt(v_00_u03b1_456_, v_n_457_);
lean_dec(v_n_457_);
return v_res_458_;
}
}
LEAN_EXPORT uint8_t l_Vector_contains___redArg(lean_object* v_inst_459_, lean_object* v_xs_460_, lean_object* v_a_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_Array_contains___redArg(v_inst_459_, v_xs_460_, v_a_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Vector_contains___redArg___boxed(lean_object* v_inst_463_, lean_object* v_xs_464_, lean_object* v_a_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Vector_contains___redArg(v_inst_463_, v_xs_464_, v_a_465_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT uint8_t l_Vector_contains(lean_object* v_00_u03b1_468_, lean_object* v_n_469_, lean_object* v_inst_470_, lean_object* v_xs_471_, lean_object* v_a_472_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = l_Array_contains___redArg(v_inst_470_, v_xs_471_, v_a_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Vector_contains___boxed(lean_object* v_00_u03b1_474_, lean_object* v_n_475_, lean_object* v_inst_476_, lean_object* v_xs_477_, lean_object* v_a_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_Vector_contains(v_00_u03b1_474_, v_n_475_, v_inst_476_, v_xs_477_, v_a_478_);
lean_dec(v_n_475_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership(lean_object* v_00_u03b1_481_, lean_object* v_n_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lean_box(0);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership___boxed(lean_object* v_00_u03b1_484_, lean_object* v_n_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Vector_instMembership(v_00_u03b1_484_, v_n_485_);
lean_dec(v_n_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg(lean_object* v_xs_487_, lean_object* v_i_488_, lean_object* v_default_489_){
_start:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_array_get_size(v_xs_487_);
v___x_491_ = lean_nat_dec_lt(v_i_488_, v___x_490_);
if (v___x_491_ == 0)
{
lean_inc(v_default_489_);
return v_default_489_;
}
else
{
lean_object* v___x_492_; 
v___x_492_ = lean_array_fget_borrowed(v_xs_487_, v_i_488_);
lean_inc(v___x_492_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg___boxed(lean_object* v_xs_493_, lean_object* v_i_494_, lean_object* v_default_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Vector_getD___redArg(v_xs_493_, v_i_494_, v_default_495_);
lean_dec(v_default_495_);
lean_dec(v_i_494_);
lean_dec_ref(v_xs_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD(lean_object* v_00_u03b1_497_, lean_object* v_n_498_, lean_object* v_xs_499_, lean_object* v_i_500_, lean_object* v_default_501_){
_start:
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_array_get_size(v_xs_499_);
v___x_503_ = lean_nat_dec_lt(v_i_500_, v___x_502_);
if (v___x_503_ == 0)
{
lean_inc(v_default_501_);
return v_default_501_;
}
else
{
lean_object* v___x_504_; 
v___x_504_ = lean_array_fget_borrowed(v_xs_499_, v_i_500_);
lean_inc(v___x_504_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___boxed(lean_object* v_00_u03b1_505_, lean_object* v_n_506_, lean_object* v_xs_507_, lean_object* v_i_508_, lean_object* v_default_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Vector_getD(v_00_u03b1_505_, v_n_506_, v_xs_507_, v_i_508_, v_default_509_);
lean_dec(v_default_509_);
lean_dec(v_i_508_);
lean_dec_ref(v_xs_507_);
lean_dec(v_n_506_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg(lean_object* v_inst_511_, lean_object* v_xs_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_array_get_size(v_xs_512_);
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_sub(v___x_513_, v___x_514_);
v___x_516_ = lean_array_get_borrowed(v_inst_511_, v_xs_512_, v___x_515_);
lean_dec(v___x_515_);
lean_inc(v___x_516_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg___boxed(lean_object* v_inst_517_, lean_object* v_xs_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Vector_back_x21___redArg(v_inst_517_, v_xs_518_);
lean_dec_ref(v_xs_518_);
lean_dec(v_inst_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21(lean_object* v_00_u03b1_520_, lean_object* v_n_521_, lean_object* v_inst_522_, lean_object* v_xs_523_){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = lean_array_get_size(v_xs_523_);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_sub(v___x_524_, v___x_525_);
v___x_527_ = lean_array_get_borrowed(v_inst_522_, v_xs_523_, v___x_526_);
lean_dec(v___x_526_);
lean_inc(v___x_527_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___boxed(lean_object* v_00_u03b1_528_, lean_object* v_n_529_, lean_object* v_inst_530_, lean_object* v_xs_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Vector_back_x21(v_00_u03b1_528_, v_n_529_, v_inst_530_, v_xs_531_);
lean_dec_ref(v_xs_531_);
lean_dec(v_inst_530_);
lean_dec(v_n_529_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg(lean_object* v_xs_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_534_ = lean_array_get_size(v_xs_533_);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_sub(v___x_534_, v___x_535_);
v___x_537_ = lean_nat_dec_lt(v___x_536_, v___x_534_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
lean_dec(v___x_536_);
v___x_538_ = lean_box(0);
return v___x_538_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_array_fget_borrowed(v_xs_533_, v___x_536_);
lean_dec(v___x_536_);
lean_inc(v___x_539_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg___boxed(lean_object* v_xs_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Vector_back_x3f___redArg(v_xs_541_);
lean_dec_ref(v_xs_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f(lean_object* v_00_u03b1_543_, lean_object* v_n_544_, lean_object* v_xs_545_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_546_ = lean_array_get_size(v_xs_545_);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_sub(v___x_546_, v___x_547_);
v___x_549_ = lean_nat_dec_lt(v___x_548_, v___x_546_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
lean_dec(v___x_548_);
v___x_550_ = lean_box(0);
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_array_fget_borrowed(v_xs_545_, v___x_548_);
lean_dec(v___x_548_);
lean_inc(v___x_551_);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___boxed(lean_object* v_00_u03b1_553_, lean_object* v_n_554_, lean_object* v_xs_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Vector_back_x3f(v_00_u03b1_553_, v_n_554_, v_xs_555_);
lean_dec_ref(v_xs_555_);
lean_dec(v_n_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg(lean_object* v_n_557_, lean_object* v_xs_558_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_sub(v_n_557_, v___x_559_);
v___x_561_ = lean_array_fget_borrowed(v_xs_558_, v___x_560_);
lean_dec(v___x_560_);
lean_inc(v___x_561_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg___boxed(lean_object* v_n_562_, lean_object* v_xs_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Vector_back___redArg(v_n_562_, v_xs_563_);
lean_dec_ref(v_xs_563_);
lean_dec(v_n_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Vector_back(lean_object* v_n_565_, lean_object* v_00_u03b1_566_, lean_object* v_inst_567_, lean_object* v_xs_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = lean_nat_sub(v_n_565_, v___x_569_);
v___x_571_ = lean_array_fget_borrowed(v_xs_568_, v___x_570_);
lean_dec(v___x_570_);
lean_inc(v___x_571_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___boxed(lean_object* v_n_572_, lean_object* v_00_u03b1_573_, lean_object* v_inst_574_, lean_object* v_xs_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Vector_back(v_n_572_, v_00_u03b1_573_, v_inst_574_, v_xs_575_);
lean_dec_ref(v_xs_575_);
lean_dec(v_n_572_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg(lean_object* v_xs_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_array_fget_borrowed(v_xs_577_, v___x_578_);
lean_inc(v___x_579_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg___boxed(lean_object* v_xs_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Vector_head___redArg(v_xs_580_);
lean_dec_ref(v_xs_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Vector_head(lean_object* v_n_582_, lean_object* v_00_u03b1_583_, lean_object* v_inst_584_, lean_object* v_xs_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_array_fget_borrowed(v_xs_585_, v___x_586_);
lean_inc(v___x_587_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___boxed(lean_object* v_n_588_, lean_object* v_00_u03b1_589_, lean_object* v_inst_590_, lean_object* v_xs_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Vector_head(v_n_588_, v_00_u03b1_589_, v_inst_590_, v_xs_591_);
lean_dec_ref(v_xs_591_);
lean_dec(v_n_588_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___redArg(lean_object* v_xs_593_, lean_object* v_x_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_array_push(v_xs_593_, v_x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Vector_push(lean_object* v_00_u03b1_596_, lean_object* v_n_597_, lean_object* v_xs_598_, lean_object* v_x_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_array_push(v_xs_598_, v_x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___boxed(lean_object* v_00_u03b1_601_, lean_object* v_n_602_, lean_object* v_xs_603_, lean_object* v_x_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Vector_push(v_00_u03b1_601_, v_n_602_, v_xs_603_, v_x_604_);
lean_dec(v_n_602_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___redArg(lean_object* v_xs_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = lean_array_pop(v_xs_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop(lean_object* v_00_u03b1_608_, lean_object* v_n_609_, lean_object* v_xs_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = lean_array_pop(v_xs_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___boxed(lean_object* v_00_u03b1_612_, lean_object* v_n_613_, lean_object* v_xs_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Vector_pop(v_00_u03b1_612_, v_n_613_, v_xs_614_);
lean_dec(v_n_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear___redArg(lean_object* v_xs_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_array_mark_linear(v_xs_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear(lean_object* v_00_u03b1_618_, lean_object* v_n_619_, lean_object* v_xs_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_array_mark_linear(v_xs_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear___boxed(lean_object* v_00_u03b1_622_, lean_object* v_n_623_, lean_object* v_xs_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Vector_markLinear(v_00_u03b1_622_, v_n_623_, v_xs_624_);
lean_dec(v_n_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg(lean_object* v_xs_626_, lean_object* v_ys_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_array_propagate_mark(v_xs_626_, v_ys_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg___boxed(lean_object* v_xs_629_, lean_object* v_ys_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Vector_propagateMark___redArg(v_xs_629_, v_ys_630_);
lean_dec_ref(v_xs_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark(lean_object* v_n_632_, lean_object* v_m_633_, lean_object* v_00_u03b1_634_, lean_object* v_00_u03b2_635_, lean_object* v_xs_636_, lean_object* v_ys_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = lean_array_propagate_mark(v_xs_636_, v_ys_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___boxed(lean_object* v_n_639_, lean_object* v_m_640_, lean_object* v_00_u03b1_641_, lean_object* v_00_u03b2_642_, lean_object* v_xs_643_, lean_object* v_ys_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Vector_propagateMark(v_n_639_, v_m_640_, v_00_u03b1_641_, v_00_u03b2_642_, v_xs_643_, v_ys_644_);
lean_dec_ref(v_xs_643_);
lean_dec(v_m_640_);
lean_dec(v_n_639_);
return v_res_645_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__9(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l_Vector_set___auto__1___closed__8));
v___x_666_ = l_Lean_mkAtom(v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__10(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_obj_once(&l_Vector_set___auto__1___closed__9, &l_Vector_set___auto__1___closed__9_once, _init_l_Vector_set___auto__1___closed__9);
v___x_668_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_669_ = lean_array_push(v___x_668_, v___x_667_);
return v___x_669_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__11(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_obj_once(&l_Vector_set___auto__1___closed__10, &l_Vector_set___auto__1___closed__10_once, _init_l_Vector_set___auto__1___closed__10);
v___x_671_ = ((lean_object*)(l_Vector_set___auto__1___closed__7));
v___x_672_ = lean_box(2);
v___x_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
lean_ctor_set(v___x_673_, 2, v___x_670_);
return v___x_673_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__12(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_obj_once(&l_Vector_set___auto__1___closed__11, &l_Vector_set___auto__1___closed__11_once, _init_l_Vector_set___auto__1___closed__11);
v___x_675_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_676_ = lean_array_push(v___x_675_, v___x_674_);
return v___x_676_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__13(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_677_ = lean_obj_once(&l_Vector_set___auto__1___closed__12, &l_Vector_set___auto__1___closed__12_once, _init_l_Vector_set___auto__1___closed__12);
v___x_678_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_679_ = lean_box(2);
v___x_680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_678_);
lean_ctor_set(v___x_680_, 2, v___x_677_);
return v___x_680_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__14(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = lean_obj_once(&l_Vector_set___auto__1___closed__13, &l_Vector_set___auto__1___closed__13_once, _init_l_Vector_set___auto__1___closed__13);
v___x_682_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_683_ = lean_array_push(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__15(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_684_ = lean_obj_once(&l_Vector_set___auto__1___closed__14, &l_Vector_set___auto__1___closed__14_once, _init_l_Vector_set___auto__1___closed__14);
v___x_685_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_686_ = lean_box(2);
v___x_687_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___x_685_);
lean_ctor_set(v___x_687_, 2, v___x_684_);
return v___x_687_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__16(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = lean_obj_once(&l_Vector_set___auto__1___closed__15, &l_Vector_set___auto__1___closed__15_once, _init_l_Vector_set___auto__1___closed__15);
v___x_689_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_690_ = lean_array_push(v___x_689_, v___x_688_);
return v___x_690_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__17(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_691_ = lean_obj_once(&l_Vector_set___auto__1___closed__16, &l_Vector_set___auto__1___closed__16_once, _init_l_Vector_set___auto__1___closed__16);
v___x_692_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_693_ = lean_box(2);
v___x_694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v___x_692_);
lean_ctor_set(v___x_694_, 2, v___x_691_);
return v___x_694_;
}
}
static lean_object* _init_l_Vector_set___auto__1(void){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg(lean_object* v_xs_696_, lean_object* v_i_697_, lean_object* v_x_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = lean_array_fset(v_xs_696_, v_i_697_, v_x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg___boxed(lean_object* v_xs_700_, lean_object* v_i_701_, lean_object* v_x_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Vector_set___redArg(v_xs_700_, v_i_701_, v_x_702_);
lean_dec(v_i_701_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Vector_set(lean_object* v_00_u03b1_704_, lean_object* v_n_705_, lean_object* v_xs_706_, lean_object* v_i_707_, lean_object* v_x_708_, lean_object* v_h_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_array_fset(v_xs_706_, v_i_707_, v_x_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___boxed(lean_object* v_00_u03b1_711_, lean_object* v_n_712_, lean_object* v_xs_713_, lean_object* v_i_714_, lean_object* v_x_715_, lean_object* v_h_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Vector_set(v_00_u03b1_711_, v_n_712_, v_xs_713_, v_i_714_, v_x_715_, v_h_716_);
lean_dec(v_i_714_);
lean_dec(v_n_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg(lean_object* v_xs_718_, lean_object* v_i_719_, lean_object* v_x_720_){
_start:
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_array_get_size(v_xs_718_);
v___x_722_ = lean_nat_dec_lt(v_i_719_, v___x_721_);
if (v___x_722_ == 0)
{
lean_dec(v_x_720_);
return v_xs_718_;
}
else
{
lean_object* v___x_723_; 
v___x_723_ = lean_array_fset(v_xs_718_, v_i_719_, v_x_720_);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg___boxed(lean_object* v_xs_724_, lean_object* v_i_725_, lean_object* v_x_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Vector_setIfInBounds___redArg(v_xs_724_, v_i_725_, v_x_726_);
lean_dec(v_i_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds(lean_object* v_00_u03b1_728_, lean_object* v_n_729_, lean_object* v_xs_730_, lean_object* v_i_731_, lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = lean_array_get_size(v_xs_730_);
v___x_734_ = lean_nat_dec_lt(v_i_731_, v___x_733_);
if (v___x_734_ == 0)
{
lean_dec(v_x_732_);
return v_xs_730_;
}
else
{
lean_object* v___x_735_; 
v___x_735_ = lean_array_fset(v_xs_730_, v_i_731_, v_x_732_);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___boxed(lean_object* v_00_u03b1_736_, lean_object* v_n_737_, lean_object* v_xs_738_, lean_object* v_i_739_, lean_object* v_x_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Vector_setIfInBounds(v_00_u03b1_736_, v_n_737_, v_xs_738_, v_i_739_, v_x_740_);
lean_dec(v_i_739_);
lean_dec(v_n_737_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg(lean_object* v_xs_742_, lean_object* v_i_743_, lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = lean_array_set(v_xs_742_, v_i_743_, v_x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg___boxed(lean_object* v_xs_746_, lean_object* v_i_747_, lean_object* v_x_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Vector_set_x21___redArg(v_xs_746_, v_i_747_, v_x_748_);
lean_dec(v_i_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21(lean_object* v_00_u03b1_750_, lean_object* v_n_751_, lean_object* v_xs_752_, lean_object* v_i_753_, lean_object* v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = lean_array_set(v_xs_752_, v_i_753_, v_x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___boxed(lean_object* v_00_u03b1_756_, lean_object* v_n_757_, lean_object* v_xs_758_, lean_object* v_i_759_, lean_object* v_x_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Vector_set_x21(v_00_u03b1_756_, v_n_757_, v_xs_758_, v_i_759_, v_x_760_);
lean_dec(v_i_759_);
lean_dec(v_n_757_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___redArg(lean_object* v_inst_762_, lean_object* v_f_763_, lean_object* v_b_764_, lean_object* v_xs_765_){
_start:
{
lean_object* v_toApplicative_766_; lean_object* v_toPure_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v_toApplicative_766_ = lean_ctor_get(v_inst_762_, 0);
v_toPure_767_ = lean_ctor_get(v_toApplicative_766_, 1);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_array_get_size(v_xs_765_);
v___x_770_ = lean_nat_dec_lt(v___x_768_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
lean_inc(v_toPure_767_);
lean_dec_ref(v_xs_765_);
lean_dec(v_f_763_);
lean_dec_ref(v_inst_762_);
v___x_771_ = lean_apply_2(v_toPure_767_, lean_box(0), v_b_764_);
return v___x_771_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = lean_nat_dec_le(v___x_769_, v___x_769_);
if (v___x_772_ == 0)
{
if (v___x_770_ == 0)
{
lean_object* v___x_773_; 
lean_inc(v_toPure_767_);
lean_dec_ref(v_xs_765_);
lean_dec(v_f_763_);
lean_dec_ref(v_inst_762_);
v___x_773_ = lean_apply_2(v_toPure_767_, lean_box(0), v_b_764_);
return v___x_773_;
}
else
{
size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((size_t)0ULL);
v___x_775_ = lean_usize_of_nat(v___x_769_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_762_, v_f_763_, v_xs_765_, v___x_774_, v___x_775_, v_b_764_);
return v___x_776_;
}
}
else
{
size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; 
v___x_777_ = ((size_t)0ULL);
v___x_778_ = lean_usize_of_nat(v___x_769_);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_762_, v_f_763_, v_xs_765_, v___x_777_, v___x_778_, v_b_764_);
return v___x_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM(lean_object* v_m_780_, lean_object* v_00_u03b2_781_, lean_object* v_00_u03b1_782_, lean_object* v_n_783_, lean_object* v_inst_784_, lean_object* v_f_785_, lean_object* v_b_786_, lean_object* v_xs_787_){
_start:
{
lean_object* v_toApplicative_788_; lean_object* v_toPure_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_toApplicative_788_ = lean_ctor_get(v_inst_784_, 0);
v_toPure_789_ = lean_ctor_get(v_toApplicative_788_, 1);
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_array_get_size(v_xs_787_);
v___x_792_ = lean_nat_dec_lt(v___x_790_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
lean_inc(v_toPure_789_);
lean_dec_ref(v_xs_787_);
lean_dec(v_f_785_);
lean_dec_ref(v_inst_784_);
v___x_793_ = lean_apply_2(v_toPure_789_, lean_box(0), v_b_786_);
return v___x_793_;
}
else
{
uint8_t v___x_794_; 
v___x_794_ = lean_nat_dec_le(v___x_791_, v___x_791_);
if (v___x_794_ == 0)
{
if (v___x_792_ == 0)
{
lean_object* v___x_795_; 
lean_inc(v_toPure_789_);
lean_dec_ref(v_xs_787_);
lean_dec(v_f_785_);
lean_dec_ref(v_inst_784_);
v___x_795_ = lean_apply_2(v_toPure_789_, lean_box(0), v_b_786_);
return v___x_795_;
}
else
{
size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((size_t)0ULL);
v___x_797_ = lean_usize_of_nat(v___x_791_);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_784_, v_f_785_, v_xs_787_, v___x_796_, v___x_797_, v_b_786_);
return v___x_798_;
}
}
else
{
size_t v___x_799_; size_t v___x_800_; lean_object* v___x_801_; 
v___x_799_ = ((size_t)0ULL);
v___x_800_ = lean_usize_of_nat(v___x_791_);
v___x_801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_784_, v_f_785_, v_xs_787_, v___x_799_, v___x_800_, v_b_786_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___boxed(lean_object* v_m_802_, lean_object* v_00_u03b2_803_, lean_object* v_00_u03b1_804_, lean_object* v_n_805_, lean_object* v_inst_806_, lean_object* v_f_807_, lean_object* v_b_808_, lean_object* v_xs_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Vector_foldlM(v_m_802_, v_00_u03b2_803_, v_00_u03b1_804_, v_n_805_, v_inst_806_, v_f_807_, v_b_808_, v_xs_809_);
lean_dec(v_n_805_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___redArg(lean_object* v_inst_811_, lean_object* v_f_812_, lean_object* v_b_813_, lean_object* v_xs_814_){
_start:
{
lean_object* v_toApplicative_815_; lean_object* v_toPure_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_toApplicative_815_ = lean_ctor_get(v_inst_811_, 0);
v_toPure_816_ = lean_ctor_get(v_toApplicative_815_, 1);
v___x_817_ = lean_array_get_size(v_xs_814_);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = lean_nat_dec_lt(v___x_818_, v___x_817_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
lean_inc(v_toPure_816_);
lean_dec_ref(v_xs_814_);
lean_dec(v_f_812_);
lean_dec_ref(v_inst_811_);
v___x_820_ = lean_apply_2(v_toPure_816_, lean_box(0), v_b_813_);
return v___x_820_;
}
else
{
size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_usize_of_nat(v___x_817_);
v___x_822_ = ((size_t)0ULL);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_811_, v_f_812_, v_xs_814_, v___x_821_, v___x_822_, v_b_813_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM(lean_object* v_m_824_, lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_n_827_, lean_object* v_inst_828_, lean_object* v_f_829_, lean_object* v_b_830_, lean_object* v_xs_831_){
_start:
{
lean_object* v_toApplicative_832_; lean_object* v_toPure_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v_toApplicative_832_ = lean_ctor_get(v_inst_828_, 0);
v_toPure_833_ = lean_ctor_get(v_toApplicative_832_, 1);
v___x_834_ = lean_array_get_size(v_xs_831_);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_nat_dec_lt(v___x_835_, v___x_834_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; 
lean_inc(v_toPure_833_);
lean_dec_ref(v_xs_831_);
lean_dec(v_f_829_);
lean_dec_ref(v_inst_828_);
v___x_837_ = lean_apply_2(v_toPure_833_, lean_box(0), v_b_830_);
return v___x_837_;
}
else
{
size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; 
v___x_838_ = lean_usize_of_nat(v___x_834_);
v___x_839_ = ((size_t)0ULL);
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_828_, v_f_829_, v_xs_831_, v___x_838_, v___x_839_, v_b_830_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___boxed(lean_object* v_m_841_, lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_n_844_, lean_object* v_inst_845_, lean_object* v_f_846_, lean_object* v_b_847_, lean_object* v_xs_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Vector_foldrM(v_m_841_, v_00_u03b1_842_, v_00_u03b2_843_, v_n_844_, v_inst_845_, v_f_846_, v_b_847_, v_xs_848_);
lean_dec(v_n_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg___lam__0(lean_object* v_f_850_, lean_object* v_x1_851_, lean_object* v_x2_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_apply_2(v_f_850_, v_x1_851_, v_x2_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg(lean_object* v_f_873_, lean_object* v_b_874_, lean_object* v_xs_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = lean_array_get_size(v_xs_875_);
v___x_878_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_879_ = lean_nat_dec_lt(v___x_876_, v___x_877_);
if (v___x_879_ == 0)
{
lean_dec_ref(v_xs_875_);
lean_dec(v_f_873_);
return v_b_874_;
}
else
{
lean_object* v___f_880_; uint8_t v___x_881_; 
v___f_880_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_880_, 0, v_f_873_);
v___x_881_ = lean_nat_dec_le(v___x_877_, v___x_877_);
if (v___x_881_ == 0)
{
if (v___x_879_ == 0)
{
lean_dec_ref(v___f_880_);
lean_dec_ref(v_xs_875_);
return v_b_874_;
}
else
{
size_t v___x_882_; size_t v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((size_t)0ULL);
v___x_883_ = lean_usize_of_nat(v___x_877_);
v___x_884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_878_, v___f_880_, v_xs_875_, v___x_882_, v___x_883_, v_b_874_);
return v___x_884_;
}
}
else
{
size_t v___x_885_; size_t v___x_886_; lean_object* v___x_887_; 
v___x_885_ = ((size_t)0ULL);
v___x_886_ = lean_usize_of_nat(v___x_877_);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_878_, v___f_880_, v_xs_875_, v___x_885_, v___x_886_, v_b_874_);
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl(lean_object* v_00_u03b2_888_, lean_object* v_00_u03b1_889_, lean_object* v_n_890_, lean_object* v_f_891_, lean_object* v_b_892_, lean_object* v_xs_893_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_array_get_size(v_xs_893_);
v___x_896_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_897_ = lean_nat_dec_lt(v___x_894_, v___x_895_);
if (v___x_897_ == 0)
{
lean_dec_ref(v_xs_893_);
lean_dec(v_f_891_);
return v_b_892_;
}
else
{
lean_object* v___f_898_; uint8_t v___x_899_; 
v___f_898_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_898_, 0, v_f_891_);
v___x_899_ = lean_nat_dec_le(v___x_895_, v___x_895_);
if (v___x_899_ == 0)
{
if (v___x_897_ == 0)
{
lean_dec_ref(v___f_898_);
lean_dec_ref(v_xs_893_);
return v_b_892_;
}
else
{
size_t v___x_900_; size_t v___x_901_; lean_object* v___x_902_; 
v___x_900_ = ((size_t)0ULL);
v___x_901_ = lean_usize_of_nat(v___x_895_);
v___x_902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_896_, v___f_898_, v_xs_893_, v___x_900_, v___x_901_, v_b_892_);
return v___x_902_;
}
}
else
{
size_t v___x_903_; size_t v___x_904_; lean_object* v___x_905_; 
v___x_903_ = ((size_t)0ULL);
v___x_904_ = lean_usize_of_nat(v___x_895_);
v___x_905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_896_, v___f_898_, v_xs_893_, v___x_903_, v___x_904_, v_b_892_);
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___boxed(lean_object* v_00_u03b2_906_, lean_object* v_00_u03b1_907_, lean_object* v_n_908_, lean_object* v_f_909_, lean_object* v_b_910_, lean_object* v_xs_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Vector_foldl(v_00_u03b2_906_, v_00_u03b1_907_, v_n_908_, v_f_909_, v_b_910_, v_xs_911_);
lean_dec(v_n_908_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___redArg(lean_object* v_f_913_, lean_object* v_b_914_, lean_object* v_xs_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_916_ = lean_array_get_size(v_xs_915_);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_919_ = lean_nat_dec_lt(v___x_917_, v___x_916_);
if (v___x_919_ == 0)
{
lean_dec_ref(v_xs_915_);
lean_dec(v_f_913_);
return v_b_914_;
}
else
{
lean_object* v___f_920_; size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; 
v___f_920_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_920_, 0, v_f_913_);
v___x_921_ = lean_usize_of_nat(v___x_916_);
v___x_922_ = ((size_t)0ULL);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_918_, v___f_920_, v_xs_915_, v___x_921_, v___x_922_, v_b_914_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_n_926_, lean_object* v_f_927_, lean_object* v_b_928_, lean_object* v_xs_929_){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_930_ = lean_array_get_size(v_xs_929_);
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_933_ = lean_nat_dec_lt(v___x_931_, v___x_930_);
if (v___x_933_ == 0)
{
lean_dec_ref(v_xs_929_);
lean_dec(v_f_927_);
return v_b_928_;
}
else
{
lean_object* v___f_934_; size_t v___x_935_; size_t v___x_936_; lean_object* v___x_937_; 
v___f_934_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_934_, 0, v_f_927_);
v___x_935_ = lean_usize_of_nat(v___x_930_);
v___x_936_ = ((size_t)0ULL);
v___x_937_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_932_, v___f_934_, v_xs_929_, v___x_935_, v___x_936_, v_b_928_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___boxed(lean_object* v_00_u03b1_938_, lean_object* v_00_u03b2_939_, lean_object* v_n_940_, lean_object* v_f_941_, lean_object* v_b_942_, lean_object* v_xs_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Vector_foldr(v_00_u03b1_938_, v_00_u03b2_939_, v_n_940_, v_f_941_, v_b_942_, v_xs_943_);
lean_dec(v_n_940_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg(lean_object* v_xs_945_, lean_object* v_ys_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Array_append___redArg(v_xs_945_, v_ys_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg___boxed(lean_object* v_xs_948_, lean_object* v_ys_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Vector_append___redArg(v_xs_948_, v_ys_949_);
lean_dec_ref(v_ys_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Vector_append(lean_object* v_00_u03b1_951_, lean_object* v_n_952_, lean_object* v_m_953_, lean_object* v_xs_954_, lean_object* v_ys_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Array_append___redArg(v_xs_954_, v_ys_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___boxed(lean_object* v_00_u03b1_957_, lean_object* v_n_958_, lean_object* v_m_959_, lean_object* v_xs_960_, lean_object* v_ys_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Vector_append(v_00_u03b1_957_, v_n_958_, v_m_959_, v_xs_960_, v_ys_961_);
lean_dec_ref(v_ys_961_);
lean_dec(v_m_959_);
lean_dec(v_n_958_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat___redArg(lean_object* v_n_963_, lean_object* v_m_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_965_, 0, lean_box(0));
lean_closure_set(v___x_965_, 1, v_n_963_);
lean_closure_set(v___x_965_, 2, v_m_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat(lean_object* v_00_u03b1_966_, lean_object* v_n_967_, lean_object* v_m_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_969_, 0, lean_box(0));
lean_closure_set(v___x_969_, 1, v_n_967_);
lean_closure_set(v___x_969_, 2, v_m_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg(lean_object* v_xs_970_){
_start:
{
lean_inc_ref(v_xs_970_);
return v_xs_970_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg___boxed(lean_object* v_xs_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Vector_cast___redArg(v_xs_971_);
lean_dec_ref(v_xs_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast(lean_object* v_n_973_, lean_object* v_m_974_, lean_object* v_00_u03b1_975_, lean_object* v_h_976_, lean_object* v_xs_977_){
_start:
{
lean_inc_ref(v_xs_977_);
return v_xs_977_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___boxed(lean_object* v_n_978_, lean_object* v_m_979_, lean_object* v_00_u03b1_980_, lean_object* v_h_981_, lean_object* v_xs_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Vector_cast(v_n_978_, v_m_979_, v_00_u03b1_980_, v_h_981_, v_xs_982_);
lean_dec_ref(v_xs_982_);
lean_dec(v_m_979_);
lean_dec(v_n_978_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg(lean_object* v_xs_984_, lean_object* v_start_985_, lean_object* v_stop_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Array_extract___redArg(v_xs_984_, v_start_985_, v_stop_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg___boxed(lean_object* v_xs_988_, lean_object* v_start_989_, lean_object* v_stop_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Vector_extract___redArg(v_xs_988_, v_start_989_, v_stop_990_);
lean_dec_ref(v_xs_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract(lean_object* v_00_u03b1_992_, lean_object* v_n_993_, lean_object* v_xs_994_, lean_object* v_start_995_, lean_object* v_stop_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Array_extract___redArg(v_xs_994_, v_start_995_, v_stop_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___boxed(lean_object* v_00_u03b1_998_, lean_object* v_n_999_, lean_object* v_xs_1000_, lean_object* v_start_1001_, lean_object* v_stop_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Vector_extract(v_00_u03b1_998_, v_n_999_, v_xs_1000_, v_start_1001_, v_stop_1002_);
lean_dec_ref(v_xs_1000_);
lean_dec(v_n_999_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg(lean_object* v_n_1004_, lean_object* v_xs_1005_, lean_object* v_i_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = l_Array_extract___redArg(v_xs_1005_, v___x_1007_, v_i_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg___boxed(lean_object* v_n_1009_, lean_object* v_xs_1010_, lean_object* v_i_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Vector_take___redArg(v_n_1009_, v_xs_1010_, v_i_1011_);
lean_dec_ref(v_xs_1010_);
lean_dec(v_n_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Vector_take(lean_object* v_00_u03b1_1013_, lean_object* v_n_1014_, lean_object* v_xs_1015_, lean_object* v_i_1016_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = l_Array_extract___redArg(v_xs_1015_, v___x_1017_, v_i_1016_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___boxed(lean_object* v_00_u03b1_1019_, lean_object* v_n_1020_, lean_object* v_xs_1021_, lean_object* v_i_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Vector_take(v_00_u03b1_1019_, v_n_1020_, v_xs_1021_, v_i_1022_);
lean_dec_ref(v_xs_1021_);
lean_dec(v_n_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg(lean_object* v_xs_1024_, lean_object* v_i_1025_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_array_get_size(v_xs_1024_);
v___x_1027_ = l_Array_extract___redArg(v_xs_1024_, v_i_1025_, v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg___boxed(lean_object* v_xs_1028_, lean_object* v_i_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Vector_drop___redArg(v_xs_1028_, v_i_1029_);
lean_dec_ref(v_xs_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop(lean_object* v_00_u03b1_1031_, lean_object* v_n_1032_, lean_object* v_xs_1033_, lean_object* v_i_1034_){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_array_get_size(v_xs_1033_);
v___x_1036_ = l_Array_extract___redArg(v_xs_1033_, v_i_1034_, v___x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___boxed(lean_object* v_00_u03b1_1037_, lean_object* v_n_1038_, lean_object* v_xs_1039_, lean_object* v_i_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Vector_drop(v_00_u03b1_1037_, v_n_1038_, v_xs_1039_, v_i_1040_);
lean_dec_ref(v_xs_1039_);
lean_dec(v_n_1038_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg(lean_object* v_xs_1042_, lean_object* v_i_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Array_shrink___redArg(v_xs_1042_, v_i_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg___boxed(lean_object* v_xs_1045_, lean_object* v_i_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Vector_shrink___redArg(v_xs_1045_, v_i_1046_);
lean_dec(v_i_1046_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink(lean_object* v_00_u03b1_1048_, lean_object* v_n_1049_, lean_object* v_xs_1050_, lean_object* v_i_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Array_shrink___redArg(v_xs_1050_, v_i_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___boxed(lean_object* v_00_u03b1_1053_, lean_object* v_n_1054_, lean_object* v_xs_1055_, lean_object* v_i_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Vector_shrink(v_00_u03b1_1053_, v_n_1054_, v_xs_1055_, v_i_1056_);
lean_dec(v_i_1056_);
lean_dec(v_n_1054_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg___lam__0(lean_object* v_f_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_apply_1(v_f_1058_, v_x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg(lean_object* v_f_1061_, lean_object* v_xs_1062_){
_start:
{
lean_object* v___f_1063_; lean_object* v___x_1064_; size_t v_sz_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___f_1063_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1063_, 0, v_f_1061_);
v___x_1064_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1065_ = lean_array_size(v_xs_1062_);
v___x_1066_ = ((size_t)0ULL);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1064_, v___f_1063_, v_sz_1065_, v___x_1066_, v_xs_1062_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Vector_map(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_n_1070_, lean_object* v_f_1071_, lean_object* v_xs_1072_){
_start:
{
lean_object* v___f_1073_; lean_object* v___x_1074_; size_t v_sz_1075_; size_t v___x_1076_; lean_object* v___x_1077_; 
v___f_1073_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1073_, 0, v_f_1071_);
v___x_1074_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1075_ = lean_array_size(v_xs_1072_);
v___x_1076_ = ((size_t)0ULL);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1074_, v___f_1073_, v_sz_1075_, v___x_1076_, v_xs_1072_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___boxed(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_n_1080_, lean_object* v_f_1081_, lean_object* v_xs_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Vector_map(v_00_u03b1_1078_, v_00_u03b2_1079_, v_n_1080_, v_f_1081_, v_xs_1082_);
lean_dec(v_n_1080_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg___lam__0(lean_object* v_f_1084_, lean_object* v_i_1085_, lean_object* v_a_1086_, lean_object* v_x_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_apply_2(v_f_1084_, v_i_1085_, v_a_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg(lean_object* v_f_1089_, lean_object* v_xs_1090_){
_start:
{
lean_object* v___f_1091_; lean_object* v___x_1092_; size_t v_sz_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
v___f_1091_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1091_, 0, v_f_1089_);
v___x_1092_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1093_ = lean_array_size(v_xs_1090_);
v___x_1094_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1090_);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1092_, v_xs_1090_, v___f_1091_, v_sz_1093_, v___x_1094_, v_xs_1090_);
lean_dec_ref(v_xs_1090_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_n_1098_, lean_object* v_f_1099_, lean_object* v_xs_1100_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_1102_; size_t v_sz_1103_; size_t v___x_1104_; lean_object* v___x_1105_; 
v___f_1101_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1101_, 0, v_f_1099_);
v___x_1102_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1103_ = lean_array_size(v_xs_1100_);
v___x_1104_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1100_);
v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1102_, v_xs_1100_, v___f_1101_, v_sz_1103_, v___x_1104_, v_xs_1100_);
lean_dec_ref(v_xs_1100_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___boxed(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_n_1108_, lean_object* v_f_1109_, lean_object* v_xs_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Vector_mapIdx(v_00_u03b1_1106_, v_00_u03b2_1107_, v_n_1108_, v_f_1109_, v_xs_1110_);
lean_dec(v_n_1108_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg___lam__0(lean_object* v_f_1112_, lean_object* v_x1_1113_, lean_object* v_x2_1114_, lean_object* v_x3_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_apply_3(v_f_1112_, v_x1_1113_, v_x2_1114_, lean_box(0));
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg(lean_object* v_xs_1117_, lean_object* v_f_1118_){
_start:
{
lean_object* v___f_1119_; lean_object* v___x_1120_; size_t v_sz_1121_; size_t v___x_1122_; lean_object* v___x_1123_; 
v___f_1119_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1119_, 0, v_f_1118_);
v___x_1120_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1121_ = lean_array_size(v_xs_1117_);
v___x_1122_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1117_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1120_, v_xs_1117_, v___f_1119_, v_sz_1121_, v___x_1122_, v_xs_1117_);
lean_dec_ref(v_xs_1117_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx(lean_object* v_00_u03b1_1124_, lean_object* v_n_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_xs_1127_, lean_object* v_f_1128_){
_start:
{
lean_object* v___f_1129_; lean_object* v___x_1130_; size_t v_sz_1131_; size_t v___x_1132_; lean_object* v___x_1133_; 
v___f_1129_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1129_, 0, v_f_1128_);
v___x_1130_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1131_ = lean_array_size(v_xs_1127_);
v___x_1132_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1127_);
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1130_, v_xs_1127_, v___f_1129_, v_sz_1131_, v___x_1132_, v_xs_1127_);
lean_dec_ref(v_xs_1127_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_n_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_xs_1137_, lean_object* v_f_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Vector_mapFinIdx(v_00_u03b1_1134_, v_n_1135_, v_00_u03b2_1136_, v_xs_1137_, v_f_1138_);
lean_dec(v_n_1135_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(lean_object* v_k_1140_, lean_object* v_acc_1141_, lean_object* v_n_1142_, lean_object* v_inst_1143_, lean_object* v_f_1144_, lean_object* v_xs_1145_, lean_object* v_____do__lift_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(v_k_1140_, v_acc_1141_, v_n_1142_, v_inst_1143_, v_f_1144_, v_xs_1145_, v_____do__lift_1146_);
lean_dec(v_k_1140_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(lean_object* v_n_1148_, lean_object* v_inst_1149_, lean_object* v_f_1150_, lean_object* v_xs_1151_, lean_object* v_k_1152_, lean_object* v_acc_1153_){
_start:
{
lean_object* v_toApplicative_1154_; lean_object* v_toBind_1155_; lean_object* v_toPure_1156_; uint8_t v___x_1157_; 
v_toApplicative_1154_ = lean_ctor_get(v_inst_1149_, 0);
v_toBind_1155_ = lean_ctor_get(v_inst_1149_, 1);
lean_inc(v_toBind_1155_);
v_toPure_1156_ = lean_ctor_get(v_toApplicative_1154_, 1);
v___x_1157_ = lean_nat_dec_lt(v_k_1152_, v_n_1148_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
lean_inc(v_toPure_1156_);
lean_dec(v_toBind_1155_);
lean_dec(v_k_1152_);
lean_dec_ref(v_xs_1151_);
lean_dec(v_f_1150_);
lean_dec_ref(v_inst_1149_);
lean_dec(v_n_1148_);
v___x_1158_ = lean_apply_2(v_toPure_1156_, lean_box(0), v_acc_1153_);
return v___x_1158_;
}
else
{
lean_object* v___f_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_inc_ref(v_xs_1151_);
lean_inc(v_f_1150_);
lean_inc(v_k_1152_);
v___f_1159_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1159_, 0, v_k_1152_);
lean_closure_set(v___f_1159_, 1, v_acc_1153_);
lean_closure_set(v___f_1159_, 2, v_n_1148_);
lean_closure_set(v___f_1159_, 3, v_inst_1149_);
lean_closure_set(v___f_1159_, 4, v_f_1150_);
lean_closure_set(v___f_1159_, 5, v_xs_1151_);
v___x_1160_ = lean_array_fget(v_xs_1151_, v_k_1152_);
lean_dec(v_k_1152_);
lean_dec_ref(v_xs_1151_);
v___x_1161_ = lean_apply_1(v_f_1150_, v___x_1160_);
v___x_1162_ = lean_apply_4(v_toBind_1155_, lean_box(0), lean_box(0), v___x_1161_, v___f_1159_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(lean_object* v_k_1163_, lean_object* v_acc_1164_, lean_object* v_n_1165_, lean_object* v_inst_1166_, lean_object* v_f_1167_, lean_object* v_xs_1168_, lean_object* v_____do__lift_1169_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_nat_add(v_k_1163_, v___x_1170_);
v___x_1172_ = lean_array_push(v_acc_1164_, v_____do__lift_1169_);
v___x_1173_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1165_, v_inst_1166_, v_f_1167_, v_xs_1168_, v___x_1171_, v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(lean_object* v_m_1174_, lean_object* v_00_u03b1_1175_, lean_object* v_00_u03b2_1176_, lean_object* v_n_1177_, lean_object* v_inst_1178_, lean_object* v_f_1179_, lean_object* v_xs_1180_, lean_object* v_k_1181_, lean_object* v_h_1182_, lean_object* v_acc_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1177_, v_inst_1178_, v_f_1179_, v_xs_1180_, v_k_1181_, v_acc_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM___redArg(lean_object* v_n_1187_, lean_object* v_inst_1188_, lean_object* v_f_1189_, lean_object* v_xs_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1193_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1187_, v_inst_1188_, v_f_1189_, v_xs_1190_, v___x_1191_, v___x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM(lean_object* v_m_1194_, lean_object* v_00_u03b1_1195_, lean_object* v_00_u03b2_1196_, lean_object* v_n_1197_, lean_object* v_inst_1198_, lean_object* v_f_1199_, lean_object* v_xs_1200_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_unsigned_to_nat(0u);
v___x_1202_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1203_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1197_, v_inst_1198_, v_f_1199_, v_xs_1200_, v___x_1201_, v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg___lam__0(lean_object* v_f_1204_, lean_object* v_x_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_apply_1(v_f_1204_, v___y_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg(lean_object* v_inst_1208_, lean_object* v_xs_1209_, lean_object* v_f_1210_){
_start:
{
lean_object* v_toApplicative_1211_; lean_object* v_toPure_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v_toApplicative_1211_ = lean_ctor_get(v_inst_1208_, 0);
v_toPure_1212_ = lean_ctor_get(v_toApplicative_1211_, 1);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_array_get_size(v_xs_1209_);
v___x_1215_ = lean_box(0);
v___x_1216_ = lean_nat_dec_lt(v___x_1213_, v___x_1214_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
lean_inc(v_toPure_1212_);
lean_dec(v_f_1210_);
lean_dec_ref(v_xs_1209_);
lean_dec_ref(v_inst_1208_);
v___x_1217_ = lean_apply_2(v_toPure_1212_, lean_box(0), v___x_1215_);
return v___x_1217_;
}
else
{
lean_object* v___f_1218_; uint8_t v___x_1219_; 
v___f_1218_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1218_, 0, v_f_1210_);
v___x_1219_ = lean_nat_dec_le(v___x_1214_, v___x_1214_);
if (v___x_1219_ == 0)
{
if (v___x_1216_ == 0)
{
lean_object* v___x_1220_; 
lean_inc(v_toPure_1212_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v_xs_1209_);
lean_dec_ref(v_inst_1208_);
v___x_1220_ = lean_apply_2(v_toPure_1212_, lean_box(0), v___x_1215_);
return v___x_1220_;
}
else
{
size_t v___x_1221_; size_t v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = ((size_t)0ULL);
v___x_1222_ = lean_usize_of_nat(v___x_1214_);
v___x_1223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1208_, v___f_1218_, v_xs_1209_, v___x_1221_, v___x_1222_, v___x_1215_);
return v___x_1223_;
}
}
else
{
size_t v___x_1224_; size_t v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = ((size_t)0ULL);
v___x_1225_ = lean_usize_of_nat(v___x_1214_);
v___x_1226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1208_, v___f_1218_, v_xs_1209_, v___x_1224_, v___x_1225_, v___x_1215_);
return v___x_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM(lean_object* v_m_1227_, lean_object* v_00_u03b1_1228_, lean_object* v_n_1229_, lean_object* v_inst_1230_, lean_object* v_xs_1231_, lean_object* v_f_1232_){
_start:
{
lean_object* v_toApplicative_1233_; lean_object* v_toPure_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_toApplicative_1233_ = lean_ctor_get(v_inst_1230_, 0);
v_toPure_1234_ = lean_ctor_get(v_toApplicative_1233_, 1);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_array_get_size(v_xs_1231_);
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_nat_dec_lt(v___x_1235_, v___x_1236_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_inc(v_toPure_1234_);
lean_dec(v_f_1232_);
lean_dec_ref(v_xs_1231_);
lean_dec_ref(v_inst_1230_);
v___x_1239_ = lean_apply_2(v_toPure_1234_, lean_box(0), v___x_1237_);
return v___x_1239_;
}
else
{
lean_object* v___f_1240_; uint8_t v___x_1241_; 
v___f_1240_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1240_, 0, v_f_1232_);
v___x_1241_ = lean_nat_dec_le(v___x_1236_, v___x_1236_);
if (v___x_1241_ == 0)
{
if (v___x_1238_ == 0)
{
lean_object* v___x_1242_; 
lean_inc(v_toPure_1234_);
lean_dec_ref(v___f_1240_);
lean_dec_ref(v_xs_1231_);
lean_dec_ref(v_inst_1230_);
v___x_1242_ = lean_apply_2(v_toPure_1234_, lean_box(0), v___x_1237_);
return v___x_1242_;
}
else
{
size_t v___x_1243_; size_t v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = ((size_t)0ULL);
v___x_1244_ = lean_usize_of_nat(v___x_1236_);
v___x_1245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1230_, v___f_1240_, v_xs_1231_, v___x_1243_, v___x_1244_, v___x_1237_);
return v___x_1245_;
}
}
else
{
size_t v___x_1246_; size_t v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = ((size_t)0ULL);
v___x_1247_ = lean_usize_of_nat(v___x_1236_);
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1230_, v___f_1240_, v_xs_1231_, v___x_1246_, v___x_1247_, v___x_1237_);
return v___x_1248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM___boxed(lean_object* v_m_1249_, lean_object* v_00_u03b1_1250_, lean_object* v_n_1251_, lean_object* v_inst_1252_, lean_object* v_xs_1253_, lean_object* v_f_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Vector_forM(v_m_1249_, v_00_u03b1_1250_, v_n_1251_, v_inst_1252_, v_xs_1253_, v_f_1254_);
lean_dec(v_n_1251_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(lean_object* v_i_1256_, lean_object* v_acc_1257_, lean_object* v_n_1258_, lean_object* v_inst_1259_, lean_object* v_xs_1260_, lean_object* v_f_1261_, lean_object* v_____do__lift_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(v_i_1256_, v_acc_1257_, v_n_1258_, v_inst_1259_, v_xs_1260_, v_f_1261_, v_____do__lift_1262_);
lean_dec_ref(v_____do__lift_1262_);
lean_dec(v_i_1256_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(lean_object* v_n_1264_, lean_object* v_inst_1265_, lean_object* v_xs_1266_, lean_object* v_f_1267_, lean_object* v_i_1268_, lean_object* v_acc_1269_){
_start:
{
lean_object* v_toApplicative_1270_; lean_object* v_toBind_1271_; lean_object* v_toPure_1272_; uint8_t v___x_1273_; 
v_toApplicative_1270_ = lean_ctor_get(v_inst_1265_, 0);
v_toBind_1271_ = lean_ctor_get(v_inst_1265_, 1);
lean_inc(v_toBind_1271_);
v_toPure_1272_ = lean_ctor_get(v_toApplicative_1270_, 1);
v___x_1273_ = lean_nat_dec_lt(v_i_1268_, v_n_1264_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
lean_inc(v_toPure_1272_);
lean_dec(v_toBind_1271_);
lean_dec(v_i_1268_);
lean_dec(v_f_1267_);
lean_dec_ref(v_xs_1266_);
lean_dec_ref(v_inst_1265_);
lean_dec(v_n_1264_);
v___x_1274_ = lean_apply_2(v_toPure_1272_, lean_box(0), v_acc_1269_);
return v___x_1274_;
}
else
{
lean_object* v___f_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_inc(v_f_1267_);
lean_inc_ref(v_xs_1266_);
lean_inc(v_i_1268_);
v___f_1275_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1275_, 0, v_i_1268_);
lean_closure_set(v___f_1275_, 1, v_acc_1269_);
lean_closure_set(v___f_1275_, 2, v_n_1264_);
lean_closure_set(v___f_1275_, 3, v_inst_1265_);
lean_closure_set(v___f_1275_, 4, v_xs_1266_);
lean_closure_set(v___f_1275_, 5, v_f_1267_);
v___x_1276_ = lean_array_fget(v_xs_1266_, v_i_1268_);
lean_dec(v_i_1268_);
lean_dec_ref(v_xs_1266_);
v___x_1277_ = lean_apply_1(v_f_1267_, v___x_1276_);
v___x_1278_ = lean_apply_4(v_toBind_1271_, lean_box(0), lean_box(0), v___x_1277_, v___f_1275_);
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(lean_object* v_i_1279_, lean_object* v_acc_1280_, lean_object* v_n_1281_, lean_object* v_inst_1282_, lean_object* v_xs_1283_, lean_object* v_f_1284_, lean_object* v_____do__lift_1285_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = lean_unsigned_to_nat(1u);
v___x_1287_ = lean_nat_add(v_i_1279_, v___x_1286_);
v___x_1288_ = l_Array_append___redArg(v_acc_1280_, v_____do__lift_1285_);
v___x_1289_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1281_, v_inst_1282_, v_xs_1283_, v_f_1284_, v___x_1287_, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(lean_object* v_m_1290_, lean_object* v_00_u03b1_1291_, lean_object* v_n_1292_, lean_object* v_00_u03b2_1293_, lean_object* v_k_1294_, lean_object* v_inst_1295_, lean_object* v_xs_1296_, lean_object* v_f_1297_, lean_object* v_i_1298_, lean_object* v_h_1299_, lean_object* v_acc_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1292_, v_inst_1295_, v_xs_1296_, v_f_1297_, v_i_1298_, v_acc_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(lean_object* v_m_1302_, lean_object* v_00_u03b1_1303_, lean_object* v_n_1304_, lean_object* v_00_u03b2_1305_, lean_object* v_k_1306_, lean_object* v_inst_1307_, lean_object* v_xs_1308_, lean_object* v_f_1309_, lean_object* v_i_1310_, lean_object* v_h_1311_, lean_object* v_acc_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(v_m_1302_, v_00_u03b1_1303_, v_n_1304_, v_00_u03b2_1305_, v_k_1306_, v_inst_1307_, v_xs_1308_, v_f_1309_, v_i_1310_, v_h_1311_, v_acc_1312_);
lean_dec(v_k_1306_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___redArg(lean_object* v_n_1314_, lean_object* v_inst_1315_, lean_object* v_xs_1316_, lean_object* v_f_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1320_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1314_, v_inst_1315_, v_xs_1316_, v_f_1317_, v___x_1318_, v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM(lean_object* v_m_1321_, lean_object* v_00_u03b1_1322_, lean_object* v_n_1323_, lean_object* v_00_u03b2_1324_, lean_object* v_k_1325_, lean_object* v_inst_1326_, lean_object* v_xs_1327_, lean_object* v_f_1328_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1331_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1323_, v_inst_1326_, v_xs_1327_, v_f_1328_, v___x_1329_, v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___boxed(lean_object* v_m_1332_, lean_object* v_00_u03b1_1333_, lean_object* v_n_1334_, lean_object* v_00_u03b2_1335_, lean_object* v_k_1336_, lean_object* v_inst_1337_, lean_object* v_xs_1338_, lean_object* v_f_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Vector_flatMapM(v_m_1332_, v_00_u03b1_1333_, v_n_1334_, v_00_u03b2_1335_, v_k_1336_, v_inst_1337_, v_xs_1338_, v_f_1339_);
lean_dec(v_k_1336_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1341_, lean_object* v_ys_1342_, lean_object* v_inst_1343_, lean_object* v_xs_1344_, lean_object* v_f_1345_, lean_object* v_n_1346_, lean_object* v_____do__lift_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Vector_mapFinIdxM_map___redArg___lam__0(v_j_1341_, v_ys_1342_, v_inst_1343_, v_xs_1344_, v_f_1345_, v_n_1346_, v_____do__lift_1347_);
lean_dec(v_n_1346_);
lean_dec(v_j_1341_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg(lean_object* v_inst_1349_, lean_object* v_xs_1350_, lean_object* v_f_1351_, lean_object* v_i_1352_, lean_object* v_j_1353_, lean_object* v_ys_1354_){
_start:
{
lean_object* v_toApplicative_1355_; lean_object* v_toBind_1356_; lean_object* v_toPure_1357_; lean_object* v_zero_1358_; uint8_t v_isZero_1359_; 
v_toApplicative_1355_ = lean_ctor_get(v_inst_1349_, 0);
v_toBind_1356_ = lean_ctor_get(v_inst_1349_, 1);
lean_inc(v_toBind_1356_);
v_toPure_1357_ = lean_ctor_get(v_toApplicative_1355_, 1);
v_zero_1358_ = lean_unsigned_to_nat(0u);
v_isZero_1359_ = lean_nat_dec_eq(v_i_1352_, v_zero_1358_);
if (v_isZero_1359_ == 1)
{
lean_object* v___x_1360_; 
lean_inc(v_toPure_1357_);
lean_dec(v_toBind_1356_);
lean_dec(v_j_1353_);
lean_dec(v_f_1351_);
lean_dec_ref(v_xs_1350_);
lean_dec_ref(v_inst_1349_);
v___x_1360_ = lean_apply_2(v_toPure_1357_, lean_box(0), v_ys_1354_);
return v___x_1360_;
}
else
{
lean_object* v_one_1361_; lean_object* v_n_1362_; lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v_one_1361_ = lean_unsigned_to_nat(1u);
v_n_1362_ = lean_nat_sub(v_i_1352_, v_one_1361_);
lean_inc(v_f_1351_);
lean_inc_ref(v_xs_1350_);
lean_inc(v_j_1353_);
v___f_1363_ = lean_alloc_closure((void*)(l_Vector_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1363_, 0, v_j_1353_);
lean_closure_set(v___f_1363_, 1, v_ys_1354_);
lean_closure_set(v___f_1363_, 2, v_inst_1349_);
lean_closure_set(v___f_1363_, 3, v_xs_1350_);
lean_closure_set(v___f_1363_, 4, v_f_1351_);
lean_closure_set(v___f_1363_, 5, v_n_1362_);
v___x_1364_ = lean_array_fget(v_xs_1350_, v_j_1353_);
lean_dec_ref(v_xs_1350_);
v___x_1365_ = lean_apply_3(v_f_1351_, v_j_1353_, v___x_1364_, lean_box(0));
v___x_1366_ = lean_apply_4(v_toBind_1356_, lean_box(0), lean_box(0), v___x_1365_, v___f_1363_);
return v___x_1366_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1367_, lean_object* v_ys_1368_, lean_object* v_inst_1369_, lean_object* v_xs_1370_, lean_object* v_f_1371_, lean_object* v_n_1372_, lean_object* v_____do__lift_1373_){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = lean_nat_add(v_j_1367_, v___x_1374_);
v___x_1376_ = lean_array_push(v_ys_1368_, v_____do__lift_1373_);
v___x_1377_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1369_, v_xs_1370_, v_f_1371_, v_n_1372_, v___x_1375_, v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1378_, lean_object* v_xs_1379_, lean_object* v_f_1380_, lean_object* v_i_1381_, lean_object* v_j_1382_, lean_object* v_ys_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1378_, v_xs_1379_, v_f_1380_, v_i_1381_, v_j_1382_, v_ys_1383_);
lean_dec(v_i_1381_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map(lean_object* v_n_1385_, lean_object* v_00_u03b1_1386_, lean_object* v_00_u03b2_1387_, lean_object* v_m_1388_, lean_object* v_inst_1389_, lean_object* v_xs_1390_, lean_object* v_f_1391_, lean_object* v_i_1392_, lean_object* v_j_1393_, lean_object* v_inv_1394_, lean_object* v_ys_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1389_, v_xs_1390_, v_f_1391_, v_i_1392_, v_j_1393_, v_ys_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___boxed(lean_object* v_n_1397_, lean_object* v_00_u03b1_1398_, lean_object* v_00_u03b2_1399_, lean_object* v_m_1400_, lean_object* v_inst_1401_, lean_object* v_xs_1402_, lean_object* v_f_1403_, lean_object* v_i_1404_, lean_object* v_j_1405_, lean_object* v_inv_1406_, lean_object* v_ys_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Vector_mapFinIdxM_map(v_n_1397_, v_00_u03b1_1398_, v_00_u03b2_1399_, v_m_1400_, v_inst_1401_, v_xs_1402_, v_f_1403_, v_i_1404_, v_j_1405_, v_inv_1406_, v_ys_1407_);
lean_dec(v_i_1404_);
lean_dec(v_n_1397_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg(lean_object* v_n_1409_, lean_object* v_inst_1410_, lean_object* v_xs_1411_, lean_object* v_f_1412_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1415_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1410_, v_xs_1411_, v_f_1412_, v_n_1409_, v___x_1413_, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg___boxed(lean_object* v_n_1416_, lean_object* v_inst_1417_, lean_object* v_xs_1418_, lean_object* v_f_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Vector_mapFinIdxM___redArg(v_n_1416_, v_inst_1417_, v_xs_1418_, v_f_1419_);
lean_dec(v_n_1416_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM(lean_object* v_n_1421_, lean_object* v_00_u03b1_1422_, lean_object* v_00_u03b2_1423_, lean_object* v_m_1424_, lean_object* v_inst_1425_, lean_object* v_xs_1426_, lean_object* v_f_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1430_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1425_, v_xs_1426_, v_f_1427_, v_n_1421_, v___x_1428_, v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___boxed(lean_object* v_n_1431_, lean_object* v_00_u03b1_1432_, lean_object* v_00_u03b2_1433_, lean_object* v_m_1434_, lean_object* v_inst_1435_, lean_object* v_xs_1436_, lean_object* v_f_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Vector_mapFinIdxM(v_n_1431_, v_00_u03b1_1432_, v_00_u03b2_1433_, v_m_1434_, v_inst_1435_, v_xs_1436_, v_f_1437_);
lean_dec(v_n_1431_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg(lean_object* v_n_1439_, lean_object* v_inst_1440_, lean_object* v_f_1441_, lean_object* v_xs_1442_){
_start:
{
lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___f_1443_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1443_, 0, v_f_1441_);
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1446_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1440_, v_xs_1442_, v___f_1443_, v_n_1439_, v___x_1444_, v___x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg___boxed(lean_object* v_n_1447_, lean_object* v_inst_1448_, lean_object* v_f_1449_, lean_object* v_xs_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Vector_mapIdxM___redArg(v_n_1447_, v_inst_1448_, v_f_1449_, v_xs_1450_);
lean_dec(v_n_1447_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM(lean_object* v_n_1452_, lean_object* v_00_u03b1_1453_, lean_object* v_00_u03b2_1454_, lean_object* v_m_1455_, lean_object* v_inst_1456_, lean_object* v_f_1457_, lean_object* v_xs_1458_){
_start:
{
lean_object* v___f_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___f_1459_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1459_, 0, v_f_1457_);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1462_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1456_, v_xs_1458_, v___f_1459_, v_n_1452_, v___x_1460_, v___x_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___boxed(lean_object* v_n_1463_, lean_object* v_00_u03b1_1464_, lean_object* v_00_u03b2_1465_, lean_object* v_m_1466_, lean_object* v_inst_1467_, lean_object* v_f_1468_, lean_object* v_xs_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Vector_mapIdxM(v_n_1463_, v_00_u03b1_1464_, v_00_u03b2_1465_, v_m_1466_, v_inst_1467_, v_f_1468_, v_xs_1469_);
lean_dec(v_n_1463_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___redArg(lean_object* v_inst_1471_, lean_object* v_f_1472_, lean_object* v_xs_1473_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1471_, v_f_1472_, v_xs_1473_, v___x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM(lean_object* v_00_u03b2_1476_, lean_object* v_n_1477_, lean_object* v_00_u03b1_1478_, lean_object* v_m_1479_, lean_object* v_inst_1480_, lean_object* v_f_1481_, lean_object* v_xs_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1480_, v_f_1481_, v_xs_1482_, v___x_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___boxed(lean_object* v_00_u03b2_1485_, lean_object* v_n_1486_, lean_object* v_00_u03b1_1487_, lean_object* v_m_1488_, lean_object* v_inst_1489_, lean_object* v_f_1490_, lean_object* v_xs_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Vector_firstM(v_00_u03b2_1485_, v_n_1486_, v_00_u03b1_1487_, v_m_1488_, v_inst_1489_, v_f_1490_, v_xs_1491_);
lean_dec(v_n_1486_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0(lean_object* v_x_1493_){
_start:
{
lean_inc_ref(v_x_1493_);
return v_x_1493_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0___boxed(lean_object* v_x_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Vector_flatten___redArg___lam__0(v_x_1494_);
lean_dec_ref(v_x_1494_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg(lean_object* v_xs_1500_){
_start:
{
lean_object* v___f_1501_; lean_object* v___x_1502_; size_t v_sz_1503_; size_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___f_1501_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1502_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1503_ = lean_array_size(v_xs_1500_);
v___x_1504_ = ((size_t)0ULL);
v___x_1505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1502_, v___f_1501_, v_sz_1503_, v___x_1504_, v_xs_1500_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1508_ = lean_array_get_size(v___x_1505_);
v___x_1509_ = lean_nat_dec_lt(v___x_1506_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_dec(v___x_1505_);
return v___x_1507_;
}
else
{
lean_object* v___f_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v___f_1510_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1511_ = lean_usize_of_nat(v___x_1508_);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1502_, v___f_1510_, v___x_1505_, v___x_1504_, v___x_1511_, v___x_1507_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten(lean_object* v_00_u03b1_1513_, lean_object* v_n_1514_, lean_object* v_m_1515_, lean_object* v_xs_1516_){
_start:
{
lean_object* v___f_1517_; lean_object* v___x_1518_; size_t v_sz_1519_; size_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___f_1517_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1518_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1519_ = lean_array_size(v_xs_1516_);
v___x_1520_ = ((size_t)0ULL);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1518_, v___f_1517_, v_sz_1519_, v___x_1520_, v_xs_1516_);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1524_ = lean_array_get_size(v___x_1521_);
v___x_1525_ = lean_nat_dec_lt(v___x_1522_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_dec(v___x_1521_);
return v___x_1523_;
}
else
{
lean_object* v___f_1526_; size_t v___x_1527_; lean_object* v___x_1528_; 
v___f_1526_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1527_ = lean_usize_of_nat(v___x_1524_);
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1518_, v___f_1526_, v___x_1521_, v___x_1520_, v___x_1527_, v___x_1523_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___boxed(lean_object* v_00_u03b1_1529_, lean_object* v_n_1530_, lean_object* v_m_1531_, lean_object* v_xs_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Vector_flatten(v_00_u03b1_1529_, v_n_1530_, v_m_1531_, v_xs_1532_);
lean_dec(v_m_1531_);
lean_dec(v_n_1530_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg___lam__0(lean_object* v_f_1534_, lean_object* v_x1_1535_, lean_object* v_x2_1536_){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_apply_1(v_f_1534_, v_x2_1536_);
v___x_1538_ = l_Array_append___redArg(v_x1_1535_, v___x_1537_);
lean_dec_ref(v___x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg(lean_object* v_xs_1539_, lean_object* v_f_1540_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1542_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1543_ = lean_array_get_size(v_xs_1539_);
v___x_1544_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1545_ = lean_nat_dec_lt(v___x_1541_, v___x_1543_);
if (v___x_1545_ == 0)
{
lean_dec_ref(v_f_1540_);
lean_dec_ref(v_xs_1539_);
return v___x_1542_;
}
else
{
lean_object* v___f_1546_; size_t v___x_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v___f_1546_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1546_, 0, v_f_1540_);
v___x_1547_ = ((size_t)0ULL);
v___x_1548_ = lean_usize_of_nat(v___x_1543_);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1544_, v___f_1546_, v_xs_1539_, v___x_1547_, v___x_1548_, v___x_1542_);
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap(lean_object* v_00_u03b1_1550_, lean_object* v_n_1551_, lean_object* v_00_u03b2_1552_, lean_object* v_m_1553_, lean_object* v_xs_1554_, lean_object* v_f_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1558_ = lean_array_get_size(v_xs_1554_);
v___x_1559_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1560_ = lean_nat_dec_lt(v___x_1556_, v___x_1558_);
if (v___x_1560_ == 0)
{
lean_dec_ref(v_f_1555_);
lean_dec_ref(v_xs_1554_);
return v___x_1557_;
}
else
{
lean_object* v___f_1561_; size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v___f_1561_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1561_, 0, v_f_1555_);
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = lean_usize_of_nat(v___x_1558_);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1559_, v___f_1561_, v_xs_1554_, v___x_1562_, v___x_1563_, v___x_1557_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_n_1566_, lean_object* v_00_u03b2_1567_, lean_object* v_m_1568_, lean_object* v_xs_1569_, lean_object* v_f_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Vector_flatMap(v_00_u03b1_1565_, v_n_1566_, v_00_u03b2_1567_, v_m_1568_, v_xs_1569_, v_f_1570_);
lean_dec(v_m_1568_);
lean_dec(v_n_1566_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg(lean_object* v_xs_1572_, lean_object* v_k_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Array_zipIdx___redArg(v_xs_1572_, v_k_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg___boxed(lean_object* v_xs_1575_, lean_object* v_k_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Vector_zipIdx___redArg(v_xs_1575_, v_k_1576_);
lean_dec(v_k_1576_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx(lean_object* v_00_u03b1_1578_, lean_object* v_n_1579_, lean_object* v_xs_1580_, lean_object* v_k_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Array_zipIdx___redArg(v_xs_1580_, v_k_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_n_1584_, lean_object* v_xs_1585_, lean_object* v_k_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Vector_zipIdx(v_00_u03b1_1583_, v_n_1584_, v_xs_1585_, v_k_1586_);
lean_dec(v_k_1586_);
lean_dec(v_n_1584_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg(lean_object* v_as_1588_, lean_object* v_bs_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Array_zip___redArg(v_as_1588_, v_bs_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg___boxed(lean_object* v_as_1591_, lean_object* v_bs_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Vector_zip___redArg(v_as_1591_, v_bs_1592_);
lean_dec_ref(v_bs_1592_);
lean_dec_ref(v_as_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip(lean_object* v_00_u03b1_1594_, lean_object* v_n_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_as_1597_, lean_object* v_bs_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Array_zip___redArg(v_as_1597_, v_bs_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___boxed(lean_object* v_00_u03b1_1600_, lean_object* v_n_1601_, lean_object* v_00_u03b2_1602_, lean_object* v_as_1603_, lean_object* v_bs_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Vector_zip(v_00_u03b1_1600_, v_n_1601_, v_00_u03b2_1602_, v_as_1603_, v_bs_1604_);
lean_dec_ref(v_bs_1604_);
lean_dec_ref(v_as_1603_);
lean_dec(v_n_1601_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___redArg(lean_object* v_f_1606_, lean_object* v_as_1607_, lean_object* v_bs_1608_){
_start:
{
lean_object* v___f_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___f_1609_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1609_, 0, v_f_1606_);
v___x_1610_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1613_ = l_Array_zipWithMAux___redArg(v___x_1610_, v_as_1607_, v_bs_1608_, v___f_1609_, v___x_1611_, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith(lean_object* v_00_u03b1_1614_, lean_object* v_00_u03b2_1615_, lean_object* v_00_u03c6_1616_, lean_object* v_n_1617_, lean_object* v_f_1618_, lean_object* v_as_1619_, lean_object* v_bs_1620_){
_start:
{
lean_object* v___f_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___f_1621_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1621_, 0, v_f_1618_);
v___x_1622_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1625_ = l_Array_zipWithMAux___redArg(v___x_1622_, v_as_1619_, v_bs_1620_, v___f_1621_, v___x_1623_, v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___boxed(lean_object* v_00_u03b1_1626_, lean_object* v_00_u03b2_1627_, lean_object* v_00_u03c6_1628_, lean_object* v_n_1629_, lean_object* v_f_1630_, lean_object* v_as_1631_, lean_object* v_bs_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Vector_zipWith(v_00_u03b1_1626_, v_00_u03b2_1627_, v_00_u03c6_1628_, v_n_1629_, v_f_1630_, v_as_1631_, v_bs_1632_);
lean_dec(v_n_1629_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg(lean_object* v_xs_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v_fst_1636_; lean_object* v_snd_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
v___x_1635_ = l_Array_unzip___redArg(v_xs_1634_);
v_fst_1636_ = lean_ctor_get(v___x_1635_, 0);
v_snd_1637_ = lean_ctor_get(v___x_1635_, 1);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1635_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_snd_1637_);
lean_inc(v_fst_1636_);
lean_dec(v___x_1635_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_fst_1636_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_snd_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg___boxed(lean_object* v_xs_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Vector_unzip___redArg(v_xs_1645_);
lean_dec_ref(v_xs_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip(lean_object* v_00_u03b1_1647_, lean_object* v_00_u03b2_1648_, lean_object* v_n_1649_, lean_object* v_xs_1650_){
_start:
{
lean_object* v___x_1651_; lean_object* v_fst_1652_; lean_object* v_snd_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v___x_1651_ = l_Array_unzip___redArg(v_xs_1650_);
v_fst_1652_ = lean_ctor_get(v___x_1651_, 0);
v_snd_1653_ = lean_ctor_get(v___x_1651_, 1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1651_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_snd_1653_);
lean_inc(v_fst_1652_);
lean_dec(v___x_1651_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_fst_1652_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_snd_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___boxed(lean_object* v_00_u03b1_1661_, lean_object* v_00_u03b2_1662_, lean_object* v_n_1663_, lean_object* v_xs_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Vector_unzip(v_00_u03b1_1661_, v_00_u03b2_1662_, v_n_1663_, v_xs_1664_);
lean_dec_ref(v_xs_1664_);
lean_dec(v_n_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn___redArg(lean_object* v_n_1666_, lean_object* v_f_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Array_ofFn___redArg(v_n_1666_, v_f_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn(lean_object* v_n_1669_, lean_object* v_00_u03b1_1670_, lean_object* v_f_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Array_ofFn___redArg(v_n_1669_, v_f_1671_);
return v___x_1672_;
}
}
static lean_object* _init_l_Vector_swap___auto__1(void){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1673_;
}
}
static lean_object* _init_l_Vector_swap___auto__3(void){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg(lean_object* v_xs_1675_, lean_object* v_i_1676_, lean_object* v_j_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_array_fswap(v_xs_1675_, v_i_1676_, v_j_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg___boxed(lean_object* v_xs_1679_, lean_object* v_i_1680_, lean_object* v_j_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Vector_swap___redArg(v_xs_1679_, v_i_1680_, v_j_1681_);
lean_dec(v_j_1681_);
lean_dec(v_i_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap(lean_object* v_00_u03b1_1683_, lean_object* v_n_1684_, lean_object* v_xs_1685_, lean_object* v_i_1686_, lean_object* v_j_1687_, lean_object* v_hi_1688_, lean_object* v_hj_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_array_fswap(v_xs_1685_, v_i_1686_, v_j_1687_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___boxed(lean_object* v_00_u03b1_1691_, lean_object* v_n_1692_, lean_object* v_xs_1693_, lean_object* v_i_1694_, lean_object* v_j_1695_, lean_object* v_hi_1696_, lean_object* v_hj_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Vector_swap(v_00_u03b1_1691_, v_n_1692_, v_xs_1693_, v_i_1694_, v_j_1695_, v_hi_1696_, v_hj_1697_);
lean_dec(v_j_1695_);
lean_dec(v_i_1694_);
lean_dec(v_n_1692_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg(lean_object* v_xs_1699_, lean_object* v_i_1700_, lean_object* v_j_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_array_swap(v_xs_1699_, v_i_1700_, v_j_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg___boxed(lean_object* v_xs_1703_, lean_object* v_i_1704_, lean_object* v_j_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Vector_swapIfInBounds___redArg(v_xs_1703_, v_i_1704_, v_j_1705_);
lean_dec(v_j_1705_);
lean_dec(v_i_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds(lean_object* v_00_u03b1_1707_, lean_object* v_n_1708_, lean_object* v_xs_1709_, lean_object* v_i_1710_, lean_object* v_j_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_array_swap(v_xs_1709_, v_i_1710_, v_j_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_n_1714_, lean_object* v_xs_1715_, lean_object* v_i_1716_, lean_object* v_j_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Vector_swapIfInBounds(v_00_u03b1_1713_, v_n_1714_, v_xs_1715_, v_i_1716_, v_j_1717_);
lean_dec(v_j_1717_);
lean_dec(v_i_1716_);
lean_dec(v_n_1714_);
return v_res_1718_;
}
}
static lean_object* _init_l_Vector_swapAt___auto__1(void){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg(lean_object* v_xs_1720_, lean_object* v_i_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v_e_1723_; lean_object* v_xs_x27_1724_; lean_object* v___x_1725_; 
v_e_1723_ = lean_array_fget(v_xs_1720_, v_i_1721_);
v_xs_x27_1724_ = lean_array_fset(v_xs_1720_, v_i_1721_, v_x_1722_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_e_1723_);
lean_ctor_set(v___x_1725_, 1, v_xs_x27_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg___boxed(lean_object* v_xs_1726_, lean_object* v_i_1727_, lean_object* v_x_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Vector_swapAt___redArg(v_xs_1726_, v_i_1727_, v_x_1728_);
lean_dec(v_i_1727_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt(lean_object* v_00_u03b1_1730_, lean_object* v_n_1731_, lean_object* v_xs_1732_, lean_object* v_i_1733_, lean_object* v_x_1734_, lean_object* v_hi_1735_){
_start:
{
lean_object* v_e_1736_; lean_object* v_xs_x27_1737_; lean_object* v___x_1738_; 
v_e_1736_ = lean_array_fget(v_xs_1732_, v_i_1733_);
v_xs_x27_1737_ = lean_array_fset(v_xs_1732_, v_i_1733_, v_x_1734_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v_e_1736_);
lean_ctor_set(v___x_1738_, 1, v_xs_x27_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___boxed(lean_object* v_00_u03b1_1739_, lean_object* v_n_1740_, lean_object* v_xs_1741_, lean_object* v_i_1742_, lean_object* v_x_1743_, lean_object* v_hi_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Vector_swapAt(v_00_u03b1_1739_, v_n_1740_, v_xs_1741_, v_i_1742_, v_x_1743_, v_hi_1744_);
lean_dec(v_i_1742_);
lean_dec(v_n_1740_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___redArg(lean_object* v_xs_1750_, lean_object* v_i_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = lean_array_get_size(v_xs_1750_);
v___x_1754_ = lean_nat_dec_lt(v_i_1751_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v_this_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v_fst_1767_; lean_object* v_snd_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_this_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1755_, 0, v_x_1752_);
lean_ctor_set(v_this_1755_, 1, v_xs_1750_);
v___x_1756_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1757_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1758_ = lean_unsigned_to_nat(463u);
v___x_1759_ = lean_unsigned_to_nat(4u);
v___x_1760_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1761_ = l_Nat_reprFast(v_i_1751_);
v___x_1762_ = lean_string_append(v___x_1760_, v___x_1761_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1764_ = lean_string_append(v___x_1762_, v___x_1763_);
v___x_1765_ = l_mkPanicMessageWithDecl(v___x_1756_, v___x_1757_, v___x_1758_, v___x_1759_, v___x_1764_);
lean_dec_ref(v___x_1764_);
v___x_1766_ = l_panic___redArg(v_this_1755_, v___x_1765_);
lean_dec_ref_known(v_this_1755_, 2);
v_fst_1767_ = lean_ctor_get(v___x_1766_, 0);
v_snd_1768_ = lean_ctor_get(v___x_1766_, 1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1766_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_snd_1768_);
lean_inc(v_fst_1767_);
lean_dec(v___x_1766_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_fst_1767_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_snd_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
else
{
lean_object* v_e_1776_; lean_object* v_xs_x27_1777_; lean_object* v___x_1778_; 
v_e_1776_ = lean_array_fget(v_xs_1750_, v_i_1751_);
v_xs_x27_1777_ = lean_array_fset(v_xs_1750_, v_i_1751_, v_x_1752_);
lean_dec(v_i_1751_);
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v_e_1776_);
lean_ctor_set(v___x_1778_, 1, v_xs_x27_1777_);
return v___x_1778_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21(lean_object* v_00_u03b1_1779_, lean_object* v_n_1780_, lean_object* v_xs_1781_, lean_object* v_i_1782_, lean_object* v_x_1783_){
_start:
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = lean_array_get_size(v_xs_1781_);
v___x_1785_ = lean_nat_dec_lt(v_i_1782_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v_this_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v_fst_1798_; lean_object* v_snd_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
v_this_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1786_, 0, v_x_1783_);
lean_ctor_set(v_this_1786_, 1, v_xs_1781_);
v___x_1787_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1788_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1789_ = lean_unsigned_to_nat(463u);
v___x_1790_ = lean_unsigned_to_nat(4u);
v___x_1791_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1792_ = l_Nat_reprFast(v_i_1782_);
v___x_1793_ = lean_string_append(v___x_1791_, v___x_1792_);
lean_dec_ref(v___x_1792_);
v___x_1794_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1795_ = lean_string_append(v___x_1793_, v___x_1794_);
v___x_1796_ = l_mkPanicMessageWithDecl(v___x_1787_, v___x_1788_, v___x_1789_, v___x_1790_, v___x_1795_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = l_panic___redArg(v_this_1786_, v___x_1796_);
lean_dec_ref_known(v_this_1786_, 2);
v_fst_1798_ = lean_ctor_get(v___x_1797_, 0);
v_snd_1799_ = lean_ctor_get(v___x_1797_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1797_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_snd_1799_);
lean_inc(v_fst_1798_);
lean_dec(v___x_1797_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_fst_1798_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_snd_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
else
{
lean_object* v_e_1807_; lean_object* v_xs_x27_1808_; lean_object* v___x_1809_; 
v_e_1807_ = lean_array_fget(v_xs_1781_, v_i_1782_);
v_xs_x27_1808_ = lean_array_fset(v_xs_1781_, v_i_1782_, v_x_1783_);
lean_dec(v_i_1782_);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v_e_1807_);
lean_ctor_set(v___x_1809_, 1, v_xs_x27_1808_);
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___boxed(lean_object* v_00_u03b1_1810_, lean_object* v_n_1811_, lean_object* v_xs_1812_, lean_object* v_i_1813_, lean_object* v_x_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Vector_swapAt_x21(v_00_u03b1_1810_, v_n_1811_, v_xs_1812_, v_i_1813_, v_x_1814_);
lean_dec(v_n_1811_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Vector_range(lean_object* v_n_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Array_range(v_n_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Vector_range_x27(lean_object* v_start_1818_, lean_object* v_size_1819_, lean_object* v_step_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Array_range_x27(v_start_1818_, v_size_1819_, v_step_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv___redArg(lean_object* v_n_1822_, lean_object* v_xs_1823_, lean_object* v_ys_1824_, lean_object* v_r_1825_){
_start:
{
uint8_t v___x_1826_; 
v___x_1826_ = l_Array_isEqvAux___redArg(v_xs_1823_, v_ys_1824_, v_r_1825_, v_n_1822_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___redArg___boxed(lean_object* v_n_1827_, lean_object* v_xs_1828_, lean_object* v_ys_1829_, lean_object* v_r_1830_){
_start:
{
uint8_t v_res_1831_; lean_object* v_r_1832_; 
v_res_1831_ = l_Vector_isEqv___redArg(v_n_1827_, v_xs_1828_, v_ys_1829_, v_r_1830_);
lean_dec_ref(v_ys_1829_);
lean_dec_ref(v_xs_1828_);
v_r_1832_ = lean_box(v_res_1831_);
return v_r_1832_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv(lean_object* v_00_u03b1_1833_, lean_object* v_n_1834_, lean_object* v_xs_1835_, lean_object* v_ys_1836_, lean_object* v_r_1837_){
_start:
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Array_isEqvAux___redArg(v_xs_1835_, v_ys_1836_, v_r_1837_, v_n_1834_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___boxed(lean_object* v_00_u03b1_1839_, lean_object* v_n_1840_, lean_object* v_xs_1841_, lean_object* v_ys_1842_, lean_object* v_r_1843_){
_start:
{
uint8_t v_res_1844_; lean_object* v_r_1845_; 
v_res_1844_ = l_Vector_isEqv(v_00_u03b1_1839_, v_n_1840_, v_xs_1841_, v_ys_1842_, v_r_1843_);
lean_dec_ref(v_ys_1842_);
lean_dec_ref(v_xs_1841_);
v_r_1845_ = lean_box(v_res_1844_);
return v_r_1845_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__0(lean_object* v_inst_1846_, lean_object* v_x1_1847_, lean_object* v_x2_1848_){
_start:
{
lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = lean_apply_2(v_inst_1846_, v_x1_1847_, v_x2_1848_);
v___x_1850_ = lean_unbox(v___x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__0___boxed(lean_object* v_inst_1851_, lean_object* v_x1_1852_, lean_object* v_x2_1853_){
_start:
{
uint8_t v_res_1854_; lean_object* v_r_1855_; 
v_res_1854_ = l_Vector_instBEq___redArg___lam__0(v_inst_1851_, v_x1_1852_, v_x2_1853_);
v_r_1855_ = lean_box(v_res_1854_);
return v_r_1855_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__1(lean_object* v___f_1856_, lean_object* v_n_1857_, lean_object* v_xs_1858_, lean_object* v_ys_1859_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Array_isEqvAux___redArg(v_xs_1858_, v_ys_1859_, v___f_1856_, v_n_1857_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__1___boxed(lean_object* v___f_1861_, lean_object* v_n_1862_, lean_object* v_xs_1863_, lean_object* v_ys_1864_){
_start:
{
uint8_t v_res_1865_; lean_object* v_r_1866_; 
v_res_1865_ = l_Vector_instBEq___redArg___lam__1(v___f_1861_, v_n_1862_, v_xs_1863_, v_ys_1864_);
lean_dec_ref(v_ys_1864_);
lean_dec_ref(v_xs_1863_);
v_r_1866_ = lean_box(v_res_1865_);
return v_r_1866_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg(lean_object* v_n_1867_, lean_object* v_inst_1868_){
_start:
{
lean_object* v___f_1869_; lean_object* v___f_1870_; 
v___f_1869_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1869_, 0, v_inst_1868_);
v___f_1870_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1870_, 0, v___f_1869_);
lean_closure_set(v___f_1870_, 1, v_n_1867_);
return v___f_1870_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq(lean_object* v_00_u03b1_1871_, lean_object* v_n_1872_, lean_object* v_inst_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Vector_instBEq___redArg(v_n_1872_, v_inst_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___redArg(lean_object* v_xs_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Array_reverse___redArg(v_xs_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse(lean_object* v_00_u03b1_1877_, lean_object* v_n_1878_, lean_object* v_xs_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Array_reverse___redArg(v_xs_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___boxed(lean_object* v_00_u03b1_1881_, lean_object* v_n_1882_, lean_object* v_xs_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Vector_reverse(v_00_u03b1_1881_, v_n_1882_, v_xs_1883_);
lean_dec(v_n_1882_);
return v_res_1884_;
}
}
static lean_object* _init_l_Vector_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___redArg(lean_object* v_xs_1886_, lean_object* v_i_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Array_eraseIdx___redArg(v_xs_1886_, v_i_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx(lean_object* v_00_u03b1_1889_, lean_object* v_n_1890_, lean_object* v_xs_1891_, lean_object* v_i_1892_, lean_object* v_h_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Array_eraseIdx___redArg(v_xs_1891_, v_i_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___boxed(lean_object* v_00_u03b1_1895_, lean_object* v_n_1896_, lean_object* v_xs_1897_, lean_object* v_i_1898_, lean_object* v_h_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Vector_eraseIdx(v_00_u03b1_1895_, v_n_1896_, v_xs_1897_, v_i_1898_, v_h_1899_);
lean_dec(v_n_1896_);
return v_res_1900_;
}
}
static lean_object* _init_l_Vector_eraseIdx_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1904_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1905_ = lean_unsigned_to_nat(4u);
v___x_1906_ = lean_unsigned_to_nat(433u);
v___x_1907_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__1));
v___x_1908_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1909_ = l_mkPanicMessageWithDecl(v___x_1908_, v___x_1907_, v___x_1906_, v___x_1905_, v___x_1904_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg(lean_object* v_n_1910_, lean_object* v_xs_1911_, lean_object* v_i_1912_){
_start:
{
uint8_t v___x_1913_; 
v___x_1913_ = lean_nat_dec_lt(v_i_1912_, v_n_1910_);
if (v___x_1913_ == 0)
{
lean_object* v_this_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec(v_i_1912_);
v_this_1914_ = lean_array_pop(v_xs_1911_);
v___x_1915_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1916_ = l_panic___redArg(v_this_1914_, v___x_1915_);
lean_dec_ref(v_this_1914_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Array_eraseIdx___redArg(v_xs_1911_, v_i_1912_);
return v___x_1917_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg___boxed(lean_object* v_n_1918_, lean_object* v_xs_1919_, lean_object* v_i_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Vector_eraseIdx_x21___redArg(v_n_1918_, v_xs_1919_, v_i_1920_);
lean_dec(v_n_1918_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21(lean_object* v_00_u03b1_1922_, lean_object* v_n_1923_, lean_object* v_xs_1924_, lean_object* v_i_1925_){
_start:
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_nat_dec_lt(v_i_1925_, v_n_1923_);
if (v___x_1926_ == 0)
{
lean_object* v_this_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v_i_1925_);
v_this_1927_ = lean_array_pop(v_xs_1924_);
v___x_1928_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1929_ = l_panic___redArg(v_this_1927_, v___x_1928_);
lean_dec_ref(v_this_1927_);
return v___x_1929_;
}
else
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Array_eraseIdx___redArg(v_xs_1924_, v_i_1925_);
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___boxed(lean_object* v_00_u03b1_1931_, lean_object* v_n_1932_, lean_object* v_xs_1933_, lean_object* v_i_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Vector_eraseIdx_x21(v_00_u03b1_1931_, v_n_1932_, v_xs_1933_, v_i_1934_);
lean_dec(v_n_1932_);
return v_res_1935_;
}
}
static lean_object* _init_l_Vector_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg(lean_object* v_xs_1937_, lean_object* v_i_1938_, lean_object* v_x_1939_){
_start:
{
lean_object* v_j_1940_; lean_object* v_as_1941_; lean_object* v___x_1942_; 
v_j_1940_ = lean_array_get_size(v_xs_1937_);
v_as_1941_ = lean_array_push(v_xs_1937_, v_x_1939_);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1938_, v_as_1941_, v_j_1940_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg___boxed(lean_object* v_xs_1943_, lean_object* v_i_1944_, lean_object* v_x_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Vector_insertIdx___redArg(v_xs_1943_, v_i_1944_, v_x_1945_);
lean_dec(v_i_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx(lean_object* v_00_u03b1_1947_, lean_object* v_n_1948_, lean_object* v_xs_1949_, lean_object* v_i_1950_, lean_object* v_x_1951_, lean_object* v_h_1952_){
_start:
{
lean_object* v_j_1953_; lean_object* v_as_1954_; lean_object* v___x_1955_; 
v_j_1953_ = lean_array_get_size(v_xs_1949_);
v_as_1954_ = lean_array_push(v_xs_1949_, v_x_1951_);
v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1950_, v_as_1954_, v_j_1953_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___boxed(lean_object* v_00_u03b1_1956_, lean_object* v_n_1957_, lean_object* v_xs_1958_, lean_object* v_i_1959_, lean_object* v_x_1960_, lean_object* v_h_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Vector_insertIdx(v_00_u03b1_1956_, v_n_1957_, v_xs_1958_, v_i_1959_, v_x_1960_, v_h_1961_);
lean_dec(v_i_1959_);
lean_dec(v_n_1957_);
return v_res_1962_;
}
}
static lean_object* _init_l_Vector_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1964_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1965_ = lean_unsigned_to_nat(4u);
v___x_1966_ = lean_unsigned_to_nat(446u);
v___x_1967_ = ((lean_object*)(l_Vector_insertIdx_x21___redArg___closed__0));
v___x_1968_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1969_ = l_mkPanicMessageWithDecl(v___x_1968_, v___x_1967_, v___x_1966_, v___x_1965_, v___x_1964_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg(lean_object* v_n_1970_, lean_object* v_xs_1971_, lean_object* v_i_1972_, lean_object* v_x_1973_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_nat_dec_le(v_i_1972_, v_n_1970_);
if (v___x_1974_ == 0)
{
lean_object* v_this_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_this_1975_ = lean_array_push(v_xs_1971_, v_x_1973_);
v___x_1976_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1977_ = l_panic___redArg(v_this_1975_, v___x_1976_);
lean_dec_ref(v_this_1975_);
return v___x_1977_;
}
else
{
lean_object* v_j_1978_; lean_object* v_as_1979_; lean_object* v___x_1980_; 
v_j_1978_ = lean_array_get_size(v_xs_1971_);
v_as_1979_ = lean_array_push(v_xs_1971_, v_x_1973_);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1972_, v_as_1979_, v_j_1978_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg___boxed(lean_object* v_n_1981_, lean_object* v_xs_1982_, lean_object* v_i_1983_, lean_object* v_x_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Vector_insertIdx_x21___redArg(v_n_1981_, v_xs_1982_, v_i_1983_, v_x_1984_);
lean_dec(v_i_1983_);
lean_dec(v_n_1981_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21(lean_object* v_00_u03b1_1986_, lean_object* v_n_1987_, lean_object* v_xs_1988_, lean_object* v_i_1989_, lean_object* v_x_1990_){
_start:
{
uint8_t v___x_1991_; 
v___x_1991_ = lean_nat_dec_le(v_i_1989_, v_n_1987_);
if (v___x_1991_ == 0)
{
lean_object* v_this_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_this_1992_ = lean_array_push(v_xs_1988_, v_x_1990_);
v___x_1993_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1994_ = l_panic___redArg(v_this_1992_, v___x_1993_);
lean_dec_ref(v_this_1992_);
return v___x_1994_;
}
else
{
lean_object* v_j_1995_; lean_object* v_as_1996_; lean_object* v___x_1997_; 
v_j_1995_ = lean_array_get_size(v_xs_1988_);
v_as_1996_ = lean_array_push(v_xs_1988_, v_x_1990_);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1989_, v_as_1996_, v_j_1995_);
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___boxed(lean_object* v_00_u03b1_1998_, lean_object* v_n_1999_, lean_object* v_xs_2000_, lean_object* v_i_2001_, lean_object* v_x_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Vector_insertIdx_x21(v_00_u03b1_1998_, v_n_1999_, v_xs_2000_, v_i_2001_, v_x_2002_);
lean_dec(v_i_2001_);
lean_dec(v_n_1999_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg(lean_object* v_n_2004_, lean_object* v_xs_2005_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = l_Array_extract___redArg(v_xs_2005_, v___x_2006_, v_n_2004_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg___boxed(lean_object* v_n_2008_, lean_object* v_xs_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Vector_tail___redArg(v_n_2008_, v_xs_2009_);
lean_dec_ref(v_xs_2009_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail(lean_object* v_00_u03b1_2011_, lean_object* v_n_2012_, lean_object* v_xs_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = l_Array_extract___redArg(v_xs_2013_, v___x_2014_, v_n_2012_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___boxed(lean_object* v_00_u03b1_2016_, lean_object* v_n_2017_, lean_object* v_xs_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Vector_tail(v_00_u03b1_2016_, v_n_2017_, v_xs_2018_);
lean_dec_ref(v_xs_2018_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg(lean_object* v_inst_2020_, lean_object* v_xs_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Array_finIdxOf_x3f___redArg(v_inst_2020_, v_xs_2021_, v_x_2022_);
if (lean_obj_tag(v___x_2023_) == 0)
{
return v___x_2023_;
}
else
{
lean_object* v_val_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
v_val_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_val_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_val_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_2032_, lean_object* v_xs_2033_, lean_object* v_x_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Vector_finIdxOf_x3f___redArg(v_inst_2032_, v_xs_2033_, v_x_2034_);
lean_dec_ref(v_xs_2033_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f(lean_object* v_00_u03b1_2036_, lean_object* v_n_2037_, lean_object* v_inst_2038_, lean_object* v_xs_2039_, lean_object* v_x_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Array_finIdxOf_x3f___redArg(v_inst_2038_, v_xs_2039_, v_x_2040_);
if (lean_obj_tag(v___x_2041_) == 0)
{
return v___x_2041_;
}
else
{
lean_object* v_val_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
v_val_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_val_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_val_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_2050_, lean_object* v_n_2051_, lean_object* v_inst_2052_, lean_object* v_xs_2053_, lean_object* v_x_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Vector_finIdxOf_x3f(v_00_u03b1_2050_, v_n_2051_, v_inst_2052_, v_xs_2053_, v_x_2054_);
lean_dec_ref(v_xs_2053_);
lean_dec(v_n_2051_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg(lean_object* v_p_2056_, lean_object* v_xs_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2056_, v_xs_2057_, v___x_2058_);
if (lean_obj_tag(v___x_2059_) == 0)
{
return v___x_2059_;
}
else
{
lean_object* v_val_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
v_val_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_val_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_val_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2068_, lean_object* v_xs_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Vector_findFinIdx_x3f___redArg(v_p_2068_, v_xs_2069_);
lean_dec_ref(v_xs_2069_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f(lean_object* v_00_u03b1_2071_, lean_object* v_n_2072_, lean_object* v_p_2073_, lean_object* v_xs_2074_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_unsigned_to_nat(0u);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2073_, v_xs_2074_, v___x_2075_);
if (lean_obj_tag(v___x_2076_) == 0)
{
return v___x_2076_;
}
else
{
lean_object* v_val_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_val_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_val_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_val_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2085_, lean_object* v_n_2086_, lean_object* v_p_2087_, lean_object* v_xs_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Vector_findFinIdx_x3f(v_00_u03b1_2085_, v_n_2086_, v_p_2087_, v_xs_2088_);
lean_dec_ref(v_xs_2088_);
lean_dec(v_n_2086_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__0(lean_object* v_toPure_2090_, lean_object* v_____s_2091_){
_start:
{
lean_object* v_fst_2092_; 
v_fst_2092_ = lean_ctor_get(v_____s_2091_, 0);
lean_inc(v_fst_2092_);
lean_dec_ref(v_____s_2091_);
if (lean_obj_tag(v_fst_2092_) == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_apply_2(v_toPure_2090_, lean_box(0), v___x_2093_);
return v___x_2094_;
}
else
{
lean_object* v_val_2095_; lean_object* v___x_2096_; 
v_val_2095_ = lean_ctor_get(v_fst_2092_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v_fst_2092_, 1);
v___x_2096_ = lean_apply_2(v_toPure_2090_, lean_box(0), v_val_2095_);
return v___x_2096_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1(lean_object* v___x_2097_, lean_object* v_toPure_2098_, lean_object* v_a_2099_, lean_object* v___x_2100_, uint8_t v_____do__lift_2101_){
_start:
{
if (v_____do__lift_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
lean_dec(v_a_2099_);
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2097_);
v___x_2103_ = lean_apply_2(v_toPure_2098_, lean_box(0), v___x_2102_);
return v___x_2103_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec_ref(v___x_2097_);
v___x_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2104_, 0, v_a_2099_);
v___x_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v___x_2100_);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
v___x_2108_ = lean_apply_2(v_toPure_2098_, lean_box(0), v___x_2107_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_2109_, lean_object* v_toPure_2110_, lean_object* v_a_2111_, lean_object* v___x_2112_, lean_object* v_____do__lift_2113_){
_start:
{
uint8_t v_____do__lift_124__boxed_2114_; lean_object* v_res_2115_; 
v_____do__lift_124__boxed_2114_ = lean_unbox(v_____do__lift_2113_);
v_res_2115_ = l_Vector_findM_x3f___redArg___lam__1(v___x_2109_, v_toPure_2110_, v_a_2111_, v___x_2112_, v_____do__lift_124__boxed_2114_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2(lean_object* v___x_2116_, lean_object* v_toPure_2117_, lean_object* v___x_2118_, lean_object* v_f_2119_, lean_object* v_toBind_2120_, lean_object* v_a_2121_, lean_object* v_x_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_inc(v_a_2121_);
v___f_2124_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2124_, 0, v___x_2116_);
lean_closure_set(v___f_2124_, 1, v_toPure_2117_);
lean_closure_set(v___f_2124_, 2, v_a_2121_);
lean_closure_set(v___f_2124_, 3, v___x_2118_);
v___x_2125_ = lean_apply_1(v_f_2119_, v_a_2121_);
v___x_2126_ = lean_apply_4(v_toBind_2120_, lean_box(0), lean_box(0), v___x_2125_, v___f_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2___boxed(lean_object* v___x_2127_, lean_object* v_toPure_2128_, lean_object* v___x_2129_, lean_object* v_f_2130_, lean_object* v_toBind_2131_, lean_object* v_a_2132_, lean_object* v_x_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Vector_findM_x3f___redArg___lam__2(v___x_2127_, v_toPure_2128_, v___x_2129_, v_f_2130_, v_toBind_2131_, v_a_2132_, v_x_2133_, v___y_2134_);
lean_dec_ref(v___y_2134_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg(lean_object* v_inst_2139_, lean_object* v_f_2140_, lean_object* v_as_2141_){
_start:
{
lean_object* v_toApplicative_2142_; lean_object* v_toBind_2143_; lean_object* v_toPure_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___f_2147_; lean_object* v___f_2148_; size_t v_sz_2149_; size_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_toApplicative_2142_ = lean_ctor_get(v_inst_2139_, 0);
v_toBind_2143_ = lean_ctor_get(v_inst_2139_, 1);
lean_inc_n(v_toBind_2143_, 2);
v_toPure_2144_ = lean_ctor_get(v_toApplicative_2142_, 1);
v___x_2145_ = lean_box(0);
v___x_2146_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2144_, 2);
v___f_2147_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2147_, 0, v_toPure_2144_);
v___f_2148_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2148_, 0, v___x_2146_);
lean_closure_set(v___f_2148_, 1, v_toPure_2144_);
lean_closure_set(v___f_2148_, 2, v___x_2145_);
lean_closure_set(v___f_2148_, 3, v_f_2140_);
lean_closure_set(v___f_2148_, 4, v_toBind_2143_);
v_sz_2149_ = lean_array_size(v_as_2141_);
v___x_2150_ = ((size_t)0ULL);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2139_, v_as_2141_, v___f_2148_, v_sz_2149_, v___x_2150_, v___x_2146_);
v___x_2152_ = lean_apply_4(v_toBind_2143_, lean_box(0), lean_box(0), v___x_2151_, v___f_2147_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f(lean_object* v_n_2153_, lean_object* v_00_u03b1_2154_, lean_object* v_m_2155_, lean_object* v_inst_2156_, lean_object* v_f_2157_, lean_object* v_as_2158_){
_start:
{
lean_object* v_toApplicative_2159_; lean_object* v_toBind_2160_; lean_object* v_toPure_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___f_2164_; lean_object* v___f_2165_; size_t v_sz_2166_; size_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_toApplicative_2159_ = lean_ctor_get(v_inst_2156_, 0);
v_toBind_2160_ = lean_ctor_get(v_inst_2156_, 1);
lean_inc_n(v_toBind_2160_, 2);
v_toPure_2161_ = lean_ctor_get(v_toApplicative_2159_, 1);
v___x_2162_ = lean_box(0);
v___x_2163_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2161_, 2);
v___f_2164_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2164_, 0, v_toPure_2161_);
v___f_2165_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2165_, 0, v___x_2163_);
lean_closure_set(v___f_2165_, 1, v_toPure_2161_);
lean_closure_set(v___f_2165_, 2, v___x_2162_);
lean_closure_set(v___f_2165_, 3, v_f_2157_);
lean_closure_set(v___f_2165_, 4, v_toBind_2160_);
v_sz_2166_ = lean_array_size(v_as_2158_);
v___x_2167_ = ((size_t)0ULL);
v___x_2168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2156_, v_as_2158_, v___f_2165_, v_sz_2166_, v___x_2167_, v___x_2163_);
v___x_2169_ = lean_apply_4(v_toBind_2160_, lean_box(0), lean_box(0), v___x_2168_, v___f_2164_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___boxed(lean_object* v_n_2170_, lean_object* v_00_u03b1_2171_, lean_object* v_m_2172_, lean_object* v_inst_2173_, lean_object* v_f_2174_, lean_object* v_as_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Vector_findM_x3f(v_n_2170_, v_00_u03b1_2171_, v_m_2172_, v_inst_2173_, v_f_2174_, v_as_2175_);
lean_dec(v_n_2170_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__1(lean_object* v___x_2177_, lean_object* v_toPure_2178_, lean_object* v___x_2179_, lean_object* v_____do__lift_2180_){
_start:
{
if (lean_obj_tag(v_____do__lift_2180_) == 1)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_dec_ref(v___x_2179_);
v___x_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_____do__lift_2180_);
v___x_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2177_);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
v___x_2184_ = lean_apply_2(v_toPure_2178_, lean_box(0), v___x_2183_);
return v___x_2184_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec(v_____do__lift_2180_);
v___x_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2179_);
v___x_2186_ = lean_apply_2(v_toPure_2178_, lean_box(0), v___x_2185_);
return v___x_2186_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0(lean_object* v_f_2187_, lean_object* v_toBind_2188_, lean_object* v___f_2189_, lean_object* v_a_2190_, lean_object* v_x_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_apply_1(v_f_2187_, v_a_2190_);
v___x_2194_ = lean_apply_4(v_toBind_2188_, lean_box(0), lean_box(0), v___x_2193_, v___f_2189_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0___boxed(lean_object* v_f_2195_, lean_object* v_toBind_2196_, lean_object* v___f_2197_, lean_object* v_a_2198_, lean_object* v_x_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Vector_findSomeM_x3f___redArg___lam__0(v_f_2195_, v_toBind_2196_, v___f_2197_, v_a_2198_, v_x_2199_, v___y_2200_);
lean_dec_ref(v___y_2200_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg(lean_object* v_inst_2202_, lean_object* v_f_2203_, lean_object* v_as_2204_){
_start:
{
lean_object* v_toApplicative_2205_; lean_object* v_toBind_2206_; lean_object* v_toPure_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___f_2210_; lean_object* v___f_2211_; lean_object* v___f_2212_; size_t v_sz_2213_; size_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v_toApplicative_2205_ = lean_ctor_get(v_inst_2202_, 0);
v_toBind_2206_ = lean_ctor_get(v_inst_2202_, 1);
lean_inc_n(v_toBind_2206_, 2);
v_toPure_2207_ = lean_ctor_get(v_toApplicative_2205_, 1);
v___x_2208_ = lean_box(0);
v___x_2209_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2207_, 2);
v___f_2210_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2210_, 0, v_toPure_2207_);
v___f_2211_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2211_, 0, v___x_2208_);
lean_closure_set(v___f_2211_, 1, v_toPure_2207_);
lean_closure_set(v___f_2211_, 2, v___x_2209_);
v___f_2212_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2212_, 0, v_f_2203_);
lean_closure_set(v___f_2212_, 1, v_toBind_2206_);
lean_closure_set(v___f_2212_, 2, v___f_2211_);
v_sz_2213_ = lean_array_size(v_as_2204_);
v___x_2214_ = ((size_t)0ULL);
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2202_, v_as_2204_, v___f_2212_, v_sz_2213_, v___x_2214_, v___x_2209_);
v___x_2216_ = lean_apply_4(v_toBind_2206_, lean_box(0), lean_box(0), v___x_2215_, v___f_2210_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f(lean_object* v_m_2217_, lean_object* v_00_u03b1_2218_, lean_object* v_00_u03b2_2219_, lean_object* v_n_2220_, lean_object* v_inst_2221_, lean_object* v_f_2222_, lean_object* v_as_2223_){
_start:
{
lean_object* v_toApplicative_2224_; lean_object* v_toBind_2225_; lean_object* v_toPure_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___f_2229_; lean_object* v___f_2230_; lean_object* v___f_2231_; size_t v_sz_2232_; size_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_toApplicative_2224_ = lean_ctor_get(v_inst_2221_, 0);
v_toBind_2225_ = lean_ctor_get(v_inst_2221_, 1);
lean_inc_n(v_toBind_2225_, 2);
v_toPure_2226_ = lean_ctor_get(v_toApplicative_2224_, 1);
v___x_2227_ = lean_box(0);
v___x_2228_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2226_, 2);
v___f_2229_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2229_, 0, v_toPure_2226_);
v___f_2230_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2230_, 0, v___x_2227_);
lean_closure_set(v___f_2230_, 1, v_toPure_2226_);
lean_closure_set(v___f_2230_, 2, v___x_2228_);
v___f_2231_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2231_, 0, v_f_2222_);
lean_closure_set(v___f_2231_, 1, v_toBind_2225_);
lean_closure_set(v___f_2231_, 2, v___f_2230_);
v_sz_2232_ = lean_array_size(v_as_2223_);
v___x_2233_ = ((size_t)0ULL);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2221_, v_as_2223_, v___f_2231_, v_sz_2232_, v___x_2233_, v___x_2228_);
v___x_2235_ = lean_apply_4(v_toBind_2225_, lean_box(0), lean_box(0), v___x_2234_, v___f_2229_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___boxed(lean_object* v_m_2236_, lean_object* v_00_u03b1_2237_, lean_object* v_00_u03b2_2238_, lean_object* v_n_2239_, lean_object* v_inst_2240_, lean_object* v_f_2241_, lean_object* v_as_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Vector_findSomeM_x3f(v_m_2236_, v_00_u03b1_2237_, v_00_u03b2_2238_, v_n_2239_, v_inst_2240_, v_f_2241_, v_as_2242_);
lean_dec(v_n_2239_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2244_, lean_object* v_a_2245_, uint8_t v_____do__lift_2246_){
_start:
{
if (v_____do__lift_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
lean_dec(v_a_2245_);
v___x_2247_ = lean_box(0);
v___x_2248_ = lean_apply_2(v_toPure_2244_, lean_box(0), v___x_2247_);
return v___x_2248_;
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_a_2245_);
v___x_2250_ = lean_apply_2(v_toPure_2244_, lean_box(0), v___x_2249_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2251_, lean_object* v_a_2252_, lean_object* v_____do__lift_2253_){
_start:
{
uint8_t v_____do__lift_50__boxed_2254_; lean_object* v_res_2255_; 
v_____do__lift_50__boxed_2254_ = lean_unbox(v_____do__lift_2253_);
v_res_2255_ = l_Vector_findRevM_x3f___redArg___lam__0(v_toPure_2251_, v_a_2252_, v_____do__lift_50__boxed_2254_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2256_, lean_object* v_f_2257_, lean_object* v_toBind_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___f_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_inc(v_a_2259_);
v___f_2260_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2260_, 0, v_toPure_2256_);
lean_closure_set(v___f_2260_, 1, v_a_2259_);
v___x_2261_ = lean_apply_1(v_f_2257_, v_a_2259_);
v___x_2262_ = lean_apply_4(v_toBind_2258_, lean_box(0), lean_box(0), v___x_2261_, v___f_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg(lean_object* v_inst_2263_, lean_object* v_f_2264_, lean_object* v_as_2265_){
_start:
{
lean_object* v_toApplicative_2266_; lean_object* v_toBind_2267_; lean_object* v_toPure_2268_; lean_object* v___f_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v_toApplicative_2266_ = lean_ctor_get(v_inst_2263_, 0);
v_toBind_2267_ = lean_ctor_get(v_inst_2263_, 1);
v_toPure_2268_ = lean_ctor_get(v_toApplicative_2266_, 1);
lean_inc(v_toBind_2267_);
lean_inc(v_toPure_2268_);
v___f_2269_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2269_, 0, v_toPure_2268_);
lean_closure_set(v___f_2269_, 1, v_f_2264_);
lean_closure_set(v___f_2269_, 2, v_toBind_2267_);
v___x_2270_ = lean_array_get_size(v_as_2265_);
v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2263_, v___f_2269_, v_as_2265_, v___x_2270_, lean_box(0));
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f(lean_object* v_n_2272_, lean_object* v_00_u03b1_2273_, lean_object* v_m_2274_, lean_object* v_inst_2275_, lean_object* v_f_2276_, lean_object* v_as_2277_){
_start:
{
lean_object* v_toApplicative_2278_; lean_object* v_toBind_2279_; lean_object* v_toPure_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_toApplicative_2278_ = lean_ctor_get(v_inst_2275_, 0);
v_toBind_2279_ = lean_ctor_get(v_inst_2275_, 1);
v_toPure_2280_ = lean_ctor_get(v_toApplicative_2278_, 1);
lean_inc(v_toBind_2279_);
lean_inc(v_toPure_2280_);
v___f_2281_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2281_, 0, v_toPure_2280_);
lean_closure_set(v___f_2281_, 1, v_f_2276_);
lean_closure_set(v___f_2281_, 2, v_toBind_2279_);
v___x_2282_ = lean_array_get_size(v_as_2277_);
v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2275_, v___f_2281_, v_as_2277_, v___x_2282_, lean_box(0));
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___boxed(lean_object* v_n_2284_, lean_object* v_00_u03b1_2285_, lean_object* v_m_2286_, lean_object* v_inst_2287_, lean_object* v_f_2288_, lean_object* v_as_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Vector_findRevM_x3f(v_n_2284_, v_00_u03b1_2285_, v_m_2286_, v_inst_2287_, v_f_2288_, v_as_2289_);
lean_dec(v_n_2284_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___redArg(lean_object* v_inst_2291_, lean_object* v_f_2292_, lean_object* v_as_2293_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_array_get_size(v_as_2293_);
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2291_, v_f_2292_, v_as_2293_, v___x_2294_, lean_box(0));
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f(lean_object* v_m_2296_, lean_object* v_00_u03b1_2297_, lean_object* v_00_u03b2_2298_, lean_object* v_n_2299_, lean_object* v_inst_2300_, lean_object* v_f_2301_, lean_object* v_as_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_array_get_size(v_as_2302_);
v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2300_, v_f_2301_, v_as_2302_, v___x_2303_, lean_box(0));
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___boxed(lean_object* v_m_2305_, lean_object* v_00_u03b1_2306_, lean_object* v_00_u03b2_2307_, lean_object* v_n_2308_, lean_object* v_inst_2309_, lean_object* v_f_2310_, lean_object* v_as_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Vector_findSomeRevM_x3f(v_m_2305_, v_00_u03b1_2306_, v_00_u03b2_2307_, v_n_2308_, v_inst_2309_, v_f_2310_, v_as_2311_);
lean_dec(v_n_2308_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0(lean_object* v_f_2313_, lean_object* v___x_2314_, lean_object* v___x_2315_, lean_object* v_a_2316_, lean_object* v_x_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2319_; uint8_t v___x_2320_; 
lean_inc(v_a_2316_);
v___x_2319_ = lean_apply_1(v_f_2313_, v_a_2316_);
v___x_2320_ = lean_unbox(v___x_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; 
lean_dec(v_a_2316_);
v___x_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2314_);
return v___x_2321_;
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_dec_ref(v___x_2314_);
v___x_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2322_, 0, v_a_2316_);
v___x_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
v___x_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
lean_ctor_set(v___x_2324_, 1, v___x_2315_);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
return v___x_2325_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0___boxed(lean_object* v_f_2326_, lean_object* v___x_2327_, lean_object* v___x_2328_, lean_object* v_a_2329_, lean_object* v_x_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Vector_find_x3f___redArg___lam__0(v_f_2326_, v___x_2327_, v___x_2328_, v_a_2329_, v_x_2330_, v___y_2331_);
lean_dec_ref(v___y_2331_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg(lean_object* v_f_2333_, lean_object* v_as_2334_){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___f_2339_; size_t v_sz_2340_; size_t v___x_2341_; lean_object* v___x_2342_; lean_object* v_fst_2343_; 
v___x_2335_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_box(0);
v___x_2338_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2339_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2339_, 0, v_f_2333_);
lean_closure_set(v___f_2339_, 1, v___x_2338_);
lean_closure_set(v___f_2339_, 2, v___x_2337_);
v_sz_2340_ = lean_array_size(v_as_2334_);
v___x_2341_ = ((size_t)0ULL);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2335_, v_as_2334_, v___f_2339_, v_sz_2340_, v___x_2341_, v___x_2338_);
v_fst_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_fst_2343_);
lean_dec(v___x_2342_);
if (lean_obj_tag(v_fst_2343_) == 0)
{
return v___x_2336_;
}
else
{
lean_object* v_val_2344_; 
v_val_2344_ = lean_ctor_get(v_fst_2343_, 0);
lean_inc(v_val_2344_);
lean_dec_ref_known(v_fst_2343_, 1);
return v_val_2344_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f(lean_object* v_n_2345_, lean_object* v_00_u03b1_2346_, lean_object* v_f_2347_, lean_object* v_as_2348_){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___f_2353_; size_t v_sz_2354_; size_t v___x_2355_; lean_object* v___x_2356_; lean_object* v_fst_2357_; 
v___x_2349_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2350_ = lean_box(0);
v___x_2351_ = lean_box(0);
v___x_2352_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2353_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2353_, 0, v_f_2347_);
lean_closure_set(v___f_2353_, 1, v___x_2352_);
lean_closure_set(v___f_2353_, 2, v___x_2351_);
v_sz_2354_ = lean_array_size(v_as_2348_);
v___x_2355_ = ((size_t)0ULL);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2349_, v_as_2348_, v___f_2353_, v_sz_2354_, v___x_2355_, v___x_2352_);
v_fst_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_fst_2357_);
lean_dec(v___x_2356_);
if (lean_obj_tag(v_fst_2357_) == 0)
{
return v___x_2350_;
}
else
{
lean_object* v_val_2358_; 
v_val_2358_ = lean_ctor_get(v_fst_2357_, 0);
lean_inc(v_val_2358_);
lean_dec_ref_known(v_fst_2357_, 1);
return v_val_2358_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___boxed(lean_object* v_n_2359_, lean_object* v_00_u03b1_2360_, lean_object* v_f_2361_, lean_object* v_as_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Vector_find_x3f(v_n_2359_, v_00_u03b1_2360_, v_f_2361_, v_as_2362_);
lean_dec(v_n_2359_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg___lam__0(lean_object* v_f_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v___x_2366_; uint8_t v___x_2367_; 
lean_inc(v_a_2365_);
v___x_2366_ = lean_apply_1(v_f_2364_, v_a_2365_);
v___x_2367_ = lean_unbox(v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; 
lean_dec(v_a_2365_);
v___x_2368_ = lean_box(0);
return v___x_2368_;
}
else
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2369_, 0, v_a_2365_);
return v___x_2369_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg(lean_object* v_f_2370_, lean_object* v_as_2371_){
_start:
{
lean_object* v___f_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___f_2372_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2372_, 0, v_f_2370_);
v___x_2373_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2374_ = lean_array_get_size(v_as_2371_);
v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2373_, v___f_2372_, v_as_2371_, v___x_2374_, lean_box(0));
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f(lean_object* v_n_2376_, lean_object* v_00_u03b1_2377_, lean_object* v_f_2378_, lean_object* v_as_2379_){
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
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___boxed(lean_object* v_n_2384_, lean_object* v_00_u03b1_2385_, lean_object* v_f_2386_, lean_object* v_as_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Vector_findRev_x3f(v_n_2384_, v_00_u03b1_2385_, v_f_2386_, v_as_2387_);
lean_dec(v_n_2384_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0(lean_object* v_f_2389_, lean_object* v___x_2390_, lean_object* v___x_2391_, lean_object* v_a_2392_, lean_object* v_x_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_apply_1(v_f_2389_, v_a_2392_);
if (lean_obj_tag(v___x_2395_) == 1)
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_dec_ref(v___x_2391_);
v___x_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
v___x_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
lean_ctor_set(v___x_2397_, 1, v___x_2390_);
v___x_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
return v___x_2398_;
}
else
{
lean_object* v___x_2399_; 
lean_dec(v___x_2395_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2391_);
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2400_, lean_object* v___x_2401_, lean_object* v___x_2402_, lean_object* v_a_2403_, lean_object* v_x_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Vector_findSome_x3f___redArg___lam__0(v_f_2400_, v___x_2401_, v___x_2402_, v_a_2403_, v_x_2404_, v___y_2405_);
lean_dec_ref(v___y_2405_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg(lean_object* v_f_2407_, lean_object* v_as_2408_){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___f_2413_; size_t v_sz_2414_; size_t v___x_2415_; lean_object* v___x_2416_; lean_object* v_fst_2417_; 
v___x_2409_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2410_ = lean_box(0);
v___x_2411_ = lean_box(0);
v___x_2412_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2413_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2413_, 0, v_f_2407_);
lean_closure_set(v___f_2413_, 1, v___x_2411_);
lean_closure_set(v___f_2413_, 2, v___x_2412_);
v_sz_2414_ = lean_array_size(v_as_2408_);
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2409_, v_as_2408_, v___f_2413_, v_sz_2414_, v___x_2415_, v___x_2412_);
v_fst_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_fst_2417_);
lean_dec(v___x_2416_);
if (lean_obj_tag(v_fst_2417_) == 0)
{
return v___x_2410_;
}
else
{
lean_object* v_val_2418_; 
v_val_2418_ = lean_ctor_get(v_fst_2417_, 0);
lean_inc(v_val_2418_);
lean_dec_ref_known(v_fst_2417_, 1);
return v_val_2418_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f(lean_object* v_00_u03b1_2419_, lean_object* v_00_u03b2_2420_, lean_object* v_n_2421_, lean_object* v_f_2422_, lean_object* v_as_2423_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___f_2428_; size_t v_sz_2429_; size_t v___x_2430_; lean_object* v___x_2431_; lean_object* v_fst_2432_; 
v___x_2424_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2425_ = lean_box(0);
v___x_2426_ = lean_box(0);
v___x_2427_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2428_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2428_, 0, v_f_2422_);
lean_closure_set(v___f_2428_, 1, v___x_2426_);
lean_closure_set(v___f_2428_, 2, v___x_2427_);
v_sz_2429_ = lean_array_size(v_as_2423_);
v___x_2430_ = ((size_t)0ULL);
v___x_2431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2424_, v_as_2423_, v___f_2428_, v_sz_2429_, v___x_2430_, v___x_2427_);
v_fst_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_fst_2432_);
lean_dec(v___x_2431_);
if (lean_obj_tag(v_fst_2432_) == 0)
{
return v___x_2425_;
}
else
{
lean_object* v_val_2433_; 
v_val_2433_ = lean_ctor_get(v_fst_2432_, 0);
lean_inc(v_val_2433_);
lean_dec_ref_known(v_fst_2432_, 1);
return v_val_2433_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_00_u03b2_2435_, lean_object* v_n_2436_, lean_object* v_f_2437_, lean_object* v_as_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Vector_findSome_x3f(v_00_u03b1_2434_, v_00_u03b2_2435_, v_n_2436_, v_f_2437_, v_as_2438_);
lean_dec(v_n_2436_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2440_, lean_object* v_x_2441_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_apply_1(v_f_2440_, v_x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg(lean_object* v_f_2443_, lean_object* v_as_2444_){
_start:
{
lean_object* v___f_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___f_2445_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2445_, 0, v_f_2443_);
v___x_2446_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2447_ = lean_array_get_size(v_as_2444_);
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2446_, v___f_2445_, v_as_2444_, v___x_2447_, lean_box(0));
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f(lean_object* v_00_u03b1_2449_, lean_object* v_00_u03b2_2450_, lean_object* v_n_2451_, lean_object* v_f_2452_, lean_object* v_as_2453_){
_start:
{
lean_object* v___f_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___f_2454_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2454_, 0, v_f_2452_);
v___x_2455_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2456_ = lean_array_get_size(v_as_2453_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2455_, v___f_2454_, v_as_2453_, v___x_2456_, lean_box(0));
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___boxed(lean_object* v_00_u03b1_2458_, lean_object* v_00_u03b2_2459_, lean_object* v_n_2460_, lean_object* v_f_2461_, lean_object* v_as_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Vector_findSomeRev_x3f(v_00_u03b1_2458_, v_00_u03b2_2459_, v_n_2460_, v_f_2461_, v_as_2462_);
lean_dec(v_n_2460_);
return v_res_2463_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf___redArg(lean_object* v_inst_2464_, lean_object* v_xs_2465_, lean_object* v_ys_2466_){
_start:
{
uint8_t v___x_2467_; 
v___x_2467_ = l_Array_isPrefixOf___redArg(v_inst_2464_, v_xs_2465_, v_ys_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___redArg___boxed(lean_object* v_inst_2468_, lean_object* v_xs_2469_, lean_object* v_ys_2470_){
_start:
{
uint8_t v_res_2471_; lean_object* v_r_2472_; 
v_res_2471_ = l_Vector_isPrefixOf___redArg(v_inst_2468_, v_xs_2469_, v_ys_2470_);
lean_dec_ref(v_ys_2470_);
lean_dec_ref(v_xs_2469_);
v_r_2472_ = lean_box(v_res_2471_);
return v_r_2472_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf(lean_object* v_00_u03b1_2473_, lean_object* v_m_2474_, lean_object* v_n_2475_, lean_object* v_inst_2476_, lean_object* v_xs_2477_, lean_object* v_ys_2478_){
_start:
{
uint8_t v___x_2479_; 
v___x_2479_ = l_Array_isPrefixOf___redArg(v_inst_2476_, v_xs_2477_, v_ys_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___boxed(lean_object* v_00_u03b1_2480_, lean_object* v_m_2481_, lean_object* v_n_2482_, lean_object* v_inst_2483_, lean_object* v_xs_2484_, lean_object* v_ys_2485_){
_start:
{
uint8_t v_res_2486_; lean_object* v_r_2487_; 
v_res_2486_ = l_Vector_isPrefixOf(v_00_u03b1_2480_, v_m_2481_, v_n_2482_, v_inst_2483_, v_xs_2484_, v_ys_2485_);
lean_dec_ref(v_ys_2485_);
lean_dec_ref(v_xs_2484_);
lean_dec(v_n_2482_);
lean_dec(v_m_2481_);
v_r_2487_ = lean_box(v_res_2486_);
return v_r_2487_;
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___redArg(lean_object* v_inst_2488_, lean_object* v_p_2489_, lean_object* v_xs_2490_){
_start:
{
lean_object* v_toApplicative_2491_; lean_object* v_toPure_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; 
v_toApplicative_2491_ = lean_ctor_get(v_inst_2488_, 0);
v_toPure_2492_ = lean_ctor_get(v_toApplicative_2491_, 1);
v___x_2493_ = lean_unsigned_to_nat(0u);
v___x_2494_ = lean_array_get_size(v_xs_2490_);
v___x_2495_ = lean_nat_dec_lt(v___x_2493_, v___x_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
lean_inc(v_toPure_2492_);
lean_dec_ref(v_xs_2490_);
lean_dec(v_p_2489_);
lean_dec_ref(v_inst_2488_);
v___x_2496_ = lean_box(v___x_2495_);
v___x_2497_ = lean_apply_2(v_toPure_2492_, lean_box(0), v___x_2496_);
return v___x_2497_;
}
else
{
if (v___x_2495_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_inc(v_toPure_2492_);
lean_dec_ref(v_xs_2490_);
lean_dec(v_p_2489_);
lean_dec_ref(v_inst_2488_);
v___x_2498_ = lean_box(v___x_2495_);
v___x_2499_ = lean_apply_2(v_toPure_2492_, lean_box(0), v___x_2498_);
return v___x_2499_;
}
else
{
size_t v___x_2500_; size_t v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = ((size_t)0ULL);
v___x_2501_ = lean_usize_of_nat(v___x_2494_);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2488_, v_p_2489_, v_xs_2490_, v___x_2500_, v___x_2501_);
return v___x_2502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM(lean_object* v_m_2503_, lean_object* v_00_u03b1_2504_, lean_object* v_n_2505_, lean_object* v_inst_2506_, lean_object* v_p_2507_, lean_object* v_xs_2508_){
_start:
{
lean_object* v_toApplicative_2509_; lean_object* v_toPure_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_toApplicative_2509_ = lean_ctor_get(v_inst_2506_, 0);
v_toPure_2510_ = lean_ctor_get(v_toApplicative_2509_, 1);
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = lean_array_get_size(v_xs_2508_);
v___x_2513_ = lean_nat_dec_lt(v___x_2511_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_inc(v_toPure_2510_);
lean_dec_ref(v_xs_2508_);
lean_dec(v_p_2507_);
lean_dec_ref(v_inst_2506_);
v___x_2514_ = lean_box(v___x_2513_);
v___x_2515_ = lean_apply_2(v_toPure_2510_, lean_box(0), v___x_2514_);
return v___x_2515_;
}
else
{
if (v___x_2513_ == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
lean_inc(v_toPure_2510_);
lean_dec_ref(v_xs_2508_);
lean_dec(v_p_2507_);
lean_dec_ref(v_inst_2506_);
v___x_2516_ = lean_box(v___x_2513_);
v___x_2517_ = lean_apply_2(v_toPure_2510_, lean_box(0), v___x_2516_);
return v___x_2517_;
}
else
{
size_t v___x_2518_; size_t v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = ((size_t)0ULL);
v___x_2519_ = lean_usize_of_nat(v___x_2512_);
v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2506_, v_p_2507_, v_xs_2508_, v___x_2518_, v___x_2519_);
return v___x_2520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___boxed(lean_object* v_m_2521_, lean_object* v_00_u03b1_2522_, lean_object* v_n_2523_, lean_object* v_inst_2524_, lean_object* v_p_2525_, lean_object* v_xs_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Vector_anyM(v_m_2521_, v_00_u03b1_2522_, v_n_2523_, v_inst_2524_, v_p_2525_, v_xs_2526_);
lean_dec(v_n_2523_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0(lean_object* v_toPure_2528_, uint8_t v_____do__lift_2529_){
_start:
{
if (v_____do__lift_2529_ == 0)
{
uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = 1;
v___x_2531_ = lean_box(v___x_2530_);
v___x_2532_ = lean_apply_2(v_toPure_2528_, lean_box(0), v___x_2531_);
return v___x_2532_;
}
else
{
uint8_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = 0;
v___x_2534_ = lean_box(v___x_2533_);
v___x_2535_ = lean_apply_2(v_toPure_2528_, lean_box(0), v___x_2534_);
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0___boxed(lean_object* v_toPure_2536_, lean_object* v_____do__lift_2537_){
_start:
{
uint8_t v_____do__lift_112__boxed_2538_; lean_object* v_res_2539_; 
v_____do__lift_112__boxed_2538_ = lean_unbox(v_____do__lift_2537_);
v_res_2539_ = l_Vector_allM___redArg___lam__0(v_toPure_2536_, v_____do__lift_112__boxed_2538_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1(lean_object* v_toPure_2540_, uint8_t v___x_2541_, uint8_t v_____do__lift_2542_){
_start:
{
if (v_____do__lift_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = lean_box(v___x_2541_);
v___x_2544_ = lean_apply_2(v_toPure_2540_, lean_box(0), v___x_2543_);
return v___x_2544_;
}
else
{
uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = 0;
v___x_2546_ = lean_box(v___x_2545_);
v___x_2547_ = lean_apply_2(v_toPure_2540_, lean_box(0), v___x_2546_);
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1___boxed(lean_object* v_toPure_2548_, lean_object* v___x_2549_, lean_object* v_____do__lift_2550_){
_start:
{
uint8_t v___x_127__boxed_2551_; uint8_t v_____do__lift_128__boxed_2552_; lean_object* v_res_2553_; 
v___x_127__boxed_2551_ = lean_unbox(v___x_2549_);
v_____do__lift_128__boxed_2552_ = lean_unbox(v_____do__lift_2550_);
v_res_2553_ = l_Vector_allM___redArg___lam__1(v_toPure_2548_, v___x_127__boxed_2551_, v_____do__lift_128__boxed_2552_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__2(lean_object* v_p_2554_, lean_object* v_toBind_2555_, lean_object* v___f_2556_, lean_object* v_v_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_apply_1(v_p_2554_, v_v_2557_);
v___x_2559_ = lean_apply_4(v_toBind_2555_, lean_box(0), lean_box(0), v___x_2558_, v___f_2556_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg(lean_object* v_inst_2560_, lean_object* v_p_2561_, lean_object* v_xs_2562_){
_start:
{
lean_object* v_toApplicative_2563_; lean_object* v_toBind_2564_; lean_object* v_toPure_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___f_2568_; uint8_t v___x_2569_; 
v_toApplicative_2563_ = lean_ctor_get(v_inst_2560_, 0);
v_toBind_2564_ = lean_ctor_get(v_inst_2560_, 1);
lean_inc(v_toBind_2564_);
v_toPure_2565_ = lean_ctor_get(v_toApplicative_2563_, 1);
v___x_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = lean_array_get_size(v_xs_2562_);
lean_inc(v_toPure_2565_);
v___f_2568_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2568_, 0, v_toPure_2565_);
v___x_2569_ = lean_nat_dec_lt(v___x_2566_, v___x_2567_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_inc(v_toPure_2565_);
lean_dec_ref(v_xs_2562_);
lean_dec(v_p_2561_);
lean_dec_ref(v_inst_2560_);
v___x_2570_ = lean_box(v___x_2569_);
v___x_2571_ = lean_apply_2(v_toPure_2565_, lean_box(0), v___x_2570_);
v___x_2572_ = lean_apply_4(v_toBind_2564_, lean_box(0), lean_box(0), v___x_2571_, v___f_2568_);
return v___x_2572_;
}
else
{
if (v___x_2569_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_inc(v_toPure_2565_);
lean_dec_ref(v_xs_2562_);
lean_dec(v_p_2561_);
lean_dec_ref(v_inst_2560_);
v___x_2573_ = lean_box(v___x_2569_);
v___x_2574_ = lean_apply_2(v_toPure_2565_, lean_box(0), v___x_2573_);
v___x_2575_ = lean_apply_4(v_toBind_2564_, lean_box(0), lean_box(0), v___x_2574_, v___f_2568_);
return v___x_2575_;
}
else
{
lean_object* v___x_2576_; lean_object* v___f_2577_; lean_object* v___f_2578_; size_t v___x_2579_; size_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2576_ = lean_box(v___x_2569_);
lean_inc(v_toPure_2565_);
v___f_2577_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2577_, 0, v_toPure_2565_);
lean_closure_set(v___f_2577_, 1, v___x_2576_);
lean_inc(v_toBind_2564_);
v___f_2578_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2578_, 0, v_p_2561_);
lean_closure_set(v___f_2578_, 1, v_toBind_2564_);
lean_closure_set(v___f_2578_, 2, v___f_2577_);
v___x_2579_ = ((size_t)0ULL);
v___x_2580_ = lean_usize_of_nat(v___x_2567_);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2560_, v___f_2578_, v_xs_2562_, v___x_2579_, v___x_2580_);
v___x_2582_ = lean_apply_4(v_toBind_2564_, lean_box(0), lean_box(0), v___x_2581_, v___f_2568_);
return v___x_2582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM(lean_object* v_m_2583_, lean_object* v_00_u03b1_2584_, lean_object* v_n_2585_, lean_object* v_inst_2586_, lean_object* v_p_2587_, lean_object* v_xs_2588_){
_start:
{
lean_object* v_toApplicative_2589_; lean_object* v_toBind_2590_; lean_object* v_toPure_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___f_2594_; uint8_t v___x_2595_; 
v_toApplicative_2589_ = lean_ctor_get(v_inst_2586_, 0);
v_toBind_2590_ = lean_ctor_get(v_inst_2586_, 1);
lean_inc(v_toBind_2590_);
v_toPure_2591_ = lean_ctor_get(v_toApplicative_2589_, 1);
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = lean_array_get_size(v_xs_2588_);
lean_inc(v_toPure_2591_);
v___f_2594_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2594_, 0, v_toPure_2591_);
v___x_2595_ = lean_nat_dec_lt(v___x_2592_, v___x_2593_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_inc(v_toPure_2591_);
lean_dec_ref(v_xs_2588_);
lean_dec(v_p_2587_);
lean_dec_ref(v_inst_2586_);
v___x_2596_ = lean_box(v___x_2595_);
v___x_2597_ = lean_apply_2(v_toPure_2591_, lean_box(0), v___x_2596_);
v___x_2598_ = lean_apply_4(v_toBind_2590_, lean_box(0), lean_box(0), v___x_2597_, v___f_2594_);
return v___x_2598_;
}
else
{
if (v___x_2595_ == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_inc(v_toPure_2591_);
lean_dec_ref(v_xs_2588_);
lean_dec(v_p_2587_);
lean_dec_ref(v_inst_2586_);
v___x_2599_ = lean_box(v___x_2595_);
v___x_2600_ = lean_apply_2(v_toPure_2591_, lean_box(0), v___x_2599_);
v___x_2601_ = lean_apply_4(v_toBind_2590_, lean_box(0), lean_box(0), v___x_2600_, v___f_2594_);
return v___x_2601_;
}
else
{
lean_object* v___x_2602_; lean_object* v___f_2603_; lean_object* v___f_2604_; size_t v___x_2605_; size_t v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2602_ = lean_box(v___x_2595_);
lean_inc(v_toPure_2591_);
v___f_2603_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2603_, 0, v_toPure_2591_);
lean_closure_set(v___f_2603_, 1, v___x_2602_);
lean_inc(v_toBind_2590_);
v___f_2604_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2604_, 0, v_p_2587_);
lean_closure_set(v___f_2604_, 1, v_toBind_2590_);
lean_closure_set(v___f_2604_, 2, v___f_2603_);
v___x_2605_ = ((size_t)0ULL);
v___x_2606_ = lean_usize_of_nat(v___x_2593_);
v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2586_, v___f_2604_, v_xs_2588_, v___x_2605_, v___x_2606_);
v___x_2608_ = lean_apply_4(v_toBind_2590_, lean_box(0), lean_box(0), v___x_2607_, v___f_2594_);
return v___x_2608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___boxed(lean_object* v_m_2609_, lean_object* v_00_u03b1_2610_, lean_object* v_n_2611_, lean_object* v_inst_2612_, lean_object* v_p_2613_, lean_object* v_xs_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Vector_allM(v_m_2609_, v_00_u03b1_2610_, v_n_2611_, v_inst_2612_, v_p_2613_, v_xs_2614_);
lean_dec(v_n_2611_);
return v_res_2615_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg___lam__0(lean_object* v_p_2616_, lean_object* v_x_2617_){
_start:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = lean_apply_1(v_p_2616_, v_x_2617_);
v___x_2619_ = lean_unbox(v___x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___lam__0___boxed(lean_object* v_p_2620_, lean_object* v_x_2621_){
_start:
{
uint8_t v_res_2622_; lean_object* v_r_2623_; 
v_res_2622_ = l_Vector_any___redArg___lam__0(v_p_2620_, v_x_2621_);
v_r_2623_ = lean_box(v_res_2622_);
return v_r_2623_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg(lean_object* v_xs_2624_, lean_object* v_p_2625_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2626_ = lean_unsigned_to_nat(0u);
v___x_2627_ = lean_array_get_size(v_xs_2624_);
v___x_2628_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2629_ = lean_nat_dec_lt(v___x_2626_, v___x_2627_);
if (v___x_2629_ == 0)
{
lean_dec_ref(v_p_2625_);
lean_dec_ref(v_xs_2624_);
return v___x_2629_;
}
else
{
if (v___x_2629_ == 0)
{
lean_dec_ref(v_p_2625_);
lean_dec_ref(v_xs_2624_);
return v___x_2629_;
}
else
{
lean_object* v___f_2630_; size_t v___x_2631_; size_t v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___f_2630_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2630_, 0, v_p_2625_);
v___x_2631_ = ((size_t)0ULL);
v___x_2632_ = lean_usize_of_nat(v___x_2627_);
v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2628_, v___f_2630_, v_xs_2624_, v___x_2631_, v___x_2632_);
v___x_2634_ = lean_unbox(v___x_2633_);
lean_dec(v___x_2633_);
return v___x_2634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___boxed(lean_object* v_xs_2635_, lean_object* v_p_2636_){
_start:
{
uint8_t v_res_2637_; lean_object* v_r_2638_; 
v_res_2637_ = l_Vector_any___redArg(v_xs_2635_, v_p_2636_);
v_r_2638_ = lean_box(v_res_2637_);
return v_r_2638_;
}
}
LEAN_EXPORT uint8_t l_Vector_any(lean_object* v_00_u03b1_2639_, lean_object* v_n_2640_, lean_object* v_xs_2641_, lean_object* v_p_2642_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_array_get_size(v_xs_2641_);
v___x_2645_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2646_ = lean_nat_dec_lt(v___x_2643_, v___x_2644_);
if (v___x_2646_ == 0)
{
lean_dec_ref(v_p_2642_);
lean_dec_ref(v_xs_2641_);
return v___x_2646_;
}
else
{
if (v___x_2646_ == 0)
{
lean_dec_ref(v_p_2642_);
lean_dec_ref(v_xs_2641_);
return v___x_2646_;
}
else
{
lean_object* v___f_2647_; size_t v___x_2648_; size_t v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___f_2647_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2647_, 0, v_p_2642_);
v___x_2648_ = ((size_t)0ULL);
v___x_2649_ = lean_usize_of_nat(v___x_2644_);
v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2645_, v___f_2647_, v_xs_2641_, v___x_2648_, v___x_2649_);
v___x_2651_ = lean_unbox(v___x_2650_);
lean_dec(v___x_2650_);
return v___x_2651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___boxed(lean_object* v_00_u03b1_2652_, lean_object* v_n_2653_, lean_object* v_xs_2654_, lean_object* v_p_2655_){
_start:
{
uint8_t v_res_2656_; lean_object* v_r_2657_; 
v_res_2656_ = l_Vector_any(v_00_u03b1_2652_, v_n_2653_, v_xs_2654_, v_p_2655_);
lean_dec(v_n_2653_);
v_r_2657_ = lean_box(v_res_2656_);
return v_r_2657_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg___lam__0(lean_object* v_p_2658_, uint8_t v___x_2659_, lean_object* v_v_2660_){
_start:
{
lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = lean_apply_1(v_p_2658_, v_v_2660_);
v___x_2662_ = lean_unbox(v___x_2661_);
if (v___x_2662_ == 0)
{
return v___x_2659_;
}
else
{
uint8_t v___x_2663_; 
v___x_2663_ = 0;
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___lam__0___boxed(lean_object* v_p_2664_, lean_object* v___x_2665_, lean_object* v_v_2666_){
_start:
{
uint8_t v___x_75__boxed_2667_; uint8_t v_res_2668_; lean_object* v_r_2669_; 
v___x_75__boxed_2667_ = lean_unbox(v___x_2665_);
v_res_2668_ = l_Vector_all___redArg___lam__0(v_p_2664_, v___x_75__boxed_2667_, v_v_2666_);
v_r_2669_ = lean_box(v_res_2668_);
return v_r_2669_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg(lean_object* v_xs_2670_, lean_object* v_p_2671_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = lean_array_get_size(v_xs_2670_);
v___x_2674_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2675_ = lean_nat_dec_lt(v___x_2672_, v___x_2673_);
if (v___x_2675_ == 0)
{
uint8_t v___x_2676_; 
lean_dec_ref(v_p_2671_);
lean_dec_ref(v_xs_2670_);
v___x_2676_ = 1;
return v___x_2676_;
}
else
{
if (v___x_2675_ == 0)
{
lean_dec_ref(v_p_2671_);
lean_dec_ref(v_xs_2670_);
return v___x_2675_;
}
else
{
lean_object* v___x_2677_; lean_object* v___f_2678_; size_t v___x_2679_; size_t v___x_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2677_ = lean_box(v___x_2675_);
v___f_2678_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2678_, 0, v_p_2671_);
lean_closure_set(v___f_2678_, 1, v___x_2677_);
v___x_2679_ = ((size_t)0ULL);
v___x_2680_ = lean_usize_of_nat(v___x_2673_);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2674_, v___f_2678_, v_xs_2670_, v___x_2679_, v___x_2680_);
v___x_2682_ = lean_unbox(v___x_2681_);
lean_dec(v___x_2681_);
if (v___x_2682_ == 0)
{
return v___x_2675_;
}
else
{
uint8_t v___x_2683_; 
v___x_2683_ = 0;
return v___x_2683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___boxed(lean_object* v_xs_2684_, lean_object* v_p_2685_){
_start:
{
uint8_t v_res_2686_; lean_object* v_r_2687_; 
v_res_2686_ = l_Vector_all___redArg(v_xs_2684_, v_p_2685_);
v_r_2687_ = lean_box(v_res_2686_);
return v_r_2687_;
}
}
LEAN_EXPORT uint8_t l_Vector_all(lean_object* v_00_u03b1_2688_, lean_object* v_n_2689_, lean_object* v_xs_2690_, lean_object* v_p_2691_){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = lean_array_get_size(v_xs_2690_);
v___x_2694_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2695_ = lean_nat_dec_lt(v___x_2692_, v___x_2693_);
if (v___x_2695_ == 0)
{
uint8_t v___x_2696_; 
lean_dec_ref(v_p_2691_);
lean_dec_ref(v_xs_2690_);
v___x_2696_ = 1;
return v___x_2696_;
}
else
{
if (v___x_2695_ == 0)
{
lean_dec_ref(v_p_2691_);
lean_dec_ref(v_xs_2690_);
return v___x_2695_;
}
else
{
lean_object* v___x_2697_; lean_object* v___f_2698_; size_t v___x_2699_; size_t v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2697_ = lean_box(v___x_2695_);
v___f_2698_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2698_, 0, v_p_2691_);
lean_closure_set(v___f_2698_, 1, v___x_2697_);
v___x_2699_ = ((size_t)0ULL);
v___x_2700_ = lean_usize_of_nat(v___x_2693_);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2694_, v___f_2698_, v_xs_2690_, v___x_2699_, v___x_2700_);
v___x_2702_ = lean_unbox(v___x_2701_);
lean_dec(v___x_2701_);
if (v___x_2702_ == 0)
{
return v___x_2695_;
}
else
{
uint8_t v___x_2703_; 
v___x_2703_ = 0;
return v___x_2703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___boxed(lean_object* v_00_u03b1_2704_, lean_object* v_n_2705_, lean_object* v_xs_2706_, lean_object* v_p_2707_){
_start:
{
uint8_t v_res_2708_; lean_object* v_r_2709_; 
v_res_2708_ = l_Vector_all(v_00_u03b1_2704_, v_n_2705_, v_xs_2706_, v_p_2707_);
lean_dec(v_n_2705_);
v_r_2709_ = lean_box(v_res_2708_);
return v_r_2709_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0(lean_object* v_p_2710_, lean_object* v_x1_2711_, lean_object* v_x2_2712_){
_start:
{
lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2713_ = lean_apply_1(v_p_2710_, v_x1_2711_);
v___x_2714_ = lean_unbox(v___x_2713_);
if (v___x_2714_ == 0)
{
lean_inc(v_x2_2712_);
return v_x2_2712_;
}
else
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = lean_unsigned_to_nat(1u);
v___x_2716_ = lean_nat_add(v_x2_2712_, v___x_2715_);
return v___x_2716_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0___boxed(lean_object* v_p_2717_, lean_object* v_x1_2718_, lean_object* v_x2_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Vector_countP___redArg___lam__0(v_p_2717_, v_x1_2718_, v_x2_2719_);
lean_dec(v_x2_2719_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg(lean_object* v_p_2721_, lean_object* v_xs_2722_){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2723_ = lean_unsigned_to_nat(0u);
v___x_2724_ = lean_array_get_size(v_xs_2722_);
v___x_2725_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2726_ = lean_nat_dec_lt(v___x_2723_, v___x_2724_);
if (v___x_2726_ == 0)
{
lean_dec_ref(v_xs_2722_);
lean_dec_ref(v_p_2721_);
return v___x_2723_;
}
else
{
lean_object* v___f_2727_; size_t v___x_2728_; size_t v___x_2729_; lean_object* v___x_2730_; 
v___f_2727_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2727_, 0, v_p_2721_);
v___x_2728_ = lean_usize_of_nat(v___x_2724_);
v___x_2729_ = ((size_t)0ULL);
v___x_2730_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2725_, v___f_2727_, v_xs_2722_, v___x_2728_, v___x_2729_, v___x_2723_);
return v___x_2730_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP(lean_object* v_00_u03b1_2731_, lean_object* v_n_2732_, lean_object* v_p_2733_, lean_object* v_xs_2734_){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2735_ = lean_unsigned_to_nat(0u);
v___x_2736_ = lean_array_get_size(v_xs_2734_);
v___x_2737_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2738_ = lean_nat_dec_lt(v___x_2735_, v___x_2736_);
if (v___x_2738_ == 0)
{
lean_dec_ref(v_xs_2734_);
lean_dec_ref(v_p_2733_);
return v___x_2735_;
}
else
{
lean_object* v___f_2739_; size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v___f_2739_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2739_, 0, v_p_2733_);
v___x_2740_ = lean_usize_of_nat(v___x_2736_);
v___x_2741_ = ((size_t)0ULL);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2737_, v___f_2739_, v_xs_2734_, v___x_2740_, v___x_2741_, v___x_2735_);
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___boxed(lean_object* v_00_u03b1_2743_, lean_object* v_n_2744_, lean_object* v_p_2745_, lean_object* v_xs_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Vector_countP(v_00_u03b1_2743_, v_n_2744_, v_p_2745_, v_xs_2746_);
lean_dec(v_n_2744_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0(lean_object* v_inst_2748_, lean_object* v_a_2749_, lean_object* v_x1_2750_, lean_object* v_x2_2751_){
_start:
{
lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2752_ = lean_apply_2(v_inst_2748_, v_x1_2750_, v_a_2749_);
v___x_2753_ = lean_unbox(v___x_2752_);
if (v___x_2753_ == 0)
{
lean_inc(v_x2_2751_);
return v_x2_2751_;
}
else
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = lean_unsigned_to_nat(1u);
v___x_2755_ = lean_nat_add(v_x2_2751_, v___x_2754_);
return v___x_2755_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0___boxed(lean_object* v_inst_2756_, lean_object* v_a_2757_, lean_object* v_x1_2758_, lean_object* v_x2_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Vector_count___redArg___lam__0(v_inst_2756_, v_a_2757_, v_x1_2758_, v_x2_2759_);
lean_dec(v_x2_2759_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg(lean_object* v_inst_2761_, lean_object* v_a_2762_, lean_object* v_xs_2763_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = lean_array_get_size(v_xs_2763_);
v___x_2766_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2767_ = lean_nat_dec_lt(v___x_2764_, v___x_2765_);
if (v___x_2767_ == 0)
{
lean_dec_ref(v_xs_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_inst_2761_);
return v___x_2764_;
}
else
{
lean_object* v___f_2768_; size_t v___x_2769_; size_t v___x_2770_; lean_object* v___x_2771_; 
v___f_2768_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2768_, 0, v_inst_2761_);
lean_closure_set(v___f_2768_, 1, v_a_2762_);
v___x_2769_ = lean_usize_of_nat(v___x_2765_);
v___x_2770_ = ((size_t)0ULL);
v___x_2771_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2766_, v___f_2768_, v_xs_2763_, v___x_2769_, v___x_2770_, v___x_2764_);
return v___x_2771_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count(lean_object* v_00_u03b1_2772_, lean_object* v_n_2773_, lean_object* v_inst_2774_, lean_object* v_a_2775_, lean_object* v_xs_2776_){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2777_ = lean_unsigned_to_nat(0u);
v___x_2778_ = lean_array_get_size(v_xs_2776_);
v___x_2779_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2780_ = lean_nat_dec_lt(v___x_2777_, v___x_2778_);
if (v___x_2780_ == 0)
{
lean_dec_ref(v_xs_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_inst_2774_);
return v___x_2777_;
}
else
{
lean_object* v___f_2781_; size_t v___x_2782_; size_t v___x_2783_; lean_object* v___x_2784_; 
v___f_2781_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2781_, 0, v_inst_2774_);
lean_closure_set(v___f_2781_, 1, v_a_2775_);
v___x_2782_ = lean_usize_of_nat(v___x_2778_);
v___x_2783_ = ((size_t)0ULL);
v___x_2784_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2779_, v___f_2781_, v_xs_2776_, v___x_2782_, v___x_2783_, v___x_2777_);
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___boxed(lean_object* v_00_u03b1_2785_, lean_object* v_n_2786_, lean_object* v_inst_2787_, lean_object* v_a_2788_, lean_object* v_xs_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Vector_count(v_00_u03b1_2785_, v_n_2786_, v_inst_2787_, v_a_2788_, v_xs_2789_);
lean_dec(v_n_2786_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___redArg(lean_object* v_inst_2791_, lean_object* v_xs_2792_, lean_object* v_a_2793_, lean_object* v_b_2794_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Array_replace___redArg(v_inst_2791_, v_xs_2792_, v_a_2793_, v_b_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace(lean_object* v_00_u03b1_2796_, lean_object* v_n_2797_, lean_object* v_inst_2798_, lean_object* v_xs_2799_, lean_object* v_a_2800_, lean_object* v_b_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Array_replace___redArg(v_inst_2798_, v_xs_2799_, v_a_2800_, v_b_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___boxed(lean_object* v_00_u03b1_2803_, lean_object* v_n_2804_, lean_object* v_inst_2805_, lean_object* v_xs_2806_, lean_object* v_a_2807_, lean_object* v_b_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Vector_replace(v_00_u03b1_2803_, v_n_2804_, v_inst_2805_, v_xs_2806_, v_a_2807_, v_b_2808_);
lean_dec(v_n_2804_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg___lam__0(lean_object* v_inst_2810_, lean_object* v_x1_2811_, lean_object* v_x2_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_apply_2(v_inst_2810_, v_x1_2811_, v_x2_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg(lean_object* v_inst_2814_, lean_object* v_inst_2815_, lean_object* v_xs_2816_){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; 
v___x_2817_ = lean_array_get_size(v_xs_2816_);
v___x_2818_ = lean_unsigned_to_nat(0u);
v___x_2819_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2820_ = lean_nat_dec_lt(v___x_2818_, v___x_2817_);
if (v___x_2820_ == 0)
{
lean_dec_ref(v_xs_2816_);
lean_dec(v_inst_2814_);
return v_inst_2815_;
}
else
{
lean_object* v___f_2821_; size_t v___x_2822_; size_t v___x_2823_; lean_object* v___x_2824_; 
v___f_2821_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2821_, 0, v_inst_2814_);
v___x_2822_ = lean_usize_of_nat(v___x_2817_);
v___x_2823_ = ((size_t)0ULL);
v___x_2824_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2819_, v___f_2821_, v_xs_2816_, v___x_2822_, v___x_2823_, v_inst_2815_);
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum(lean_object* v_00_u03b1_2825_, lean_object* v_n_2826_, lean_object* v_inst_2827_, lean_object* v_inst_2828_, lean_object* v_xs_2829_){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2830_ = lean_array_get_size(v_xs_2829_);
v___x_2831_ = lean_unsigned_to_nat(0u);
v___x_2832_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2833_ = lean_nat_dec_lt(v___x_2831_, v___x_2830_);
if (v___x_2833_ == 0)
{
lean_dec_ref(v_xs_2829_);
lean_dec(v_inst_2827_);
return v_inst_2828_;
}
else
{
lean_object* v___f_2834_; size_t v___x_2835_; size_t v___x_2836_; lean_object* v___x_2837_; 
v___f_2834_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2834_, 0, v_inst_2827_);
v___x_2835_ = lean_usize_of_nat(v___x_2830_);
v___x_2836_ = ((size_t)0ULL);
v___x_2837_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2832_, v___f_2834_, v_xs_2829_, v___x_2835_, v___x_2836_, v_inst_2828_);
return v___x_2837_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum___boxed(lean_object* v_00_u03b1_2838_, lean_object* v_n_2839_, lean_object* v_inst_2840_, lean_object* v_inst_2841_, lean_object* v_xs_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Vector_sum(v_00_u03b1_2838_, v_n_2839_, v_inst_2840_, v_inst_2841_, v_xs_2842_);
lean_dec(v_n_2839_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Vector_prod___redArg(lean_object* v_inst_2844_, lean_object* v_inst_2845_, lean_object* v_xs_2846_){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2847_ = lean_array_get_size(v_xs_2846_);
v___x_2848_ = lean_unsigned_to_nat(0u);
v___x_2849_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2850_ = lean_nat_dec_lt(v___x_2848_, v___x_2847_);
if (v___x_2850_ == 0)
{
lean_dec_ref(v_xs_2846_);
lean_dec(v_inst_2844_);
return v_inst_2845_;
}
else
{
lean_object* v___f_2851_; size_t v___x_2852_; size_t v___x_2853_; lean_object* v___x_2854_; 
v___f_2851_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2851_, 0, v_inst_2844_);
v___x_2852_ = lean_usize_of_nat(v___x_2847_);
v___x_2853_ = ((size_t)0ULL);
v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2849_, v___f_2851_, v_xs_2846_, v___x_2852_, v___x_2853_, v_inst_2845_);
return v___x_2854_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod(lean_object* v_00_u03b1_2855_, lean_object* v_n_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_xs_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2860_ = lean_array_get_size(v_xs_2859_);
v___x_2861_ = lean_unsigned_to_nat(0u);
v___x_2862_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2863_ = lean_nat_dec_lt(v___x_2861_, v___x_2860_);
if (v___x_2863_ == 0)
{
lean_dec_ref(v_xs_2859_);
lean_dec(v_inst_2857_);
return v_inst_2858_;
}
else
{
lean_object* v___f_2864_; size_t v___x_2865_; size_t v___x_2866_; lean_object* v___x_2867_; 
v___f_2864_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2864_, 0, v_inst_2857_);
v___x_2865_ = lean_usize_of_nat(v___x_2860_);
v___x_2866_ = ((size_t)0ULL);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2862_, v___f_2864_, v_xs_2859_, v___x_2865_, v___x_2866_, v_inst_2858_);
return v___x_2867_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod___boxed(lean_object* v_00_u03b1_2868_, lean_object* v_n_2869_, lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_xs_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Vector_prod(v_00_u03b1_2868_, v_n_2869_, v_inst_2870_, v_inst_2871_, v_xs_2872_);
lean_dec(v_n_2869_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg(lean_object* v_m_2874_, lean_object* v_n_2875_, lean_object* v_a_2876_, lean_object* v_xs_2877_){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_nat_sub(v_n_2875_, v_m_2874_);
v___x_2879_ = lean_mk_array(v___x_2878_, v_a_2876_);
v___x_2880_ = l_Array_append___redArg(v___x_2879_, v_xs_2877_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg___boxed(lean_object* v_m_2881_, lean_object* v_n_2882_, lean_object* v_a_2883_, lean_object* v_xs_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Vector_leftpad___redArg(v_m_2881_, v_n_2882_, v_a_2883_, v_xs_2884_);
lean_dec_ref(v_xs_2884_);
lean_dec(v_n_2882_);
lean_dec(v_m_2881_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad(lean_object* v_00_u03b1_2886_, lean_object* v_m_2887_, lean_object* v_n_2888_, lean_object* v_a_2889_, lean_object* v_xs_2890_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = lean_nat_sub(v_n_2888_, v_m_2887_);
v___x_2892_ = lean_mk_array(v___x_2891_, v_a_2889_);
v___x_2893_ = l_Array_append___redArg(v___x_2892_, v_xs_2890_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___boxed(lean_object* v_00_u03b1_2894_, lean_object* v_m_2895_, lean_object* v_n_2896_, lean_object* v_a_2897_, lean_object* v_xs_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Vector_leftpad(v_00_u03b1_2894_, v_m_2895_, v_n_2896_, v_a_2897_, v_xs_2898_);
lean_dec_ref(v_xs_2898_);
lean_dec(v_n_2896_);
lean_dec(v_m_2895_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg(lean_object* v_m_2900_, lean_object* v_n_2901_, lean_object* v_a_2902_, lean_object* v_xs_2903_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2904_ = lean_nat_sub(v_n_2901_, v_m_2900_);
v___x_2905_ = lean_mk_array(v___x_2904_, v_a_2902_);
v___x_2906_ = l_Array_append___redArg(v_xs_2903_, v___x_2905_);
lean_dec_ref(v___x_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg___boxed(lean_object* v_m_2907_, lean_object* v_n_2908_, lean_object* v_a_2909_, lean_object* v_xs_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Vector_rightpad___redArg(v_m_2907_, v_n_2908_, v_a_2909_, v_xs_2910_);
lean_dec(v_n_2908_);
lean_dec(v_m_2907_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad(lean_object* v_00_u03b1_2912_, lean_object* v_m_2913_, lean_object* v_n_2914_, lean_object* v_a_2915_, lean_object* v_xs_2916_){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2917_ = lean_nat_sub(v_n_2914_, v_m_2913_);
v___x_2918_ = lean_mk_array(v___x_2917_, v_a_2915_);
v___x_2919_ = l_Array_append___redArg(v_xs_2916_, v___x_2918_);
lean_dec_ref(v___x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___boxed(lean_object* v_00_u03b1_2920_, lean_object* v_m_2921_, lean_object* v_n_2922_, lean_object* v_a_2923_, lean_object* v_xs_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Vector_rightpad(v_00_u03b1_2920_, v_m_2921_, v_n_2922_, v_a_2923_, v_xs_2924_);
lean_dec(v_n_2922_);
lean_dec(v_m_2921_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_f_2926_, lean_object* v_a_2927_, lean_object* v_h_2928_, lean_object* v_b_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_apply_3(v_f_2926_, v_a_2927_, lean_box(0), v_b_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_inst_2931_, lean_object* v_00_u03b2_2932_, lean_object* v_xs_2933_, lean_object* v_b_2934_, lean_object* v_f_2935_){
_start:
{
lean_object* v___f_2936_; size_t v_sz_2937_; size_t v___x_2938_; lean_object* v___x_2939_; 
v___f_2936_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2936_, 0, v_f_2935_);
v_sz_2937_ = lean_array_size(v_xs_2933_);
v___x_2938_ = ((size_t)0ULL);
v___x_2939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2931_, v_xs_2933_, v___f_2936_, v_sz_2937_, v___x_2938_, v_b_2934_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_2940_){
_start:
{
lean_object* v___f_2941_; 
v___f_2941_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2941_, 0, v_inst_2940_);
return v___f_2941_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_2942_, lean_object* v_00_u03b1_2943_, lean_object* v_n_2944_, lean_object* v_inst_2945_){
_start:
{
lean_object* v___f_2946_; 
v___f_2946_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2946_, 0, v_inst_2945_);
return v___f_2946_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(lean_object* v_m_2947_, lean_object* v_00_u03b1_2948_, lean_object* v_n_2949_, lean_object* v_inst_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Vector_instForIn_x27InferInstanceMembershipOfMonad(v_m_2947_, v_00_u03b1_2948_, v_n_2949_, v_inst_2950_);
lean_dec(v_n_2949_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad___redArg(lean_object* v_n_2952_, lean_object* v_inst_2953_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2954_, 0, lean_box(0));
lean_closure_set(v___x_2954_, 1, lean_box(0));
lean_closure_set(v___x_2954_, 2, v_n_2952_);
lean_closure_set(v___x_2954_, 3, v_inst_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad(lean_object* v_m_2955_, lean_object* v_00_u03b1_2956_, lean_object* v_n_2957_, lean_object* v_inst_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2959_, 0, lean_box(0));
lean_closure_set(v___x_2959_, 1, lean_box(0));
lean_closure_set(v___x_2959_, 2, v_n_2957_);
lean_closure_set(v___x_2959_, 3, v_inst_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object* v_00_u03b1_2960_, lean_object* v_n_2961_, lean_object* v_inst_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_box(0);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object* v_00_u03b1_2964_, lean_object* v_n_2965_, lean_object* v_inst_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Vector_instLT(v_00_u03b1_2964_, v_n_2965_, v_inst_2966_);
lean_dec(v_n_2965_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE(lean_object* v_00_u03b1_2968_, lean_object* v_n_2969_, lean_object* v_inst_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_box(0);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___boxed(lean_object* v_00_u03b1_2972_, lean_object* v_n_2973_, lean_object* v_inst_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Vector_instLE(v_00_u03b1_2972_, v_n_2973_, v_inst_2974_);
lean_dec(v_n_2973_);
return v_res_2975_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__2(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = ((lean_object*)(l_Vector_lex___auto__1___closed__0));
v___x_2983_ = l_Lean_mkAtom(v___x_2982_);
return v___x_2983_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__3(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_obj_once(&l_Vector_lex___auto__1___closed__2, &l_Vector_lex___auto__1___closed__2_once, _init_l_Vector_lex___auto__1___closed__2);
v___x_2985_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_2986_ = lean_array_push(v___x_2985_, v___x_2984_);
return v___x_2986_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_3000_ = l_Lean_mkAtom(v___x_2999_);
return v___x_3000_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3001_ = lean_obj_once(&l_Vector_lex___auto__1___closed__8, &l_Vector_lex___auto__1___closed__8_once, _init_l_Vector_lex___auto__1___closed__8);
v___x_3002_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3003_ = lean_array_push(v___x_3002_, v___x_3001_);
return v___x_3003_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_3009_ = lean_string_utf8_byte_size(v___x_3008_);
return v___x_3009_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3010_ = lean_obj_once(&l_Vector_lex___auto__1___closed__13, &l_Vector_lex___auto__1___closed__13_once, _init_l_Vector_lex___auto__1___closed__13);
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_3013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v___x_3011_);
lean_ctor_set(v___x_3013_, 2, v___x_3010_);
return v___x_3013_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3014_ = lean_box(0);
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_obj_once(&l_Vector_lex___auto__1___closed__14, &l_Vector_lex___auto__1___closed__14_once, _init_l_Vector_lex___auto__1___closed__14);
v___x_3017_ = lean_box(2);
v___x_3018_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___x_3016_);
lean_ctor_set(v___x_3018_, 2, v___x_3015_);
lean_ctor_set(v___x_3018_, 3, v___x_3014_);
return v___x_3018_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3019_ = lean_obj_once(&l_Vector_lex___auto__1___closed__15, &l_Vector_lex___auto__1___closed__15_once, _init_l_Vector_lex___auto__1___closed__15);
v___x_3020_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3021_ = lean_array_push(v___x_3020_, v___x_3019_);
return v___x_3021_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3022_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_3023_ = ((lean_object*)(l_Vector_lex___auto__1___closed__11));
v___x_3024_ = lean_box(2);
v___x_3025_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v___x_3023_);
lean_ctor_set(v___x_3025_, 2, v___x_3022_);
return v___x_3025_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3027_ = lean_obj_once(&l_Vector_lex___auto__1___closed__9, &l_Vector_lex___auto__1___closed__9_once, _init_l_Vector_lex___auto__1___closed__9);
v___x_3028_ = lean_array_push(v___x_3027_, v___x_3026_);
return v___x_3028_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3029_ = lean_obj_once(&l_Vector_lex___auto__1___closed__18, &l_Vector_lex___auto__1___closed__18_once, _init_l_Vector_lex___auto__1___closed__18);
v___x_3030_ = ((lean_object*)(l_Vector_lex___auto__1___closed__7));
v___x_3031_ = lean_box(2);
v___x_3032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
lean_ctor_set(v___x_3032_, 1, v___x_3030_);
lean_ctor_set(v___x_3032_, 2, v___x_3029_);
return v___x_3032_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = lean_obj_once(&l_Vector_lex___auto__1___closed__19, &l_Vector_lex___auto__1___closed__19_once, _init_l_Vector_lex___auto__1___closed__19);
v___x_3034_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3035_ = lean_array_push(v___x_3034_, v___x_3033_);
return v___x_3035_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = ((lean_object*)(l_Vector_lex___auto__1___closed__25));
v___x_3047_ = l_Lean_mkAtom(v___x_3046_);
return v___x_3047_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = lean_obj_once(&l_Vector_lex___auto__1___closed__26, &l_Vector_lex___auto__1___closed__26_once, _init_l_Vector_lex___auto__1___closed__26);
v___x_3049_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3050_ = lean_array_push(v___x_3049_, v___x_3048_);
return v___x_3050_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3052_ = lean_obj_once(&l_Vector_lex___auto__1___closed__27, &l_Vector_lex___auto__1___closed__27_once, _init_l_Vector_lex___auto__1___closed__27);
v___x_3053_ = lean_array_push(v___x_3052_, v___x_3051_);
return v___x_3053_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3054_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3055_ = ((lean_object*)(l_Vector_lex___auto__1___closed__24));
v___x_3056_ = lean_box(2);
v___x_3057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
lean_ctor_set(v___x_3057_, 1, v___x_3055_);
lean_ctor_set(v___x_3057_, 2, v___x_3054_);
return v___x_3057_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3059_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3060_ = lean_array_push(v___x_3059_, v___x_3058_);
return v___x_3060_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = ((lean_object*)(l_Vector_lex___auto__1___closed__31));
v___x_3063_ = l_Lean_mkAtom(v___x_3062_);
return v___x_3063_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__33(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = lean_obj_once(&l_Vector_lex___auto__1___closed__32, &l_Vector_lex___auto__1___closed__32_once, _init_l_Vector_lex___auto__1___closed__32);
v___x_3065_ = lean_obj_once(&l_Vector_lex___auto__1___closed__30, &l_Vector_lex___auto__1___closed__30_once, _init_l_Vector_lex___auto__1___closed__30);
v___x_3066_ = lean_array_push(v___x_3065_, v___x_3064_);
return v___x_3066_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__34(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3067_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3068_ = lean_obj_once(&l_Vector_lex___auto__1___closed__33, &l_Vector_lex___auto__1___closed__33_once, _init_l_Vector_lex___auto__1___closed__33);
v___x_3069_ = lean_array_push(v___x_3068_, v___x_3067_);
return v___x_3069_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__35(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3070_ = lean_obj_once(&l_Vector_lex___auto__1___closed__34, &l_Vector_lex___auto__1___closed__34_once, _init_l_Vector_lex___auto__1___closed__34);
v___x_3071_ = ((lean_object*)(l_Vector_lex___auto__1___closed__22));
v___x_3072_ = lean_box(2);
v___x_3073_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3071_);
lean_ctor_set(v___x_3073_, 2, v___x_3070_);
return v___x_3073_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__36(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = lean_obj_once(&l_Vector_lex___auto__1___closed__35, &l_Vector_lex___auto__1___closed__35_once, _init_l_Vector_lex___auto__1___closed__35);
v___x_3075_ = lean_obj_once(&l_Vector_lex___auto__1___closed__20, &l_Vector_lex___auto__1___closed__20_once, _init_l_Vector_lex___auto__1___closed__20);
v___x_3076_ = lean_array_push(v___x_3075_, v___x_3074_);
return v___x_3076_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_3078_ = l_Lean_mkAtom(v___x_3077_);
return v___x_3078_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = lean_obj_once(&l_Vector_lex___auto__1___closed__37, &l_Vector_lex___auto__1___closed__37_once, _init_l_Vector_lex___auto__1___closed__37);
v___x_3080_ = lean_obj_once(&l_Vector_lex___auto__1___closed__36, &l_Vector_lex___auto__1___closed__36_once, _init_l_Vector_lex___auto__1___closed__36);
v___x_3081_ = lean_array_push(v___x_3080_, v___x_3079_);
return v___x_3081_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3082_ = lean_obj_once(&l_Vector_lex___auto__1___closed__38, &l_Vector_lex___auto__1___closed__38_once, _init_l_Vector_lex___auto__1___closed__38);
v___x_3083_ = ((lean_object*)(l_Vector_lex___auto__1___closed__5));
v___x_3084_ = lean_box(2);
v___x_3085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set(v___x_3085_, 1, v___x_3083_);
lean_ctor_set(v___x_3085_, 2, v___x_3082_);
return v___x_3085_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_obj_once(&l_Vector_lex___auto__1___closed__39, &l_Vector_lex___auto__1___closed__39_once, _init_l_Vector_lex___auto__1___closed__39);
v___x_3087_ = lean_obj_once(&l_Vector_lex___auto__1___closed__3, &l_Vector_lex___auto__1___closed__3_once, _init_l_Vector_lex___auto__1___closed__3);
v___x_3088_ = lean_array_push(v___x_3087_, v___x_3086_);
return v___x_3088_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3089_ = lean_obj_once(&l_Vector_lex___auto__1___closed__40, &l_Vector_lex___auto__1___closed__40_once, _init_l_Vector_lex___auto__1___closed__40);
v___x_3090_ = ((lean_object*)(l_Vector_lex___auto__1___closed__1));
v___x_3091_ = lean_box(2);
v___x_3092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v___x_3090_);
lean_ctor_set(v___x_3092_, 2, v___x_3089_);
return v___x_3092_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = lean_obj_once(&l_Vector_lex___auto__1___closed__41, &l_Vector_lex___auto__1___closed__41_once, _init_l_Vector_lex___auto__1___closed__41);
v___x_3094_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3095_ = lean_array_push(v___x_3094_, v___x_3093_);
return v___x_3095_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3096_ = lean_obj_once(&l_Vector_lex___auto__1___closed__42, &l_Vector_lex___auto__1___closed__42_once, _init_l_Vector_lex___auto__1___closed__42);
v___x_3097_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_3098_ = lean_box(2);
v___x_3099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
lean_ctor_set(v___x_3099_, 1, v___x_3097_);
lean_ctor_set(v___x_3099_, 2, v___x_3096_);
return v___x_3099_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = lean_obj_once(&l_Vector_lex___auto__1___closed__43, &l_Vector_lex___auto__1___closed__43_once, _init_l_Vector_lex___auto__1___closed__43);
v___x_3101_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3102_ = lean_array_push(v___x_3101_, v___x_3100_);
return v___x_3102_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3103_ = lean_obj_once(&l_Vector_lex___auto__1___closed__44, &l_Vector_lex___auto__1___closed__44_once, _init_l_Vector_lex___auto__1___closed__44);
v___x_3104_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_3105_ = lean_box(2);
v___x_3106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set(v___x_3106_, 1, v___x_3104_);
lean_ctor_set(v___x_3106_, 2, v___x_3103_);
return v___x_3106_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = lean_obj_once(&l_Vector_lex___auto__1___closed__45, &l_Vector_lex___auto__1___closed__45_once, _init_l_Vector_lex___auto__1___closed__45);
v___x_3108_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3109_ = lean_array_push(v___x_3108_, v___x_3107_);
return v___x_3109_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3110_ = lean_obj_once(&l_Vector_lex___auto__1___closed__46, &l_Vector_lex___auto__1___closed__46_once, _init_l_Vector_lex___auto__1___closed__46);
v___x_3111_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_3112_ = lean_box(2);
v___x_3113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
lean_ctor_set(v___x_3113_, 1, v___x_3111_);
lean_ctor_set(v___x_3113_, 2, v___x_3110_);
return v___x_3113_;
}
}
static lean_object* _init_l_Vector_lex___auto__1(void){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = lean_obj_once(&l_Vector_lex___auto__1___closed__47, &l_Vector_lex___auto__1___closed__47_once, _init_l_Vector_lex___auto__1___closed__47);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0(lean_object* v_n_3115_, lean_object* v_xs_3116_, lean_object* v_ys_3117_, lean_object* v_lt_3118_, lean_object* v_inst_3119_, lean_object* v___x_3120_, lean_object* v___x_3121_, lean_object* v_next_3122_, lean_object* v_acc_3123_, lean_object* v_h_3124_, lean_object* v_G_3125_){
_start:
{
uint8_t v___x_3126_; 
v___x_3126_ = lean_nat_dec_lt(v_next_3122_, v_n_3115_);
if (v___x_3126_ == 0)
{
lean_dec_ref(v_G_3125_);
lean_dec_ref(v___x_3121_);
lean_dec_ref(v_inst_3119_);
lean_dec_ref(v_lt_3118_);
lean_inc_ref(v_acc_3123_);
return v_acc_3123_;
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v___x_3127_ = lean_array_fget_borrowed(v_xs_3116_, v_next_3122_);
v___x_3128_ = lean_array_fget_borrowed(v_ys_3117_, v_next_3122_);
lean_inc(v___x_3128_);
lean_inc(v___x_3127_);
v___x_3129_ = lean_apply_2(v_lt_3118_, v___x_3127_, v___x_3128_);
v___x_3130_ = lean_unbox(v___x_3129_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; uint8_t v___x_3132_; 
lean_inc(v___x_3128_);
lean_inc(v___x_3127_);
v___x_3131_ = lean_apply_2(v_inst_3119_, v___x_3127_, v___x_3128_);
v___x_3132_ = lean_unbox(v___x_3131_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_dec_ref(v_G_3125_);
lean_dec_ref(v___x_3121_);
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3129_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
lean_ctor_set(v___x_3134_, 1, v___x_3120_);
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_unsigned_to_nat(1u);
v___x_3136_ = lean_nat_add(v_next_3122_, v___x_3135_);
v___x_3137_ = lean_apply_4(v_G_3125_, v___x_3136_, v___x_3121_, lean_box(0), lean_box(0));
return v___x_3137_;
}
}
else
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_dec_ref(v_G_3125_);
lean_dec_ref(v___x_3121_);
lean_dec_ref(v_inst_3119_);
v___x_3138_ = lean_box(v___x_3126_);
v___x_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
lean_ctor_set(v___x_3140_, 1, v___x_3120_);
return v___x_3140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0___boxed(lean_object* v_n_3141_, lean_object* v_xs_3142_, lean_object* v_ys_3143_, lean_object* v_lt_3144_, lean_object* v_inst_3145_, lean_object* v___x_3146_, lean_object* v___x_3147_, lean_object* v_next_3148_, lean_object* v_acc_3149_, lean_object* v_h_3150_, lean_object* v_G_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Vector_lex___redArg___lam__0(v_n_3141_, v_xs_3142_, v_ys_3143_, v_lt_3144_, v_inst_3145_, v___x_3146_, v___x_3147_, v_next_3148_, v_acc_3149_, v_h_3150_, v_G_3151_);
lean_dec_ref(v_acc_3149_);
lean_dec(v_next_3148_);
lean_dec_ref(v_ys_3143_);
lean_dec_ref(v_xs_3142_);
lean_dec(v_n_3141_);
return v_res_3152_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object* v_n_3156_, lean_object* v_inst_3157_, lean_object* v_xs_3158_, lean_object* v_ys_3159_, lean_object* v_lt_3160_){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___f_3164_; lean_object* v___x_3165_; lean_object* v_fst_3166_; 
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = lean_box(0);
v___x_3163_ = ((lean_object*)(l_Vector_lex___redArg___closed__0));
v___f_3164_ = lean_alloc_closure((void*)(l_Vector_lex___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_3164_, 0, v_n_3156_);
lean_closure_set(v___f_3164_, 1, v_xs_3158_);
lean_closure_set(v___f_3164_, 2, v_ys_3159_);
lean_closure_set(v___f_3164_, 3, v_lt_3160_);
lean_closure_set(v___f_3164_, 4, v_inst_3157_);
lean_closure_set(v___f_3164_, 5, v___x_3162_);
lean_closure_set(v___f_3164_, 6, v___x_3163_);
v___x_3165_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3164_, v___x_3161_, v___x_3163_, lean_box(0));
v_fst_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_fst_3166_);
lean_dec(v___x_3165_);
if (lean_obj_tag(v_fst_3166_) == 0)
{
uint8_t v___x_3167_; 
v___x_3167_ = 0;
return v___x_3167_;
}
else
{
lean_object* v_val_3168_; uint8_t v___x_3169_; 
v_val_3168_ = lean_ctor_get(v_fst_3166_, 0);
lean_inc(v_val_3168_);
lean_dec_ref_known(v_fst_3166_, 1);
v___x_3169_ = lean_unbox(v_val_3168_);
lean_dec(v_val_3168_);
return v___x_3169_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object* v_n_3170_, lean_object* v_inst_3171_, lean_object* v_xs_3172_, lean_object* v_ys_3173_, lean_object* v_lt_3174_){
_start:
{
uint8_t v_res_3175_; lean_object* v_r_3176_; 
v_res_3175_ = l_Vector_lex___redArg(v_n_3170_, v_inst_3171_, v_xs_3172_, v_ys_3173_, v_lt_3174_);
v_r_3176_ = lean_box(v_res_3175_);
return v_r_3176_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex(lean_object* v_00_u03b1_3177_, lean_object* v_n_3178_, lean_object* v_inst_3179_, lean_object* v_xs_3180_, lean_object* v_ys_3181_, lean_object* v_lt_3182_){
_start:
{
uint8_t v___x_3183_; 
v___x_3183_ = l_Vector_lex___redArg(v_n_3178_, v_inst_3179_, v_xs_3180_, v_ys_3181_, v_lt_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object* v_00_u03b1_3184_, lean_object* v_n_3185_, lean_object* v_inst_3186_, lean_object* v_xs_3187_, lean_object* v_ys_3188_, lean_object* v_lt_3189_){
_start:
{
uint8_t v_res_3190_; lean_object* v_r_3191_; 
v_res_3190_ = l_Vector_lex(v_00_u03b1_3184_, v_n_3185_, v_inst_3186_, v_xs_3187_, v_ys_3188_, v_lt_3189_);
v_r_3191_ = lean_box(v_res_3190_);
return v_r_3191_;
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
