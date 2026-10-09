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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
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
static const lean_ctor_object l_Vector_lex___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(11) << 1) | 1))}};
static const lean_object* l_Vector_lex___auto__1___closed__13 = (const lean_object*)&l_Vector_lex___auto__1___closed__13_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Vector_lex___auto__1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector_lex___auto__1___closed__14 = (const lean_object*)&l_Vector_lex___auto__1___closed__14_value;
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
static const lean_string_object l_Vector_lex___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l_Vector_lex___auto__1___closed__20 = (const lean_object*)&l_Vector_lex___auto__1___closed__20_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_lex___auto__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l_Vector_lex___auto__1___closed__21 = (const lean_object*)&l_Vector_lex___auto__1___closed__21_value;
static const lean_string_object l_Vector_lex___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l_Vector_lex___auto__1___closed__22 = (const lean_object*)&l_Vector_lex___auto__1___closed__22_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__23_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__23_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__23_value_aux_2),((lean_object*)&l_Vector_lex___auto__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l_Vector_lex___auto__1___closed__23 = (const lean_object*)&l_Vector_lex___auto__1___closed__23_value;
static const lean_string_object l_Vector_lex___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l_Vector_lex___auto__1___closed__24 = (const lean_object*)&l_Vector_lex___auto__1___closed__24_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__25;
static lean_once_cell_t l_Vector_lex___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__26;
static lean_once_cell_t l_Vector_lex___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__27;
static lean_once_cell_t l_Vector_lex___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__28;
static lean_once_cell_t l_Vector_lex___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__29;
static const lean_string_object l_Vector_lex___auto__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_Vector_lex___auto__1___closed__30 = (const lean_object*)&l_Vector_lex___auto__1___closed__30_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__31;
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
LEAN_EXPORT lean_object* l_Vector_lex___auto__1;
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Vector_lex___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector_lex___redArg___closed__0 = (const lean_object*)&l_Vector_lex___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_lex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqVector_decEq___redArg(lean_object* v_inst_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Array_instDecidableEqImpl___redArg(v_inst_1_, v_x_2_, v_x_3_);
return v___x_4_;
}
}
LEAN_EXPORT void l_instDecidableEqVector_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_x_3_ = stack[2].m_obj;
uint8_t v_res_5_;
v_res_5_ = l_instDecidableEqVector_decEq___redArg(v_inst_1_, v_x_2_, v_x_3_);
stack->m_num = v_res_5_;
}
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___redArg___boxed(lean_object* v_inst_6_, lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_instDecidableEqVector_decEq___redArg(v_inst_6_, v_x_7_, v_x_8_);
lean_dec_ref(v_x_8_);
lean_dec_ref(v_x_7_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
uint8_t l_instDecidableEqVector_decEq(lean_object* v_00_u03b1_11_, lean_object* v_n_12_, lean_object* v_inst_13_, lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = l_Array_instDecidableEqImpl___redArg(v_inst_13_, v_x_14_, v_x_15_);
return v___x_16_;
}
}
LEAN_EXPORT void l_instDecidableEqVector_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_12_ = stack[1].m_obj;
lean_object* v_inst_13_ = stack[2].m_obj;
lean_object* v_x_14_ = stack[3].m_obj;
lean_object* v_x_15_ = stack[4].m_obj;
uint8_t v_res_17_;
v_res_17_ = l_instDecidableEqVector_decEq(lean_box(0), v_n_12_, v_inst_13_, v_x_14_, v_x_15_);
stack->m_num = v_res_17_;
}
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___boxed(lean_object* v_00_u03b1_18_, lean_object* v_n_19_, lean_object* v_inst_20_, lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_instDecidableEqVector_decEq(v_00_u03b1_18_, v_n_19_, v_inst_20_, v_x_21_, v_x_22_);
lean_dec_ref(v_x_22_);
lean_dec_ref(v_x_21_);
lean_dec(v_n_19_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
uint8_t l_instDecidableEqVector___redArg(lean_object* v_inst_25_, lean_object* v_x_26_, lean_object* v_x_27_){
_start:
{
uint8_t v___x_28_; 
v___x_28_ = l_Array_instDecidableEqImpl___redArg(v_inst_25_, v_x_26_, v_x_27_);
return v___x_28_;
}
}
LEAN_EXPORT void l_instDecidableEqVector___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_25_ = stack[0].m_obj;
lean_object* v_x_26_ = stack[1].m_obj;
lean_object* v_x_27_ = stack[2].m_obj;
uint8_t v_res_29_;
v_res_29_ = l_instDecidableEqVector___redArg(v_inst_25_, v_x_26_, v_x_27_);
stack->m_num = v_res_29_;
}
LEAN_EXPORT lean_object* l_instDecidableEqVector___redArg___boxed(lean_object* v_inst_30_, lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_instDecidableEqVector___redArg(v_inst_30_, v_x_31_, v_x_32_);
lean_dec_ref(v_x_32_);
lean_dec_ref(v_x_31_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
uint8_t l_instDecidableEqVector(lean_object* v_00_u03b1_35_, lean_object* v_n_36_, lean_object* v_inst_37_, lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
uint8_t v___x_40_; 
v___x_40_ = l_Array_instDecidableEqImpl___redArg(v_inst_37_, v_x_38_, v_x_39_);
return v___x_40_;
}
}
LEAN_EXPORT void l_instDecidableEqVector_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_36_ = stack[1].m_obj;
lean_object* v_inst_37_ = stack[2].m_obj;
lean_object* v_x_38_ = stack[3].m_obj;
lean_object* v_x_39_ = stack[4].m_obj;
uint8_t v_res_41_;
v_res_41_ = l_instDecidableEqVector(lean_box(0), v_n_36_, v_inst_37_, v_x_38_, v_x_39_);
stack->m_num = v_res_41_;
}
LEAN_EXPORT lean_object* l_instDecidableEqVector___boxed(lean_object* v_00_u03b1_42_, lean_object* v_n_43_, lean_object* v_inst_44_, lean_object* v_x_45_, lean_object* v_x_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_instDecidableEqVector(v_00_u03b1_42_, v_n_43_, v_inst_44_, v_x_45_, v_x_46_);
lean_dec_ref(v_x_46_);
lean_dec_ref(v_x_45_);
lean_dec(v_n_43_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___redArg(lean_object* v_xs_49_){
_start:
{
lean_inc_ref(v_xs_49_);
return v_xs_49_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___redArg___boxed(lean_object* v_xs_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Array_toVector___redArg(v_xs_50_);
lean_dec_ref(v_xs_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector(lean_object* v_00_u03b1_52_, lean_object* v_xs_53_){
_start:
{
lean_inc_ref(v_xs_53_);
return v_xs_53_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___boxed(lean_object* v_00_u03b1_54_, lean_object* v_xs_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Array_toVector(v_00_u03b1_54_, v_xs_55_);
lean_dec_ref(v_xs_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___redArg(lean_object* v_n_57_){
_start:
{
lean_inc(v_n_57_);
return v_n_57_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___redArg___boxed(lean_object* v_n_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Vector_size___redArg(v_n_58_);
lean_dec(v_n_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Vector_size(lean_object* v_00_u03b1_60_, lean_object* v_n_61_, lean_object* v_x_62_){
_start:
{
lean_inc(v_n_61_);
return v_n_61_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___boxed(lean_object* v_00_u03b1_63_, lean_object* v_n_64_, lean_object* v_x_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Vector_size(v_00_u03b1_63_, v_n_64_, v_x_65_);
lean_dec_ref(v_x_65_);
lean_dec(v_n_64_);
return v_res_66_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5));
v___x_126_ = l_String_toRawSubstring_x27(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18));
v___x_154_ = l_String_toRawSubstring_x27(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26(void){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Array_mkArray0___redArg();
return v___x_163_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27));
v___x_166_ = l_String_toRawSubstring_x27(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(lean_object* v_x_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__2));
lean_inc(v_x_175_);
v___x_179_ = l_Lean_Syntax_isOfKind(v_x_175_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_x_175_);
v___x_180_ = lean_box(1);
v___x_181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_a_177_);
return v___x_181_;
}
else
{
lean_object* v_quotContext_182_; lean_object* v_currMacroScope_183_; lean_object* v_ref_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_elems_187_; uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_quotContext_182_ = lean_ctor_get(v_a_176_, 1);
v_currMacroScope_183_ = lean_ctor_get(v_a_176_, 2);
v_ref_184_ = lean_ctor_get(v_a_176_, 5);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = l_Lean_Syntax_getArg(v_x_175_, v___x_185_);
lean_dec(v_x_175_);
v_elems_187_ = l_Lean_Syntax_getArgs(v___x_186_);
lean_dec(v___x_186_);
v___x_188_ = 0;
v___x_189_ = l_Lean_SourceInfo_fromRef(v_ref_184_, v___x_188_);
v___x_190_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4));
v___x_191_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6);
v___x_192_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8));
lean_inc_n(v_currMacroScope_183_, 3);
lean_inc_n(v_quotContext_182_, 3);
v___x_193_ = l_Lean_addMacroScope(v_quotContext_182_, v___x_192_, v_currMacroScope_183_);
v___x_194_ = lean_box(0);
v___x_195_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12));
lean_inc_n(v___x_189_, 12);
v___x_196_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_196_, 0, v___x_189_);
lean_ctor_set(v___x_196_, 1, v___x_191_);
lean_ctor_set(v___x_196_, 2, v___x_193_);
lean_ctor_set(v___x_196_, 3, v___x_195_);
v___x_197_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_198_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16));
v___x_199_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_189_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19);
v___x_202_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20));
v___x_203_ = l_Lean_addMacroScope(v_quotContext_182_, v___x_202_, v_currMacroScope_183_);
v___x_204_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_204_, 0, v___x_189_);
lean_ctor_set(v___x_204_, 1, v___x_201_);
lean_ctor_set(v___x_204_, 2, v___x_203_);
lean_ctor_set(v___x_204_, 3, v___x_194_);
v___x_205_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21));
v___x_206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_189_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_elems_187_);
v___x_208_ = lean_array_get_size(v___x_207_);
lean_dec_ref(v___x_207_);
v___x_209_ = l_Nat_reprFast(v___x_208_);
v___x_210_ = lean_box(2);
v___x_211_ = l_Lean_Syntax_mkNumLit(v___x_209_, v___x_210_);
v___x_212_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_189_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = l_Lean_Syntax_node5(v___x_189_, v___x_198_, v___x_200_, v___x_204_, v___x_206_, v___x_211_, v___x_213_);
v___x_215_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24));
v___x_216_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25));
v___x_217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_189_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
v___x_219_ = l_Array_append___redArg(v___x_218_, v_elems_187_);
lean_dec_ref(v_elems_187_);
v___x_220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_220_, 0, v___x_189_);
lean_ctor_set(v___x_220_, 1, v___x_197_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
v___x_221_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__18));
v___x_222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_189_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = l_Lean_Syntax_node3(v___x_189_, v___x_215_, v___x_217_, v___x_220_, v___x_222_);
v___x_224_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28);
v___x_225_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29));
v___x_226_ = l_Lean_addMacroScope(v_quotContext_182_, v___x_225_, v_currMacroScope_183_);
v___x_227_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31));
v___x_228_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_228_, 0, v___x_189_);
lean_ctor_set(v___x_228_, 1, v___x_224_);
lean_ctor_set(v___x_228_, 2, v___x_226_);
lean_ctor_set(v___x_228_, 3, v___x_227_);
v___x_229_ = l_Lean_Syntax_node3(v___x_189_, v___x_197_, v___x_214_, v___x_223_, v___x_228_);
v___x_230_ = l_Lean_Syntax_node2(v___x_189_, v___x_190_, v___x_196_, v___x_229_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_a_177_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___boxed(lean_object* v_x_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(v_x_232_, v_a_233_, v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Vector_unexpandMk(lean_object* v_x_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4));
lean_inc(v_x_236_);
v___x_240_ = l_Lean_Syntax_isOfKind(v_x_236_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_dec(v_x_236_);
v___x_241_ = lean_box(0);
v___x_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v_a_238_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = l_Lean_Syntax_getArg(v_x_236_, v___x_243_);
lean_dec(v_x_236_);
v___x_245_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_244_);
v___x_246_ = l_Lean_Syntax_matchesNull(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_a_238_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = l_Lean_Syntax_getArg(v___x_244_, v___x_249_);
lean_dec(v___x_244_);
v___x_251_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24));
lean_inc(v___x_250_);
v___x_252_ = l_Lean_Syntax_isOfKind(v___x_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v___x_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v_a_238_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_255_ = l_Lean_Syntax_getArg(v___x_250_, v___x_243_);
lean_dec(v___x_250_);
v___x_256_ = l_Lean_Syntax_getArgs(v___x_255_);
lean_dec(v___x_255_);
v___x_257_ = 0;
v___x_258_ = l_Lean_SourceInfo_fromRef(v_a_237_, v___x_257_);
v___x_259_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__2));
v___x_260_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__5));
lean_inc_n(v___x_258_, 3);
v___x_261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_258_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_263_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
v___x_264_ = l_Array_append___redArg(v___x_263_, v___x_256_);
lean_dec_ref(v___x_256_);
v___x_265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_265_, 0, v___x_258_);
lean_ctor_set(v___x_265_, 1, v___x_262_);
lean_ctor_set(v___x_265_, 2, v___x_264_);
v___x_266_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__18));
v___x_267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_258_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = l_Lean_Syntax_node3(v___x_258_, v___x_259_, v___x_261_, v___x_265_, v___x_267_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_a_238_);
return v___x_269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unexpandMk___boxed(lean_object* v_x_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Vector_unexpandMk(v_x_270_, v_a_271_, v_a_272_);
lean_dec(v_a_271_);
return v_res_273_;
}
}
static lean_object* _init_l_Vector_Vector_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__5));
v___x_280_ = lean_string_length(v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Vector_Vector_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_obj_once(&l_Vector_Vector_repr___redArg___closed__2, &l_Vector_Vector_repr___redArg___closed__2_once, _init_l_Vector_Vector_repr___redArg___closed__2);
v___x_282_ = lean_nat_to_int(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr___redArg(lean_object* v_inst_290_, lean_object* v_n_291_, lean_object* v_xs_292_){
_start:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_nat_dec_eq(v_n_291_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v_x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_x_295_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_295_, 0, lean_box(0));
lean_closure_set(v_x_295_, 1, v_inst_290_);
v___x_296_ = lean_array_to_list(v_xs_292_);
v___x_297_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__1));
v___x_298_ = l_Std_Format_joinSep___redArg(v_x_295_, v___x_296_, v___x_297_);
v___x_299_ = lean_obj_once(&l_Vector_Vector_repr___redArg___closed__3, &l_Vector_Vector_repr___redArg___closed__3_once, _init_l_Vector_Vector_repr___redArg___closed__3);
v___x_300_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__4));
v___x_301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_298_);
v___x_302_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__5));
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_299_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Std_Format_fill(v___x_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; 
lean_dec_ref(v_xs_292_);
lean_dec_ref(v_inst_290_);
v___x_306_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__7));
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr___redArg___boxed(lean_object* v_inst_307_, lean_object* v_n_308_, lean_object* v_xs_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Vector_Vector_repr___redArg(v_inst_307_, v_n_308_, v_xs_309_);
lean_dec(v_n_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr(lean_object* v_00_u03b1_311_, lean_object* v_inst_312_, lean_object* v_n_313_, lean_object* v_xs_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Vector_Vector_repr___redArg(v_inst_312_, v_n_313_, v_xs_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr___boxed(lean_object* v_00_u03b1_316_, lean_object* v_inst_317_, lean_object* v_n_318_, lean_object* v_xs_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Vector_Vector_repr(v_00_u03b1_316_, v_inst_317_, v_n_318_, v_xs_319_);
lean_dec(v_n_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg___lam__0(lean_object* v_inst_321_, lean_object* v_n_322_, lean_object* v_xs_323_, lean_object* v_x_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Vector_Vector_repr___redArg(v_inst_321_, v_n_322_, v_xs_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg___lam__0___boxed(lean_object* v_inst_326_, lean_object* v_n_327_, lean_object* v_xs_328_, lean_object* v_x_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Vector_Vector_instRepr___redArg___lam__0(v_inst_326_, v_n_327_, v_xs_328_, v_x_329_);
lean_dec(v_x_329_);
lean_dec(v_n_327_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg(lean_object* v_inst_331_, lean_object* v_n_332_){
_start:
{
lean_object* v___f_333_; 
v___f_333_ = lean_alloc_closure((void*)(l_Vector_Vector_instRepr___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_333_, 0, v_inst_331_);
lean_closure_set(v___f_333_, 1, v_n_332_);
return v___f_333_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr(lean_object* v_00_u03b1_334_, lean_object* v_inst_335_, lean_object* v_n_336_){
_start:
{
lean_object* v___f_337_; 
v___f_337_ = lean_alloc_closure((void*)(l_Vector_Vector_instRepr___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_337_, 0, v_inst_335_);
lean_closure_set(v___f_337_, 1, v_n_336_);
return v___f_337_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList___redArg(lean_object* v_xs_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_array_to_list(v_xs_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList(lean_object* v_00_u03b1_340_, lean_object* v_n_341_, lean_object* v_xs_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_array_to_list(v_xs_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList___boxed(lean_object* v_00_u03b1_344_, lean_object* v_n_345_, lean_object* v_xs_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Vector_toList(v_00_u03b1_344_, v_n_345_, v_xs_346_);
lean_dec(v_n_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray___redArg(lean_object* v_mk_348_, lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lean_apply_2(v_mk_348_, v_x_349_, lean_box(0));
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray(lean_object* v_00_u03b1_351_, lean_object* v_n_352_, lean_object* v_motive_353_, lean_object* v_mk_354_, lean_object* v_x_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_apply_2(v_mk_354_, v_x_355_, lean_box(0));
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray___boxed(lean_object* v_00_u03b1_357_, lean_object* v_n_358_, lean_object* v_motive_359_, lean_object* v_mk_360_, lean_object* v_x_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Vector_elimAsArray(v_00_u03b1_357_, v_n_358_, v_motive_359_, v_mk_360_, v_x_361_);
lean_dec(v_n_358_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList___redArg(lean_object* v_mk_363_, lean_object* v_x_364_){
_start:
{
lean_object* v_toList_365_; lean_object* v___x_366_; 
v_toList_365_ = lean_array_to_list(v_x_364_);
v___x_366_ = lean_apply_2(v_mk_363_, v_toList_365_, lean_box(0));
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList(lean_object* v_00_u03b1_367_, lean_object* v_n_368_, lean_object* v_motive_369_, lean_object* v_mk_370_, lean_object* v_x_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Vector_elimAsList___redArg(v_mk_370_, v_x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList___boxed(lean_object* v_00_u03b1_373_, lean_object* v_n_374_, lean_object* v_motive_375_, lean_object* v_mk_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Vector_elimAsList(v_00_u03b1_373_, v_n_374_, v_motive_375_, v_mk_376_, v_x_377_);
lean_dec(v_n_374_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg(lean_object* v_capacity_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_mk_empty_array_with_capacity(v_capacity_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Vector_emptyWithCapacity___redArg(v_capacity_381_);
lean_dec(v_capacity_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity(lean_object* v_00_u03b1_383_, lean_object* v_capacity_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_mk_empty_array_with_capacity(v_capacity_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___boxed(lean_object* v_00_u03b1_386_, lean_object* v_capacity_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Vector_emptyWithCapacity(v_00_u03b1_386_, v_capacity_387_);
lean_dec(v_capacity_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Vector_replicate___redArg(lean_object* v_n_389_, lean_object* v_v_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_mk_array(v_n_389_, v_v_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Vector_replicate(lean_object* v_00_u03b1_392_, lean_object* v_n_393_, lean_object* v_v_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_mk_array(v_n_393_, v_v_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Vector_singleton___redArg(lean_object* v_v_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_mk_empty_array_with_capacity(v___x_397_);
v___x_399_ = lean_array_push(v___x_398_, v_v_396_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Vector_singleton(lean_object* v_00_u03b1_400_, lean_object* v_v_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_mk_empty_array_with_capacity(v___x_402_);
v___x_404_ = lean_array_push(v___x_403_, v_v_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Vector_instInhabited___redArg(lean_object* v_n_405_, lean_object* v_inst_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_mk_array(v_n_405_, v_inst_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Vector_instInhabited(lean_object* v_00_u03b1_408_, lean_object* v_n_409_, lean_object* v_inst_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_mk_array(v_n_409_, v_inst_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___redArg(lean_object* v_xs_412_, lean_object* v_i_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_array_fget_borrowed(v_xs_412_, v_i_413_);
lean_inc(v___x_414_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___redArg___boxed(lean_object* v_xs_415_, lean_object* v_i_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Vector_get___redArg(v_xs_415_, v_i_416_);
lean_dec(v_i_416_);
lean_dec_ref(v_xs_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Vector_get(lean_object* v_00_u03b1_418_, lean_object* v_n_419_, lean_object* v_xs_420_, lean_object* v_i_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = lean_array_fget_borrowed(v_xs_420_, v_i_421_);
lean_inc(v___x_422_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___boxed(lean_object* v_00_u03b1_423_, lean_object* v_n_424_, lean_object* v_xs_425_, lean_object* v_i_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Vector_get(v_00_u03b1_423_, v_n_424_, v_xs_425_, v_i_426_);
lean_dec(v_i_426_);
lean_dec_ref(v_xs_425_);
lean_dec(v_n_424_);
return v_res_427_;
}
}
lean_object* l_Vector_uget___redArg(lean_object* v_xs_428_, size_t v_i_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_array_uget_borrowed(v_xs_428_, v_i_429_);
lean_inc(v___x_430_);
return v___x_430_;
}
}
LEAN_EXPORT void l_Vector_uget___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_428_ = stack[0].m_obj;
size_t v_i_429_ = stack[1].m_num;
lean_object* v_res_431_;
v_res_431_ = l_Vector_uget___redArg(v_xs_428_, v_i_429_);
stack->m_obj
 = v_res_431_;
}
LEAN_EXPORT lean_object* l_Vector_uget___redArg___boxed(lean_object* v_xs_432_, lean_object* v_i_433_){
_start:
{
size_t v_i_boxed_434_; lean_object* v_res_435_; 
v_i_boxed_434_ = lean_unbox_usize(v_i_433_);
lean_dec(v_i_433_);
v_res_435_ = l_Vector_uget___redArg(v_xs_432_, v_i_boxed_434_);
lean_dec_ref(v_xs_432_);
return v_res_435_;
}
}
lean_object* l_Vector_uget(lean_object* v_00_u03b1_436_, lean_object* v_n_437_, lean_object* v_xs_438_, size_t v_i_439_, lean_object* v_h_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_array_uget_borrowed(v_xs_438_, v_i_439_);
lean_inc(v___x_441_);
return v___x_441_;
}
}
LEAN_EXPORT void l_Vector_uget_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_437_ = stack[1].m_obj;
lean_object* v_xs_438_ = stack[2].m_obj;
size_t v_i_439_ = stack[3].m_num;
lean_object* v_res_442_;
v_res_442_ = l_Vector_uget(lean_box(0), v_n_437_, v_xs_438_, v_i_439_, lean_box(0));
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_Vector_uget___boxed(lean_object* v_00_u03b1_443_, lean_object* v_n_444_, lean_object* v_xs_445_, lean_object* v_i_446_, lean_object* v_h_447_){
_start:
{
size_t v_i_boxed_448_; lean_object* v_res_449_; 
v_i_boxed_448_ = lean_unbox_usize(v_i_446_);
lean_dec(v_i_446_);
v_res_449_ = l_Vector_uget(v_00_u03b1_443_, v_n_444_, v_xs_445_, v_i_boxed_448_, v_h_447_);
lean_dec_ref(v_xs_445_);
lean_dec(v_n_444_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___lam__0(lean_object* v_xs_450_, lean_object* v_i_451_, lean_object* v_h_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = lean_array_fget_borrowed(v_xs_450_, v_i_451_);
lean_inc(v___x_453_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___lam__0___boxed(lean_object* v_xs_454_, lean_object* v_i_455_, lean_object* v_h_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Vector_instGetElemNatLt___redArg___lam__0(v_xs_454_, v_i_455_, v_h_456_);
lean_dec(v_i_455_);
lean_dec_ref(v_xs_454_);
return v_res_457_;
}
}
lean_object* l_Vector_instGetElemNatLt___redArg(){
_start:
{
lean_object* v___f_460_; 
v___f_460_ = ((lean_object*)(l_Vector_instGetElemNatLt___redArg___closed__0));
return v___f_460_;
}
}
LEAN_EXPORT void l_Vector_instGetElemNatLt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_461_;
v_res_461_ = l_Vector_instGetElemNatLt___redArg();
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___boxed(lean_object* v___dummy_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Vector_instGetElemNatLt___redArg();
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt(lean_object* v_00_u03b1_464_, lean_object* v_n_465_){
_start:
{
lean_object* v___f_466_; 
v___f_466_ = ((lean_object*)(l_Vector_instGetElemNatLt___redArg___closed__0));
return v___f_466_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___boxed(lean_object* v_00_u03b1_467_, lean_object* v_n_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Vector_instGetElemNatLt(v_00_u03b1_467_, v_n_468_);
lean_dec(v_n_468_);
return v_res_469_;
}
}
uint8_t l_Vector_contains___redArg(lean_object* v_inst_470_, lean_object* v_xs_471_, lean_object* v_a_472_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = l_Array_contains___redArg(v_inst_470_, v_xs_471_, v_a_472_);
return v___x_473_;
}
}
LEAN_EXPORT void l_Vector_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_470_ = stack[0].m_obj;
lean_object* v_xs_471_ = stack[1].m_obj;
lean_object* v_a_472_ = stack[2].m_obj;
uint8_t v_res_474_;
v_res_474_ = l_Vector_contains___redArg(v_inst_470_, v_xs_471_, v_a_472_);
stack->m_num = v_res_474_;
}
LEAN_EXPORT lean_object* l_Vector_contains___redArg___boxed(lean_object* v_inst_475_, lean_object* v_xs_476_, lean_object* v_a_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_Vector_contains___redArg(v_inst_475_, v_xs_476_, v_a_477_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
uint8_t l_Vector_contains(lean_object* v_00_u03b1_480_, lean_object* v_n_481_, lean_object* v_inst_482_, lean_object* v_xs_483_, lean_object* v_a_484_){
_start:
{
uint8_t v___x_485_; 
v___x_485_ = l_Array_contains___redArg(v_inst_482_, v_xs_483_, v_a_484_);
return v___x_485_;
}
}
LEAN_EXPORT void l_Vector_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_481_ = stack[1].m_obj;
lean_object* v_inst_482_ = stack[2].m_obj;
lean_object* v_xs_483_ = stack[3].m_obj;
lean_object* v_a_484_ = stack[4].m_obj;
uint8_t v_res_486_;
v_res_486_ = l_Vector_contains(lean_box(0), v_n_481_, v_inst_482_, v_xs_483_, v_a_484_);
stack->m_num = v_res_486_;
}
LEAN_EXPORT lean_object* l_Vector_contains___boxed(lean_object* v_00_u03b1_487_, lean_object* v_n_488_, lean_object* v_inst_489_, lean_object* v_xs_490_, lean_object* v_a_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Vector_contains(v_00_u03b1_487_, v_n_488_, v_inst_489_, v_xs_490_, v_a_491_);
lean_dec(v_n_488_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
lean_object* l_Vector_instMembership___redArg(){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_box(0);
return v___x_495_;
}
}
LEAN_EXPORT void l_Vector_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_496_;
v_res_496_ = l_Vector_instMembership___redArg();
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l_Vector_instMembership___redArg___boxed(lean_object* v___dummy_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Vector_instMembership___redArg();
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership(lean_object* v_00_u03b1_499_, lean_object* v_n_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_box(0);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership___boxed(lean_object* v_00_u03b1_502_, lean_object* v_n_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Vector_instMembership(v_00_u03b1_502_, v_n_503_);
lean_dec(v_n_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg(lean_object* v_xs_505_, lean_object* v_i_506_, lean_object* v_default_507_){
_start:
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_array_get_size(v_xs_505_);
v___x_509_ = lean_nat_dec_lt(v_i_506_, v___x_508_);
if (v___x_509_ == 0)
{
lean_inc(v_default_507_);
return v_default_507_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = lean_array_fget_borrowed(v_xs_505_, v_i_506_);
lean_inc(v___x_510_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg___boxed(lean_object* v_xs_511_, lean_object* v_i_512_, lean_object* v_default_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Vector_getD___redArg(v_xs_511_, v_i_512_, v_default_513_);
lean_dec(v_default_513_);
lean_dec(v_i_512_);
lean_dec_ref(v_xs_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD(lean_object* v_00_u03b1_515_, lean_object* v_n_516_, lean_object* v_xs_517_, lean_object* v_i_518_, lean_object* v_default_519_){
_start:
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_array_get_size(v_xs_517_);
v___x_521_ = lean_nat_dec_lt(v_i_518_, v___x_520_);
if (v___x_521_ == 0)
{
lean_inc(v_default_519_);
return v_default_519_;
}
else
{
lean_object* v___x_522_; 
v___x_522_ = lean_array_fget_borrowed(v_xs_517_, v_i_518_);
lean_inc(v___x_522_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___boxed(lean_object* v_00_u03b1_523_, lean_object* v_n_524_, lean_object* v_xs_525_, lean_object* v_i_526_, lean_object* v_default_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Vector_getD(v_00_u03b1_523_, v_n_524_, v_xs_525_, v_i_526_, v_default_527_);
lean_dec(v_default_527_);
lean_dec(v_i_526_);
lean_dec_ref(v_xs_525_);
lean_dec(v_n_524_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg(lean_object* v_inst_529_, lean_object* v_xs_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_531_ = lean_array_get_size(v_xs_530_);
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = lean_nat_sub(v___x_531_, v___x_532_);
v___x_534_ = lean_array_get_borrowed(v_inst_529_, v_xs_530_, v___x_533_);
lean_dec(v___x_533_);
lean_inc(v___x_534_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg___boxed(lean_object* v_inst_535_, lean_object* v_xs_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Vector_back_x21___redArg(v_inst_535_, v_xs_536_);
lean_dec_ref(v_xs_536_);
lean_dec(v_inst_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21(lean_object* v_00_u03b1_538_, lean_object* v_n_539_, lean_object* v_inst_540_, lean_object* v_xs_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = lean_array_get_size(v_xs_541_);
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_sub(v___x_542_, v___x_543_);
v___x_545_ = lean_array_get_borrowed(v_inst_540_, v_xs_541_, v___x_544_);
lean_dec(v___x_544_);
lean_inc(v___x_545_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___boxed(lean_object* v_00_u03b1_546_, lean_object* v_n_547_, lean_object* v_inst_548_, lean_object* v_xs_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Vector_back_x21(v_00_u03b1_546_, v_n_547_, v_inst_548_, v_xs_549_);
lean_dec_ref(v_xs_549_);
lean_dec(v_inst_548_);
lean_dec(v_n_547_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg(lean_object* v_xs_551_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_552_ = lean_array_get_size(v_xs_551_);
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_nat_sub(v___x_552_, v___x_553_);
v___x_555_ = lean_nat_dec_lt(v___x_554_, v___x_552_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
lean_dec(v___x_554_);
v___x_556_ = lean_box(0);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_array_fget_borrowed(v_xs_551_, v___x_554_);
lean_dec(v___x_554_);
lean_inc(v___x_557_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg___boxed(lean_object* v_xs_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Vector_back_x3f___redArg(v_xs_559_);
lean_dec_ref(v_xs_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f(lean_object* v_00_u03b1_561_, lean_object* v_n_562_, lean_object* v_xs_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_564_ = lean_array_get_size(v_xs_563_);
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_sub(v___x_564_, v___x_565_);
v___x_567_ = lean_nat_dec_lt(v___x_566_, v___x_564_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
lean_dec(v___x_566_);
v___x_568_ = lean_box(0);
return v___x_568_;
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_array_fget_borrowed(v_xs_563_, v___x_566_);
lean_dec(v___x_566_);
lean_inc(v___x_569_);
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___boxed(lean_object* v_00_u03b1_571_, lean_object* v_n_572_, lean_object* v_xs_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Vector_back_x3f(v_00_u03b1_571_, v_n_572_, v_xs_573_);
lean_dec_ref(v_xs_573_);
lean_dec(v_n_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg(lean_object* v_n_575_, lean_object* v_xs_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_sub(v_n_575_, v___x_577_);
v___x_579_ = lean_array_fget_borrowed(v_xs_576_, v___x_578_);
lean_dec(v___x_578_);
lean_inc(v___x_579_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg___boxed(lean_object* v_n_580_, lean_object* v_xs_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Vector_back___redArg(v_n_580_, v_xs_581_);
lean_dec_ref(v_xs_581_);
lean_dec(v_n_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Vector_back(lean_object* v_n_583_, lean_object* v_00_u03b1_584_, lean_object* v_inst_585_, lean_object* v_xs_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_nat_sub(v_n_583_, v___x_587_);
v___x_589_ = lean_array_fget_borrowed(v_xs_586_, v___x_588_);
lean_dec(v___x_588_);
lean_inc(v___x_589_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___boxed(lean_object* v_n_590_, lean_object* v_00_u03b1_591_, lean_object* v_inst_592_, lean_object* v_xs_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Vector_back(v_n_590_, v_00_u03b1_591_, v_inst_592_, v_xs_593_);
lean_dec_ref(v_xs_593_);
lean_dec(v_n_590_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg(lean_object* v_xs_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_array_fget_borrowed(v_xs_595_, v___x_596_);
lean_inc(v___x_597_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg___boxed(lean_object* v_xs_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Vector_head___redArg(v_xs_598_);
lean_dec_ref(v_xs_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Vector_head(lean_object* v_n_600_, lean_object* v_00_u03b1_601_, lean_object* v_inst_602_, lean_object* v_xs_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_array_fget_borrowed(v_xs_603_, v___x_604_);
lean_inc(v___x_605_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___boxed(lean_object* v_n_606_, lean_object* v_00_u03b1_607_, lean_object* v_inst_608_, lean_object* v_xs_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Vector_head(v_n_606_, v_00_u03b1_607_, v_inst_608_, v_xs_609_);
lean_dec_ref(v_xs_609_);
lean_dec(v_n_606_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___redArg(lean_object* v_xs_611_, lean_object* v_x_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_array_push(v_xs_611_, v_x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Vector_push(lean_object* v_00_u03b1_614_, lean_object* v_n_615_, lean_object* v_xs_616_, lean_object* v_x_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_array_push(v_xs_616_, v_x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___boxed(lean_object* v_00_u03b1_619_, lean_object* v_n_620_, lean_object* v_xs_621_, lean_object* v_x_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Vector_push(v_00_u03b1_619_, v_n_620_, v_xs_621_, v_x_622_);
lean_dec(v_n_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___redArg(lean_object* v_xs_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_array_pop(v_xs_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop(lean_object* v_00_u03b1_626_, lean_object* v_n_627_, lean_object* v_xs_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_array_pop(v_xs_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___boxed(lean_object* v_00_u03b1_630_, lean_object* v_n_631_, lean_object* v_xs_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Vector_pop(v_00_u03b1_630_, v_n_631_, v_xs_632_);
lean_dec(v_n_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear___redArg(lean_object* v_xs_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = lean_array_mark_linear(v_xs_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear(lean_object* v_00_u03b1_636_, lean_object* v_n_637_, lean_object* v_xs_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = lean_array_mark_linear(v_xs_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear___boxed(lean_object* v_00_u03b1_640_, lean_object* v_n_641_, lean_object* v_xs_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Vector_markLinear(v_00_u03b1_640_, v_n_641_, v_xs_642_);
lean_dec(v_n_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg(lean_object* v_xs_644_, lean_object* v_ys_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_array_propagate_mark(v_xs_644_, v_ys_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg___boxed(lean_object* v_xs_647_, lean_object* v_ys_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Vector_propagateMark___redArg(v_xs_647_, v_ys_648_);
lean_dec_ref(v_xs_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark(lean_object* v_n_650_, lean_object* v_m_651_, lean_object* v_00_u03b1_652_, lean_object* v_00_u03b2_653_, lean_object* v_xs_654_, lean_object* v_ys_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = lean_array_propagate_mark(v_xs_654_, v_ys_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___boxed(lean_object* v_n_657_, lean_object* v_m_658_, lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_xs_661_, lean_object* v_ys_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Vector_propagateMark(v_n_657_, v_m_658_, v_00_u03b1_659_, v_00_u03b2_660_, v_xs_661_, v_ys_662_);
lean_dec_ref(v_xs_661_);
lean_dec(v_m_658_);
lean_dec(v_n_657_);
return v_res_663_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__9(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l_Vector_set___auto__1___closed__8));
v___x_684_ = l_Lean_mkAtom(v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__10(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_685_ = lean_obj_once(&l_Vector_set___auto__1___closed__9, &l_Vector_set___auto__1___closed__9_once, _init_l_Vector_set___auto__1___closed__9);
v___x_686_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_687_ = lean_array_push(v___x_686_, v___x_685_);
return v___x_687_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__11(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_688_ = lean_obj_once(&l_Vector_set___auto__1___closed__10, &l_Vector_set___auto__1___closed__10_once, _init_l_Vector_set___auto__1___closed__10);
v___x_689_ = ((lean_object*)(l_Vector_set___auto__1___closed__7));
v___x_690_ = lean_box(2);
v___x_691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___x_689_);
lean_ctor_set(v___x_691_, 2, v___x_688_);
return v___x_691_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__12(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = lean_obj_once(&l_Vector_set___auto__1___closed__11, &l_Vector_set___auto__1___closed__11_once, _init_l_Vector_set___auto__1___closed__11);
v___x_693_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_694_ = lean_array_push(v___x_693_, v___x_692_);
return v___x_694_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__13(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_695_ = lean_obj_once(&l_Vector_set___auto__1___closed__12, &l_Vector_set___auto__1___closed__12_once, _init_l_Vector_set___auto__1___closed__12);
v___x_696_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_697_ = lean_box(2);
v___x_698_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_696_);
lean_ctor_set(v___x_698_, 2, v___x_695_);
return v___x_698_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__14(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_obj_once(&l_Vector_set___auto__1___closed__13, &l_Vector_set___auto__1___closed__13_once, _init_l_Vector_set___auto__1___closed__13);
v___x_700_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_701_ = lean_array_push(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__15(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_702_ = lean_obj_once(&l_Vector_set___auto__1___closed__14, &l_Vector_set___auto__1___closed__14_once, _init_l_Vector_set___auto__1___closed__14);
v___x_703_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_704_ = lean_box(2);
v___x_705_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___x_703_);
lean_ctor_set(v___x_705_, 2, v___x_702_);
return v___x_705_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__16(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_obj_once(&l_Vector_set___auto__1___closed__15, &l_Vector_set___auto__1___closed__15_once, _init_l_Vector_set___auto__1___closed__15);
v___x_707_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_708_ = lean_array_push(v___x_707_, v___x_706_);
return v___x_708_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__17(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_709_ = lean_obj_once(&l_Vector_set___auto__1___closed__16, &l_Vector_set___auto__1___closed__16_once, _init_l_Vector_set___auto__1___closed__16);
v___x_710_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_711_ = lean_box(2);
v___x_712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_710_);
lean_ctor_set(v___x_712_, 2, v___x_709_);
return v___x_712_;
}
}
static lean_object* _init_l_Vector_set___auto__1(void){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg(lean_object* v_xs_714_, lean_object* v_i_715_, lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_array_fset(v_xs_714_, v_i_715_, v_x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg___boxed(lean_object* v_xs_718_, lean_object* v_i_719_, lean_object* v_x_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Vector_set___redArg(v_xs_718_, v_i_719_, v_x_720_);
lean_dec(v_i_719_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Vector_set(lean_object* v_00_u03b1_722_, lean_object* v_n_723_, lean_object* v_xs_724_, lean_object* v_i_725_, lean_object* v_x_726_, lean_object* v_h_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_array_fset(v_xs_724_, v_i_725_, v_x_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___boxed(lean_object* v_00_u03b1_729_, lean_object* v_n_730_, lean_object* v_xs_731_, lean_object* v_i_732_, lean_object* v_x_733_, lean_object* v_h_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Vector_set(v_00_u03b1_729_, v_n_730_, v_xs_731_, v_i_732_, v_x_733_, v_h_734_);
lean_dec(v_i_732_);
lean_dec(v_n_730_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg(lean_object* v_xs_736_, lean_object* v_i_737_, lean_object* v_x_738_){
_start:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_array_get_size(v_xs_736_);
v___x_740_ = lean_nat_dec_lt(v_i_737_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec(v_x_738_);
return v_xs_736_;
}
else
{
lean_object* v___x_741_; 
v___x_741_ = lean_array_fset(v_xs_736_, v_i_737_, v_x_738_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg___boxed(lean_object* v_xs_742_, lean_object* v_i_743_, lean_object* v_x_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Vector_setIfInBounds___redArg(v_xs_742_, v_i_743_, v_x_744_);
lean_dec(v_i_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds(lean_object* v_00_u03b1_746_, lean_object* v_n_747_, lean_object* v_xs_748_, lean_object* v_i_749_, lean_object* v_x_750_){
_start:
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_array_get_size(v_xs_748_);
v___x_752_ = lean_nat_dec_lt(v_i_749_, v___x_751_);
if (v___x_752_ == 0)
{
lean_dec(v_x_750_);
return v_xs_748_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_array_fset(v_xs_748_, v_i_749_, v_x_750_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___boxed(lean_object* v_00_u03b1_754_, lean_object* v_n_755_, lean_object* v_xs_756_, lean_object* v_i_757_, lean_object* v_x_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Vector_setIfInBounds(v_00_u03b1_754_, v_n_755_, v_xs_756_, v_i_757_, v_x_758_);
lean_dec(v_i_757_);
lean_dec(v_n_755_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg(lean_object* v_xs_760_, lean_object* v_i_761_, lean_object* v_x_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = lean_array_set(v_xs_760_, v_i_761_, v_x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg___boxed(lean_object* v_xs_764_, lean_object* v_i_765_, lean_object* v_x_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Vector_set_x21___redArg(v_xs_764_, v_i_765_, v_x_766_);
lean_dec(v_i_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21(lean_object* v_00_u03b1_768_, lean_object* v_n_769_, lean_object* v_xs_770_, lean_object* v_i_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_array_set(v_xs_770_, v_i_771_, v_x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___boxed(lean_object* v_00_u03b1_774_, lean_object* v_n_775_, lean_object* v_xs_776_, lean_object* v_i_777_, lean_object* v_x_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Vector_set_x21(v_00_u03b1_774_, v_n_775_, v_xs_776_, v_i_777_, v_x_778_);
lean_dec(v_i_777_);
lean_dec(v_n_775_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___redArg(lean_object* v_inst_780_, lean_object* v_f_781_, lean_object* v_b_782_, lean_object* v_xs_783_){
_start:
{
lean_object* v_toApplicative_784_; lean_object* v_toPure_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_toApplicative_784_ = lean_ctor_get(v_inst_780_, 0);
v_toPure_785_ = lean_ctor_get(v_toApplicative_784_, 1);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_array_get_size(v_xs_783_);
v___x_788_ = lean_nat_dec_lt(v___x_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_inc(v_toPure_785_);
lean_dec_ref(v_xs_783_);
lean_dec(v_f_781_);
lean_dec_ref(v_inst_780_);
v___x_789_ = lean_apply_2(v_toPure_785_, lean_box(0), v_b_782_);
return v___x_789_;
}
else
{
uint8_t v___x_790_; 
v___x_790_ = lean_nat_dec_le(v___x_787_, v___x_787_);
if (v___x_790_ == 0)
{
if (v___x_788_ == 0)
{
lean_object* v___x_791_; 
lean_inc(v_toPure_785_);
lean_dec_ref(v_xs_783_);
lean_dec(v_f_781_);
lean_dec_ref(v_inst_780_);
v___x_791_ = lean_apply_2(v_toPure_785_, lean_box(0), v_b_782_);
return v___x_791_;
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((size_t)0ULL);
v___x_793_ = lean_usize_of_nat(v___x_787_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_780_, v_f_781_, v_xs_783_, v___x_792_, v___x_793_, v_b_782_);
return v___x_794_;
}
}
else
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((size_t)0ULL);
v___x_796_ = lean_usize_of_nat(v___x_787_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_780_, v_f_781_, v_xs_783_, v___x_795_, v___x_796_, v_b_782_);
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM(lean_object* v_m_798_, lean_object* v_00_u03b2_799_, lean_object* v_00_u03b1_800_, lean_object* v_n_801_, lean_object* v_inst_802_, lean_object* v_f_803_, lean_object* v_b_804_, lean_object* v_xs_805_){
_start:
{
lean_object* v_toApplicative_806_; lean_object* v_toPure_807_; lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_toApplicative_806_ = lean_ctor_get(v_inst_802_, 0);
v_toPure_807_ = lean_ctor_get(v_toApplicative_806_, 1);
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = lean_array_get_size(v_xs_805_);
v___x_810_ = lean_nat_dec_lt(v___x_808_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; 
lean_inc(v_toPure_807_);
lean_dec_ref(v_xs_805_);
lean_dec(v_f_803_);
lean_dec_ref(v_inst_802_);
v___x_811_ = lean_apply_2(v_toPure_807_, lean_box(0), v_b_804_);
return v___x_811_;
}
else
{
uint8_t v___x_812_; 
v___x_812_ = lean_nat_dec_le(v___x_809_, v___x_809_);
if (v___x_812_ == 0)
{
if (v___x_810_ == 0)
{
lean_object* v___x_813_; 
lean_inc(v_toPure_807_);
lean_dec_ref(v_xs_805_);
lean_dec(v_f_803_);
lean_dec_ref(v_inst_802_);
v___x_813_ = lean_apply_2(v_toPure_807_, lean_box(0), v_b_804_);
return v___x_813_;
}
else
{
size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; 
v___x_814_ = ((size_t)0ULL);
v___x_815_ = lean_usize_of_nat(v___x_809_);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_802_, v_f_803_, v_xs_805_, v___x_814_, v___x_815_, v_b_804_);
return v___x_816_;
}
}
else
{
size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; 
v___x_817_ = ((size_t)0ULL);
v___x_818_ = lean_usize_of_nat(v___x_809_);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_802_, v_f_803_, v_xs_805_, v___x_817_, v___x_818_, v_b_804_);
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___boxed(lean_object* v_m_820_, lean_object* v_00_u03b2_821_, lean_object* v_00_u03b1_822_, lean_object* v_n_823_, lean_object* v_inst_824_, lean_object* v_f_825_, lean_object* v_b_826_, lean_object* v_xs_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Vector_foldlM(v_m_820_, v_00_u03b2_821_, v_00_u03b1_822_, v_n_823_, v_inst_824_, v_f_825_, v_b_826_, v_xs_827_);
lean_dec(v_n_823_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___redArg(lean_object* v_inst_829_, lean_object* v_f_830_, lean_object* v_b_831_, lean_object* v_xs_832_){
_start:
{
lean_object* v_toApplicative_833_; lean_object* v_toPure_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_toApplicative_833_ = lean_ctor_get(v_inst_829_, 0);
v_toPure_834_ = lean_ctor_get(v_toApplicative_833_, 1);
v___x_835_ = lean_array_get_size(v_xs_832_);
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_nat_dec_lt(v___x_836_, v___x_835_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_inc(v_toPure_834_);
lean_dec_ref(v_xs_832_);
lean_dec(v_f_830_);
lean_dec_ref(v_inst_829_);
v___x_838_ = lean_apply_2(v_toPure_834_, lean_box(0), v_b_831_);
return v___x_838_;
}
else
{
size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_usize_of_nat(v___x_835_);
v___x_840_ = ((size_t)0ULL);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_829_, v_f_830_, v_xs_832_, v___x_839_, v___x_840_, v_b_831_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM(lean_object* v_m_842_, lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_n_845_, lean_object* v_inst_846_, lean_object* v_f_847_, lean_object* v_b_848_, lean_object* v_xs_849_){
_start:
{
lean_object* v_toApplicative_850_; lean_object* v_toPure_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_toApplicative_850_ = lean_ctor_get(v_inst_846_, 0);
v_toPure_851_ = lean_ctor_get(v_toApplicative_850_, 1);
v___x_852_ = lean_array_get_size(v_xs_849_);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_nat_dec_lt(v___x_853_, v___x_852_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
lean_inc(v_toPure_851_);
lean_dec_ref(v_xs_849_);
lean_dec(v_f_847_);
lean_dec_ref(v_inst_846_);
v___x_855_ = lean_apply_2(v_toPure_851_, lean_box(0), v_b_848_);
return v___x_855_;
}
else
{
size_t v___x_856_; size_t v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_usize_of_nat(v___x_852_);
v___x_857_ = ((size_t)0ULL);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_846_, v_f_847_, v_xs_849_, v___x_856_, v___x_857_, v_b_848_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___boxed(lean_object* v_m_859_, lean_object* v_00_u03b1_860_, lean_object* v_00_u03b2_861_, lean_object* v_n_862_, lean_object* v_inst_863_, lean_object* v_f_864_, lean_object* v_b_865_, lean_object* v_xs_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Vector_foldrM(v_m_859_, v_00_u03b1_860_, v_00_u03b2_861_, v_n_862_, v_inst_863_, v_f_864_, v_b_865_, v_xs_866_);
lean_dec(v_n_862_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg___lam__0(lean_object* v_f_868_, lean_object* v_x1_869_, lean_object* v_x2_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = lean_apply_2(v_f_868_, v_x1_869_, v_x2_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg(lean_object* v_f_891_, lean_object* v_b_892_, lean_object* v_xs_893_){
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
LEAN_EXPORT lean_object* l_Vector_foldl(lean_object* v_00_u03b2_906_, lean_object* v_00_u03b1_907_, lean_object* v_n_908_, lean_object* v_f_909_, lean_object* v_b_910_, lean_object* v_xs_911_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_array_get_size(v_xs_911_);
v___x_914_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_915_ = lean_nat_dec_lt(v___x_912_, v___x_913_);
if (v___x_915_ == 0)
{
lean_dec_ref(v_xs_911_);
lean_dec(v_f_909_);
return v_b_910_;
}
else
{
lean_object* v___f_916_; uint8_t v___x_917_; 
v___f_916_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_916_, 0, v_f_909_);
v___x_917_ = lean_nat_dec_le(v___x_913_, v___x_913_);
if (v___x_917_ == 0)
{
if (v___x_915_ == 0)
{
lean_dec_ref(v___f_916_);
lean_dec_ref(v_xs_911_);
return v_b_910_;
}
else
{
size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; 
v___x_918_ = ((size_t)0ULL);
v___x_919_ = lean_usize_of_nat(v___x_913_);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_914_, v___f_916_, v_xs_911_, v___x_918_, v___x_919_, v_b_910_);
return v___x_920_;
}
}
else
{
size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; 
v___x_921_ = ((size_t)0ULL);
v___x_922_ = lean_usize_of_nat(v___x_913_);
v___x_923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_914_, v___f_916_, v_xs_911_, v___x_921_, v___x_922_, v_b_910_);
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___boxed(lean_object* v_00_u03b2_924_, lean_object* v_00_u03b1_925_, lean_object* v_n_926_, lean_object* v_f_927_, lean_object* v_b_928_, lean_object* v_xs_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Vector_foldl(v_00_u03b2_924_, v_00_u03b1_925_, v_n_926_, v_f_927_, v_b_928_, v_xs_929_);
lean_dec(v_n_926_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___redArg(lean_object* v_f_931_, lean_object* v_b_932_, lean_object* v_xs_933_){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_934_ = lean_array_get_size(v_xs_933_);
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_937_ = lean_nat_dec_lt(v___x_935_, v___x_934_);
if (v___x_937_ == 0)
{
lean_dec_ref(v_xs_933_);
lean_dec(v_f_931_);
return v_b_932_;
}
else
{
lean_object* v___f_938_; size_t v___x_939_; size_t v___x_940_; lean_object* v___x_941_; 
v___f_938_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_938_, 0, v_f_931_);
v___x_939_ = lean_usize_of_nat(v___x_934_);
v___x_940_ = ((size_t)0ULL);
v___x_941_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_936_, v___f_938_, v_xs_933_, v___x_939_, v___x_940_, v_b_932_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr(lean_object* v_00_u03b1_942_, lean_object* v_00_u03b2_943_, lean_object* v_n_944_, lean_object* v_f_945_, lean_object* v_b_946_, lean_object* v_xs_947_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_948_ = lean_array_get_size(v_xs_947_);
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_951_ = lean_nat_dec_lt(v___x_949_, v___x_948_);
if (v___x_951_ == 0)
{
lean_dec_ref(v_xs_947_);
lean_dec(v_f_945_);
return v_b_946_;
}
else
{
lean_object* v___f_952_; size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
v___f_952_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_952_, 0, v_f_945_);
v___x_953_ = lean_usize_of_nat(v___x_948_);
v___x_954_ = ((size_t)0ULL);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_950_, v___f_952_, v_xs_947_, v___x_953_, v___x_954_, v_b_946_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___boxed(lean_object* v_00_u03b1_956_, lean_object* v_00_u03b2_957_, lean_object* v_n_958_, lean_object* v_f_959_, lean_object* v_b_960_, lean_object* v_xs_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Vector_foldr(v_00_u03b1_956_, v_00_u03b2_957_, v_n_958_, v_f_959_, v_b_960_, v_xs_961_);
lean_dec(v_n_958_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg(lean_object* v_xs_963_, lean_object* v_ys_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Array_append___redArg(v_xs_963_, v_ys_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg___boxed(lean_object* v_xs_966_, lean_object* v_ys_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Vector_append___redArg(v_xs_966_, v_ys_967_);
lean_dec_ref(v_ys_967_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Vector_append(lean_object* v_00_u03b1_969_, lean_object* v_n_970_, lean_object* v_m_971_, lean_object* v_xs_972_, lean_object* v_ys_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Array_append___redArg(v_xs_972_, v_ys_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___boxed(lean_object* v_00_u03b1_975_, lean_object* v_n_976_, lean_object* v_m_977_, lean_object* v_xs_978_, lean_object* v_ys_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Vector_append(v_00_u03b1_975_, v_n_976_, v_m_977_, v_xs_978_, v_ys_979_);
lean_dec_ref(v_ys_979_);
lean_dec(v_m_977_);
lean_dec(v_n_976_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat___redArg(lean_object* v_n_981_, lean_object* v_m_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_983_, 0, lean_box(0));
lean_closure_set(v___x_983_, 1, v_n_981_);
lean_closure_set(v___x_983_, 2, v_m_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat(lean_object* v_00_u03b1_984_, lean_object* v_n_985_, lean_object* v_m_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_987_, 0, lean_box(0));
lean_closure_set(v___x_987_, 1, v_n_985_);
lean_closure_set(v___x_987_, 2, v_m_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg(lean_object* v_xs_988_){
_start:
{
lean_inc_ref(v_xs_988_);
return v_xs_988_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg___boxed(lean_object* v_xs_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Vector_cast___redArg(v_xs_989_);
lean_dec_ref(v_xs_989_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast(lean_object* v_n_991_, lean_object* v_m_992_, lean_object* v_00_u03b1_993_, lean_object* v_h_994_, lean_object* v_xs_995_){
_start:
{
lean_inc_ref(v_xs_995_);
return v_xs_995_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___boxed(lean_object* v_n_996_, lean_object* v_m_997_, lean_object* v_00_u03b1_998_, lean_object* v_h_999_, lean_object* v_xs_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Vector_cast(v_n_996_, v_m_997_, v_00_u03b1_998_, v_h_999_, v_xs_1000_);
lean_dec_ref(v_xs_1000_);
lean_dec(v_m_997_);
lean_dec(v_n_996_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg(lean_object* v_xs_1002_, lean_object* v_start_1003_, lean_object* v_stop_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Array_extract___redArg(v_xs_1002_, v_start_1003_, v_stop_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg___boxed(lean_object* v_xs_1006_, lean_object* v_start_1007_, lean_object* v_stop_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Vector_extract___redArg(v_xs_1006_, v_start_1007_, v_stop_1008_);
lean_dec_ref(v_xs_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract(lean_object* v_00_u03b1_1010_, lean_object* v_n_1011_, lean_object* v_xs_1012_, lean_object* v_start_1013_, lean_object* v_stop_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Array_extract___redArg(v_xs_1012_, v_start_1013_, v_stop_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___boxed(lean_object* v_00_u03b1_1016_, lean_object* v_n_1017_, lean_object* v_xs_1018_, lean_object* v_start_1019_, lean_object* v_stop_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Vector_extract(v_00_u03b1_1016_, v_n_1017_, v_xs_1018_, v_start_1019_, v_stop_1020_);
lean_dec_ref(v_xs_1018_);
lean_dec(v_n_1017_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg(lean_object* v_n_1022_, lean_object* v_xs_1023_, lean_object* v_i_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = l_Array_extract___redArg(v_xs_1023_, v___x_1025_, v_i_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg___boxed(lean_object* v_n_1027_, lean_object* v_xs_1028_, lean_object* v_i_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Vector_take___redArg(v_n_1027_, v_xs_1028_, v_i_1029_);
lean_dec_ref(v_xs_1028_);
lean_dec(v_n_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Vector_take(lean_object* v_00_u03b1_1031_, lean_object* v_n_1032_, lean_object* v_xs_1033_, lean_object* v_i_1034_){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = l_Array_extract___redArg(v_xs_1033_, v___x_1035_, v_i_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___boxed(lean_object* v_00_u03b1_1037_, lean_object* v_n_1038_, lean_object* v_xs_1039_, lean_object* v_i_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Vector_take(v_00_u03b1_1037_, v_n_1038_, v_xs_1039_, v_i_1040_);
lean_dec_ref(v_xs_1039_);
lean_dec(v_n_1038_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg(lean_object* v_xs_1042_, lean_object* v_i_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_array_get_size(v_xs_1042_);
v___x_1045_ = l_Array_extract___redArg(v_xs_1042_, v_i_1043_, v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg___boxed(lean_object* v_xs_1046_, lean_object* v_i_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Vector_drop___redArg(v_xs_1046_, v_i_1047_);
lean_dec_ref(v_xs_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop(lean_object* v_00_u03b1_1049_, lean_object* v_n_1050_, lean_object* v_xs_1051_, lean_object* v_i_1052_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_array_get_size(v_xs_1051_);
v___x_1054_ = l_Array_extract___redArg(v_xs_1051_, v_i_1052_, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___boxed(lean_object* v_00_u03b1_1055_, lean_object* v_n_1056_, lean_object* v_xs_1057_, lean_object* v_i_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Vector_drop(v_00_u03b1_1055_, v_n_1056_, v_xs_1057_, v_i_1058_);
lean_dec_ref(v_xs_1057_);
lean_dec(v_n_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg(lean_object* v_xs_1060_, lean_object* v_i_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Array_shrink___redArg(v_xs_1060_, v_i_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg___boxed(lean_object* v_xs_1063_, lean_object* v_i_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Vector_shrink___redArg(v_xs_1063_, v_i_1064_);
lean_dec(v_i_1064_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink(lean_object* v_00_u03b1_1066_, lean_object* v_n_1067_, lean_object* v_xs_1068_, lean_object* v_i_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Array_shrink___redArg(v_xs_1068_, v_i_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_n_1072_, lean_object* v_xs_1073_, lean_object* v_i_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Vector_shrink(v_00_u03b1_1071_, v_n_1072_, v_xs_1073_, v_i_1074_);
lean_dec(v_i_1074_);
lean_dec(v_n_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg___lam__0(lean_object* v_f_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_apply_1(v_f_1076_, v_x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg(lean_object* v_f_1079_, lean_object* v_xs_1080_){
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
LEAN_EXPORT lean_object* l_Vector_map(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_n_1088_, lean_object* v_f_1089_, lean_object* v_xs_1090_){
_start:
{
lean_object* v___f_1091_; lean_object* v___x_1092_; size_t v_sz_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
v___f_1091_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1091_, 0, v_f_1089_);
v___x_1092_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1093_ = lean_array_size(v_xs_1090_);
v___x_1094_ = ((size_t)0ULL);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1092_, v___f_1091_, v_sz_1093_, v___x_1094_, v_xs_1090_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___boxed(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_n_1098_, lean_object* v_f_1099_, lean_object* v_xs_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Vector_map(v_00_u03b1_1096_, v_00_u03b2_1097_, v_n_1098_, v_f_1099_, v_xs_1100_);
lean_dec(v_n_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg___lam__0(lean_object* v_f_1102_, lean_object* v_i_1103_, lean_object* v_a_1104_, lean_object* v_x_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_apply_2(v_f_1102_, v_i_1103_, v_a_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg(lean_object* v_f_1107_, lean_object* v_xs_1108_){
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
LEAN_EXPORT lean_object* l_Vector_mapIdx(lean_object* v_00_u03b1_1114_, lean_object* v_00_u03b2_1115_, lean_object* v_n_1116_, lean_object* v_f_1117_, lean_object* v_xs_1118_){
_start:
{
lean_object* v___f_1119_; lean_object* v___x_1120_; size_t v_sz_1121_; size_t v___x_1122_; lean_object* v___x_1123_; 
v___f_1119_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1119_, 0, v_f_1117_);
v___x_1120_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1121_ = lean_array_size(v_xs_1118_);
v___x_1122_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1118_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1120_, v_xs_1118_, v___f_1119_, v_sz_1121_, v___x_1122_, v_xs_1118_);
lean_dec_ref(v_xs_1118_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___boxed(lean_object* v_00_u03b1_1124_, lean_object* v_00_u03b2_1125_, lean_object* v_n_1126_, lean_object* v_f_1127_, lean_object* v_xs_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Vector_mapIdx(v_00_u03b1_1124_, v_00_u03b2_1125_, v_n_1126_, v_f_1127_, v_xs_1128_);
lean_dec(v_n_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg___lam__0(lean_object* v_f_1130_, lean_object* v_x1_1131_, lean_object* v_x2_1132_, lean_object* v_x3_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_apply_3(v_f_1130_, v_x1_1131_, v_x2_1132_, lean_box(0));
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg(lean_object* v_xs_1135_, lean_object* v_f_1136_){
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
LEAN_EXPORT lean_object* l_Vector_mapFinIdx(lean_object* v_00_u03b1_1142_, lean_object* v_n_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_xs_1145_, lean_object* v_f_1146_){
_start:
{
lean_object* v___f_1147_; lean_object* v___x_1148_; size_t v_sz_1149_; size_t v___x_1150_; lean_object* v___x_1151_; 
v___f_1147_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1147_, 0, v_f_1146_);
v___x_1148_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1149_ = lean_array_size(v_xs_1145_);
v___x_1150_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1145_);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1148_, v_xs_1145_, v___f_1147_, v_sz_1149_, v___x_1150_, v_xs_1145_);
lean_dec_ref(v_xs_1145_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___boxed(lean_object* v_00_u03b1_1152_, lean_object* v_n_1153_, lean_object* v_00_u03b2_1154_, lean_object* v_xs_1155_, lean_object* v_f_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Vector_mapFinIdx(v_00_u03b1_1152_, v_n_1153_, v_00_u03b2_1154_, v_xs_1155_, v_f_1156_);
lean_dec(v_n_1153_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(lean_object* v_k_1158_, lean_object* v_acc_1159_, lean_object* v_n_1160_, lean_object* v_inst_1161_, lean_object* v_f_1162_, lean_object* v_xs_1163_, lean_object* v_____do__lift_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(v_k_1158_, v_acc_1159_, v_n_1160_, v_inst_1161_, v_f_1162_, v_xs_1163_, v_____do__lift_1164_);
lean_dec(v_k_1158_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(lean_object* v_n_1166_, lean_object* v_inst_1167_, lean_object* v_f_1168_, lean_object* v_xs_1169_, lean_object* v_k_1170_, lean_object* v_acc_1171_){
_start:
{
lean_object* v_toApplicative_1172_; lean_object* v_toBind_1173_; lean_object* v_toPure_1174_; uint8_t v___x_1175_; 
v_toApplicative_1172_ = lean_ctor_get(v_inst_1167_, 0);
v_toBind_1173_ = lean_ctor_get(v_inst_1167_, 1);
lean_inc(v_toBind_1173_);
v_toPure_1174_ = lean_ctor_get(v_toApplicative_1172_, 1);
v___x_1175_ = lean_nat_dec_lt(v_k_1170_, v_n_1166_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
lean_inc(v_toPure_1174_);
lean_dec(v_toBind_1173_);
lean_dec(v_k_1170_);
lean_dec_ref(v_xs_1169_);
lean_dec(v_f_1168_);
lean_dec_ref(v_inst_1167_);
lean_dec(v_n_1166_);
v___x_1176_ = lean_apply_2(v_toPure_1174_, lean_box(0), v_acc_1171_);
return v___x_1176_;
}
else
{
lean_object* v___f_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_inc_ref(v_xs_1169_);
lean_inc(v_f_1168_);
lean_inc(v_k_1170_);
v___f_1177_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1177_, 0, v_k_1170_);
lean_closure_set(v___f_1177_, 1, v_acc_1171_);
lean_closure_set(v___f_1177_, 2, v_n_1166_);
lean_closure_set(v___f_1177_, 3, v_inst_1167_);
lean_closure_set(v___f_1177_, 4, v_f_1168_);
lean_closure_set(v___f_1177_, 5, v_xs_1169_);
v___x_1178_ = lean_array_fget(v_xs_1169_, v_k_1170_);
lean_dec(v_k_1170_);
lean_dec_ref(v_xs_1169_);
v___x_1179_ = lean_apply_1(v_f_1168_, v___x_1178_);
v___x_1180_ = lean_apply_4(v_toBind_1173_, lean_box(0), lean_box(0), v___x_1179_, v___f_1177_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(lean_object* v_k_1181_, lean_object* v_acc_1182_, lean_object* v_n_1183_, lean_object* v_inst_1184_, lean_object* v_f_1185_, lean_object* v_xs_1186_, lean_object* v_____do__lift_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1188_ = lean_unsigned_to_nat(1u);
v___x_1189_ = lean_nat_add(v_k_1181_, v___x_1188_);
v___x_1190_ = lean_array_push(v_acc_1182_, v_____do__lift_1187_);
v___x_1191_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1183_, v_inst_1184_, v_f_1185_, v_xs_1186_, v___x_1189_, v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(lean_object* v_m_1192_, lean_object* v_00_u03b1_1193_, lean_object* v_00_u03b2_1194_, lean_object* v_n_1195_, lean_object* v_inst_1196_, lean_object* v_f_1197_, lean_object* v_xs_1198_, lean_object* v_k_1199_, lean_object* v_h_1200_, lean_object* v_acc_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1195_, v_inst_1196_, v_f_1197_, v_xs_1198_, v_k_1199_, v_acc_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM___redArg(lean_object* v_n_1205_, lean_object* v_inst_1206_, lean_object* v_f_1207_, lean_object* v_xs_1208_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1211_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1205_, v_inst_1206_, v_f_1207_, v_xs_1208_, v___x_1209_, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM(lean_object* v_m_1212_, lean_object* v_00_u03b1_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_n_1215_, lean_object* v_inst_1216_, lean_object* v_f_1217_, lean_object* v_xs_1218_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1221_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1215_, v_inst_1216_, v_f_1217_, v_xs_1218_, v___x_1219_, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg___lam__0(lean_object* v_f_1222_, lean_object* v_x_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_apply_1(v_f_1222_, v___y_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg(lean_object* v_inst_1226_, lean_object* v_xs_1227_, lean_object* v_f_1228_){
_start:
{
lean_object* v_toApplicative_1229_; lean_object* v_toPure_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_toApplicative_1229_ = lean_ctor_get(v_inst_1226_, 0);
v_toPure_1230_ = lean_ctor_get(v_toApplicative_1229_, 1);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = lean_array_get_size(v_xs_1227_);
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_nat_dec_lt(v___x_1231_, v___x_1232_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_inc(v_toPure_1230_);
lean_dec(v_f_1228_);
lean_dec_ref(v_xs_1227_);
lean_dec_ref(v_inst_1226_);
v___x_1235_ = lean_apply_2(v_toPure_1230_, lean_box(0), v___x_1233_);
return v___x_1235_;
}
else
{
lean_object* v___f_1236_; uint8_t v___x_1237_; 
v___f_1236_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1236_, 0, v_f_1228_);
v___x_1237_ = lean_nat_dec_le(v___x_1232_, v___x_1232_);
if (v___x_1237_ == 0)
{
if (v___x_1234_ == 0)
{
lean_object* v___x_1238_; 
lean_inc(v_toPure_1230_);
lean_dec_ref(v___f_1236_);
lean_dec_ref(v_xs_1227_);
lean_dec_ref(v_inst_1226_);
v___x_1238_ = lean_apply_2(v_toPure_1230_, lean_box(0), v___x_1233_);
return v___x_1238_;
}
else
{
size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = ((size_t)0ULL);
v___x_1240_ = lean_usize_of_nat(v___x_1232_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1226_, v___f_1236_, v_xs_1227_, v___x_1239_, v___x_1240_, v___x_1233_);
return v___x_1241_;
}
}
else
{
size_t v___x_1242_; size_t v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = ((size_t)0ULL);
v___x_1243_ = lean_usize_of_nat(v___x_1232_);
v___x_1244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1226_, v___f_1236_, v_xs_1227_, v___x_1242_, v___x_1243_, v___x_1233_);
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM(lean_object* v_m_1245_, lean_object* v_00_u03b1_1246_, lean_object* v_n_1247_, lean_object* v_inst_1248_, lean_object* v_xs_1249_, lean_object* v_f_1250_){
_start:
{
lean_object* v_toApplicative_1251_; lean_object* v_toPure_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_toApplicative_1251_ = lean_ctor_get(v_inst_1248_, 0);
v_toPure_1252_ = lean_ctor_get(v_toApplicative_1251_, 1);
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = lean_array_get_size(v_xs_1249_);
v___x_1255_ = lean_box(0);
v___x_1256_ = lean_nat_dec_lt(v___x_1253_, v___x_1254_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
lean_inc(v_toPure_1252_);
lean_dec(v_f_1250_);
lean_dec_ref(v_xs_1249_);
lean_dec_ref(v_inst_1248_);
v___x_1257_ = lean_apply_2(v_toPure_1252_, lean_box(0), v___x_1255_);
return v___x_1257_;
}
else
{
lean_object* v___f_1258_; uint8_t v___x_1259_; 
v___f_1258_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1258_, 0, v_f_1250_);
v___x_1259_ = lean_nat_dec_le(v___x_1254_, v___x_1254_);
if (v___x_1259_ == 0)
{
if (v___x_1256_ == 0)
{
lean_object* v___x_1260_; 
lean_inc(v_toPure_1252_);
lean_dec_ref(v___f_1258_);
lean_dec_ref(v_xs_1249_);
lean_dec_ref(v_inst_1248_);
v___x_1260_ = lean_apply_2(v_toPure_1252_, lean_box(0), v___x_1255_);
return v___x_1260_;
}
else
{
size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = ((size_t)0ULL);
v___x_1262_ = lean_usize_of_nat(v___x_1254_);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1248_, v___f_1258_, v_xs_1249_, v___x_1261_, v___x_1262_, v___x_1255_);
return v___x_1263_;
}
}
else
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = ((size_t)0ULL);
v___x_1265_ = lean_usize_of_nat(v___x_1254_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1248_, v___f_1258_, v_xs_1249_, v___x_1264_, v___x_1265_, v___x_1255_);
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM___boxed(lean_object* v_m_1267_, lean_object* v_00_u03b1_1268_, lean_object* v_n_1269_, lean_object* v_inst_1270_, lean_object* v_xs_1271_, lean_object* v_f_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Vector_forM(v_m_1267_, v_00_u03b1_1268_, v_n_1269_, v_inst_1270_, v_xs_1271_, v_f_1272_);
lean_dec(v_n_1269_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(lean_object* v_i_1274_, lean_object* v_acc_1275_, lean_object* v_n_1276_, lean_object* v_inst_1277_, lean_object* v_xs_1278_, lean_object* v_f_1279_, lean_object* v_____do__lift_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(v_i_1274_, v_acc_1275_, v_n_1276_, v_inst_1277_, v_xs_1278_, v_f_1279_, v_____do__lift_1280_);
lean_dec_ref(v_____do__lift_1280_);
lean_dec(v_i_1274_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(lean_object* v_n_1282_, lean_object* v_inst_1283_, lean_object* v_xs_1284_, lean_object* v_f_1285_, lean_object* v_i_1286_, lean_object* v_acc_1287_){
_start:
{
lean_object* v_toApplicative_1288_; lean_object* v_toBind_1289_; lean_object* v_toPure_1290_; uint8_t v___x_1291_; 
v_toApplicative_1288_ = lean_ctor_get(v_inst_1283_, 0);
v_toBind_1289_ = lean_ctor_get(v_inst_1283_, 1);
lean_inc(v_toBind_1289_);
v_toPure_1290_ = lean_ctor_get(v_toApplicative_1288_, 1);
v___x_1291_ = lean_nat_dec_lt(v_i_1286_, v_n_1282_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
lean_inc(v_toPure_1290_);
lean_dec(v_toBind_1289_);
lean_dec(v_i_1286_);
lean_dec(v_f_1285_);
lean_dec_ref(v_xs_1284_);
lean_dec_ref(v_inst_1283_);
lean_dec(v_n_1282_);
v___x_1292_ = lean_apply_2(v_toPure_1290_, lean_box(0), v_acc_1287_);
return v___x_1292_;
}
else
{
lean_object* v___f_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_inc(v_f_1285_);
lean_inc_ref(v_xs_1284_);
lean_inc(v_i_1286_);
v___f_1293_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1293_, 0, v_i_1286_);
lean_closure_set(v___f_1293_, 1, v_acc_1287_);
lean_closure_set(v___f_1293_, 2, v_n_1282_);
lean_closure_set(v___f_1293_, 3, v_inst_1283_);
lean_closure_set(v___f_1293_, 4, v_xs_1284_);
lean_closure_set(v___f_1293_, 5, v_f_1285_);
v___x_1294_ = lean_array_fget(v_xs_1284_, v_i_1286_);
lean_dec(v_i_1286_);
lean_dec_ref(v_xs_1284_);
v___x_1295_ = lean_apply_1(v_f_1285_, v___x_1294_);
v___x_1296_ = lean_apply_4(v_toBind_1289_, lean_box(0), lean_box(0), v___x_1295_, v___f_1293_);
return v___x_1296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(lean_object* v_i_1297_, lean_object* v_acc_1298_, lean_object* v_n_1299_, lean_object* v_inst_1300_, lean_object* v_xs_1301_, lean_object* v_f_1302_, lean_object* v_____do__lift_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_nat_add(v_i_1297_, v___x_1304_);
v___x_1306_ = l_Array_append___redArg(v_acc_1298_, v_____do__lift_1303_);
v___x_1307_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1299_, v_inst_1300_, v_xs_1301_, v_f_1302_, v___x_1305_, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(lean_object* v_m_1308_, lean_object* v_00_u03b1_1309_, lean_object* v_n_1310_, lean_object* v_00_u03b2_1311_, lean_object* v_k_1312_, lean_object* v_inst_1313_, lean_object* v_xs_1314_, lean_object* v_f_1315_, lean_object* v_i_1316_, lean_object* v_h_1317_, lean_object* v_acc_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1310_, v_inst_1313_, v_xs_1314_, v_f_1315_, v_i_1316_, v_acc_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(lean_object* v_m_1320_, lean_object* v_00_u03b1_1321_, lean_object* v_n_1322_, lean_object* v_00_u03b2_1323_, lean_object* v_k_1324_, lean_object* v_inst_1325_, lean_object* v_xs_1326_, lean_object* v_f_1327_, lean_object* v_i_1328_, lean_object* v_h_1329_, lean_object* v_acc_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(v_m_1320_, v_00_u03b1_1321_, v_n_1322_, v_00_u03b2_1323_, v_k_1324_, v_inst_1325_, v_xs_1326_, v_f_1327_, v_i_1328_, v_h_1329_, v_acc_1330_);
lean_dec(v_k_1324_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___redArg(lean_object* v_n_1332_, lean_object* v_inst_1333_, lean_object* v_xs_1334_, lean_object* v_f_1335_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1338_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1332_, v_inst_1333_, v_xs_1334_, v_f_1335_, v___x_1336_, v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM(lean_object* v_m_1339_, lean_object* v_00_u03b1_1340_, lean_object* v_n_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_k_1343_, lean_object* v_inst_1344_, lean_object* v_xs_1345_, lean_object* v_f_1346_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1349_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1341_, v_inst_1344_, v_xs_1345_, v_f_1346_, v___x_1347_, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___boxed(lean_object* v_m_1350_, lean_object* v_00_u03b1_1351_, lean_object* v_n_1352_, lean_object* v_00_u03b2_1353_, lean_object* v_k_1354_, lean_object* v_inst_1355_, lean_object* v_xs_1356_, lean_object* v_f_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Vector_flatMapM(v_m_1350_, v_00_u03b1_1351_, v_n_1352_, v_00_u03b2_1353_, v_k_1354_, v_inst_1355_, v_xs_1356_, v_f_1357_);
lean_dec(v_k_1354_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1359_, lean_object* v_ys_1360_, lean_object* v_inst_1361_, lean_object* v_xs_1362_, lean_object* v_f_1363_, lean_object* v_n_1364_, lean_object* v_____do__lift_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Vector_mapFinIdxM_map___redArg___lam__0(v_j_1359_, v_ys_1360_, v_inst_1361_, v_xs_1362_, v_f_1363_, v_n_1364_, v_____do__lift_1365_);
lean_dec(v_n_1364_);
lean_dec(v_j_1359_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg(lean_object* v_inst_1367_, lean_object* v_xs_1368_, lean_object* v_f_1369_, lean_object* v_i_1370_, lean_object* v_j_1371_, lean_object* v_ys_1372_){
_start:
{
lean_object* v_toApplicative_1373_; lean_object* v_toBind_1374_; lean_object* v_toPure_1375_; lean_object* v_zero_1376_; uint8_t v_isZero_1377_; 
v_toApplicative_1373_ = lean_ctor_get(v_inst_1367_, 0);
v_toBind_1374_ = lean_ctor_get(v_inst_1367_, 1);
lean_inc(v_toBind_1374_);
v_toPure_1375_ = lean_ctor_get(v_toApplicative_1373_, 1);
v_zero_1376_ = lean_unsigned_to_nat(0u);
v_isZero_1377_ = lean_nat_dec_eq(v_i_1370_, v_zero_1376_);
if (v_isZero_1377_ == 1)
{
lean_object* v___x_1378_; 
lean_inc(v_toPure_1375_);
lean_dec(v_toBind_1374_);
lean_dec(v_j_1371_);
lean_dec(v_f_1369_);
lean_dec_ref(v_xs_1368_);
lean_dec_ref(v_inst_1367_);
v___x_1378_ = lean_apply_2(v_toPure_1375_, lean_box(0), v_ys_1372_);
return v___x_1378_;
}
else
{
lean_object* v_one_1379_; lean_object* v_n_1380_; lean_object* v___f_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_one_1379_ = lean_unsigned_to_nat(1u);
v_n_1380_ = lean_nat_sub(v_i_1370_, v_one_1379_);
lean_inc(v_f_1369_);
lean_inc_ref(v_xs_1368_);
lean_inc(v_j_1371_);
v___f_1381_ = lean_alloc_closure((void*)(l_Vector_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1381_, 0, v_j_1371_);
lean_closure_set(v___f_1381_, 1, v_ys_1372_);
lean_closure_set(v___f_1381_, 2, v_inst_1367_);
lean_closure_set(v___f_1381_, 3, v_xs_1368_);
lean_closure_set(v___f_1381_, 4, v_f_1369_);
lean_closure_set(v___f_1381_, 5, v_n_1380_);
v___x_1382_ = lean_array_fget(v_xs_1368_, v_j_1371_);
lean_dec_ref(v_xs_1368_);
v___x_1383_ = lean_apply_3(v_f_1369_, v_j_1371_, v___x_1382_, lean_box(0));
v___x_1384_ = lean_apply_4(v_toBind_1374_, lean_box(0), lean_box(0), v___x_1383_, v___f_1381_);
return v___x_1384_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1385_, lean_object* v_ys_1386_, lean_object* v_inst_1387_, lean_object* v_xs_1388_, lean_object* v_f_1389_, lean_object* v_n_1390_, lean_object* v_____do__lift_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1392_ = lean_unsigned_to_nat(1u);
v___x_1393_ = lean_nat_add(v_j_1385_, v___x_1392_);
v___x_1394_ = lean_array_push(v_ys_1386_, v_____do__lift_1391_);
v___x_1395_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1387_, v_xs_1388_, v_f_1389_, v_n_1390_, v___x_1393_, v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1396_, lean_object* v_xs_1397_, lean_object* v_f_1398_, lean_object* v_i_1399_, lean_object* v_j_1400_, lean_object* v_ys_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1396_, v_xs_1397_, v_f_1398_, v_i_1399_, v_j_1400_, v_ys_1401_);
lean_dec(v_i_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map(lean_object* v_n_1403_, lean_object* v_00_u03b1_1404_, lean_object* v_00_u03b2_1405_, lean_object* v_m_1406_, lean_object* v_inst_1407_, lean_object* v_xs_1408_, lean_object* v_f_1409_, lean_object* v_i_1410_, lean_object* v_j_1411_, lean_object* v_inv_1412_, lean_object* v_ys_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1407_, v_xs_1408_, v_f_1409_, v_i_1410_, v_j_1411_, v_ys_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___boxed(lean_object* v_n_1415_, lean_object* v_00_u03b1_1416_, lean_object* v_00_u03b2_1417_, lean_object* v_m_1418_, lean_object* v_inst_1419_, lean_object* v_xs_1420_, lean_object* v_f_1421_, lean_object* v_i_1422_, lean_object* v_j_1423_, lean_object* v_inv_1424_, lean_object* v_ys_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Vector_mapFinIdxM_map(v_n_1415_, v_00_u03b1_1416_, v_00_u03b2_1417_, v_m_1418_, v_inst_1419_, v_xs_1420_, v_f_1421_, v_i_1422_, v_j_1423_, v_inv_1424_, v_ys_1425_);
lean_dec(v_i_1422_);
lean_dec(v_n_1415_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg(lean_object* v_n_1427_, lean_object* v_inst_1428_, lean_object* v_xs_1429_, lean_object* v_f_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1433_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1428_, v_xs_1429_, v_f_1430_, v_n_1427_, v___x_1431_, v___x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg___boxed(lean_object* v_n_1434_, lean_object* v_inst_1435_, lean_object* v_xs_1436_, lean_object* v_f_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Vector_mapFinIdxM___redArg(v_n_1434_, v_inst_1435_, v_xs_1436_, v_f_1437_);
lean_dec(v_n_1434_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM(lean_object* v_n_1439_, lean_object* v_00_u03b1_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_m_1442_, lean_object* v_inst_1443_, lean_object* v_xs_1444_, lean_object* v_f_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1448_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1443_, v_xs_1444_, v_f_1445_, v_n_1439_, v___x_1446_, v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___boxed(lean_object* v_n_1449_, lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_m_1452_, lean_object* v_inst_1453_, lean_object* v_xs_1454_, lean_object* v_f_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Vector_mapFinIdxM(v_n_1449_, v_00_u03b1_1450_, v_00_u03b2_1451_, v_m_1452_, v_inst_1453_, v_xs_1454_, v_f_1455_);
lean_dec(v_n_1449_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg(lean_object* v_n_1457_, lean_object* v_inst_1458_, lean_object* v_f_1459_, lean_object* v_xs_1460_){
_start:
{
lean_object* v___f_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___f_1461_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1461_, 0, v_f_1459_);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1464_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1458_, v_xs_1460_, v___f_1461_, v_n_1457_, v___x_1462_, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg___boxed(lean_object* v_n_1465_, lean_object* v_inst_1466_, lean_object* v_f_1467_, lean_object* v_xs_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Vector_mapIdxM___redArg(v_n_1465_, v_inst_1466_, v_f_1467_, v_xs_1468_);
lean_dec(v_n_1465_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM(lean_object* v_n_1470_, lean_object* v_00_u03b1_1471_, lean_object* v_00_u03b2_1472_, lean_object* v_m_1473_, lean_object* v_inst_1474_, lean_object* v_f_1475_, lean_object* v_xs_1476_){
_start:
{
lean_object* v___f_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___f_1477_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1477_, 0, v_f_1475_);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1480_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1474_, v_xs_1476_, v___f_1477_, v_n_1470_, v___x_1478_, v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___boxed(lean_object* v_n_1481_, lean_object* v_00_u03b1_1482_, lean_object* v_00_u03b2_1483_, lean_object* v_m_1484_, lean_object* v_inst_1485_, lean_object* v_f_1486_, lean_object* v_xs_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Vector_mapIdxM(v_n_1481_, v_00_u03b1_1482_, v_00_u03b2_1483_, v_m_1484_, v_inst_1485_, v_f_1486_, v_xs_1487_);
lean_dec(v_n_1481_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___redArg(lean_object* v_inst_1489_, lean_object* v_f_1490_, lean_object* v_xs_1491_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1489_, v_f_1490_, v_xs_1491_, v___x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM(lean_object* v_00_u03b2_1494_, lean_object* v_n_1495_, lean_object* v_00_u03b1_1496_, lean_object* v_m_1497_, lean_object* v_inst_1498_, lean_object* v_f_1499_, lean_object* v_xs_1500_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1498_, v_f_1499_, v_xs_1500_, v___x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___boxed(lean_object* v_00_u03b2_1503_, lean_object* v_n_1504_, lean_object* v_00_u03b1_1505_, lean_object* v_m_1506_, lean_object* v_inst_1507_, lean_object* v_f_1508_, lean_object* v_xs_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Vector_firstM(v_00_u03b2_1503_, v_n_1504_, v_00_u03b1_1505_, v_m_1506_, v_inst_1507_, v_f_1508_, v_xs_1509_);
lean_dec(v_n_1504_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0(lean_object* v_x_1511_){
_start:
{
lean_inc_ref(v_x_1511_);
return v_x_1511_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0___boxed(lean_object* v_x_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Vector_flatten___redArg___lam__0(v_x_1512_);
lean_dec_ref(v_x_1512_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg(lean_object* v_xs_1518_){
_start:
{
lean_object* v___f_1519_; lean_object* v___x_1520_; size_t v_sz_1521_; size_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___f_1519_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1520_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1521_ = lean_array_size(v_xs_1518_);
v___x_1522_ = ((size_t)0ULL);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1520_, v___f_1519_, v_sz_1521_, v___x_1522_, v_xs_1518_);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1526_ = lean_array_get_size(v___x_1523_);
v___x_1527_ = lean_nat_dec_lt(v___x_1524_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_dec(v___x_1523_);
return v___x_1525_;
}
else
{
lean_object* v___f_1528_; size_t v___x_1529_; lean_object* v___x_1530_; 
v___f_1528_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1529_ = lean_usize_of_nat(v___x_1526_);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1520_, v___f_1528_, v___x_1523_, v___x_1522_, v___x_1529_, v___x_1525_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten(lean_object* v_00_u03b1_1531_, lean_object* v_n_1532_, lean_object* v_m_1533_, lean_object* v_xs_1534_){
_start:
{
lean_object* v___f_1535_; lean_object* v___x_1536_; size_t v_sz_1537_; size_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___f_1535_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1536_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1537_ = lean_array_size(v_xs_1534_);
v___x_1538_ = ((size_t)0ULL);
v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1536_, v___f_1535_, v_sz_1537_, v___x_1538_, v_xs_1534_);
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1542_ = lean_array_get_size(v___x_1539_);
v___x_1543_ = lean_nat_dec_lt(v___x_1540_, v___x_1542_);
if (v___x_1543_ == 0)
{
lean_dec(v___x_1539_);
return v___x_1541_;
}
else
{
lean_object* v___f_1544_; size_t v___x_1545_; lean_object* v___x_1546_; 
v___f_1544_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1545_ = lean_usize_of_nat(v___x_1542_);
v___x_1546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1536_, v___f_1544_, v___x_1539_, v___x_1538_, v___x_1545_, v___x_1541_);
return v___x_1546_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___boxed(lean_object* v_00_u03b1_1547_, lean_object* v_n_1548_, lean_object* v_m_1549_, lean_object* v_xs_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Vector_flatten(v_00_u03b1_1547_, v_n_1548_, v_m_1549_, v_xs_1550_);
lean_dec(v_m_1549_);
lean_dec(v_n_1548_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg___lam__0(lean_object* v_f_1552_, lean_object* v_x1_1553_, lean_object* v_x2_1554_){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_apply_1(v_f_1552_, v_x2_1554_);
v___x_1556_ = l_Array_append___redArg(v_x1_1553_, v___x_1555_);
lean_dec_ref(v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg(lean_object* v_xs_1557_, lean_object* v_f_1558_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1561_ = lean_array_get_size(v_xs_1557_);
v___x_1562_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1563_ = lean_nat_dec_lt(v___x_1559_, v___x_1561_);
if (v___x_1563_ == 0)
{
lean_dec_ref(v_f_1558_);
lean_dec_ref(v_xs_1557_);
return v___x_1560_;
}
else
{
lean_object* v___f_1564_; size_t v___x_1565_; size_t v___x_1566_; lean_object* v___x_1567_; 
v___f_1564_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1564_, 0, v_f_1558_);
v___x_1565_ = ((size_t)0ULL);
v___x_1566_ = lean_usize_of_nat(v___x_1561_);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1562_, v___f_1564_, v_xs_1557_, v___x_1565_, v___x_1566_, v___x_1560_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap(lean_object* v_00_u03b1_1568_, lean_object* v_n_1569_, lean_object* v_00_u03b2_1570_, lean_object* v_m_1571_, lean_object* v_xs_1572_, lean_object* v_f_1573_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1576_ = lean_array_get_size(v_xs_1572_);
v___x_1577_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1578_ = lean_nat_dec_lt(v___x_1574_, v___x_1576_);
if (v___x_1578_ == 0)
{
lean_dec_ref(v_f_1573_);
lean_dec_ref(v_xs_1572_);
return v___x_1575_;
}
else
{
lean_object* v___f_1579_; size_t v___x_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
v___f_1579_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1579_, 0, v_f_1573_);
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = lean_usize_of_nat(v___x_1576_);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1577_, v___f_1579_, v_xs_1572_, v___x_1580_, v___x_1581_, v___x_1575_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_n_1584_, lean_object* v_00_u03b2_1585_, lean_object* v_m_1586_, lean_object* v_xs_1587_, lean_object* v_f_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Vector_flatMap(v_00_u03b1_1583_, v_n_1584_, v_00_u03b2_1585_, v_m_1586_, v_xs_1587_, v_f_1588_);
lean_dec(v_m_1586_);
lean_dec(v_n_1584_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg(lean_object* v_xs_1590_, lean_object* v_k_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Array_zipIdx___redArg(v_xs_1590_, v_k_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg___boxed(lean_object* v_xs_1593_, lean_object* v_k_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Vector_zipIdx___redArg(v_xs_1593_, v_k_1594_);
lean_dec(v_k_1594_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx(lean_object* v_00_u03b1_1596_, lean_object* v_n_1597_, lean_object* v_xs_1598_, lean_object* v_k_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Array_zipIdx___redArg(v_xs_1598_, v_k_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___boxed(lean_object* v_00_u03b1_1601_, lean_object* v_n_1602_, lean_object* v_xs_1603_, lean_object* v_k_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Vector_zipIdx(v_00_u03b1_1601_, v_n_1602_, v_xs_1603_, v_k_1604_);
lean_dec(v_k_1604_);
lean_dec(v_n_1602_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg(lean_object* v_as_1606_, lean_object* v_bs_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Array_zip___redArg(v_as_1606_, v_bs_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg___boxed(lean_object* v_as_1609_, lean_object* v_bs_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Vector_zip___redArg(v_as_1609_, v_bs_1610_);
lean_dec_ref(v_bs_1610_);
lean_dec_ref(v_as_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip(lean_object* v_00_u03b1_1612_, lean_object* v_n_1613_, lean_object* v_00_u03b2_1614_, lean_object* v_as_1615_, lean_object* v_bs_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Array_zip___redArg(v_as_1615_, v_bs_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___boxed(lean_object* v_00_u03b1_1618_, lean_object* v_n_1619_, lean_object* v_00_u03b2_1620_, lean_object* v_as_1621_, lean_object* v_bs_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Vector_zip(v_00_u03b1_1618_, v_n_1619_, v_00_u03b2_1620_, v_as_1621_, v_bs_1622_);
lean_dec_ref(v_bs_1622_);
lean_dec_ref(v_as_1621_);
lean_dec(v_n_1619_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___redArg(lean_object* v_f_1624_, lean_object* v_as_1625_, lean_object* v_bs_1626_){
_start:
{
lean_object* v___f_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___f_1627_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1627_, 0, v_f_1624_);
v___x_1628_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1631_ = l_Array_zipWithMAux___redArg(v___x_1628_, v_as_1625_, v_bs_1626_, v___f_1627_, v___x_1629_, v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith(lean_object* v_00_u03b1_1632_, lean_object* v_00_u03b2_1633_, lean_object* v_00_u03c6_1634_, lean_object* v_n_1635_, lean_object* v_f_1636_, lean_object* v_as_1637_, lean_object* v_bs_1638_){
_start:
{
lean_object* v___f_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___f_1639_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1639_, 0, v_f_1636_);
v___x_1640_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1641_ = lean_unsigned_to_nat(0u);
v___x_1642_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1643_ = l_Array_zipWithMAux___redArg(v___x_1640_, v_as_1637_, v_bs_1638_, v___f_1639_, v___x_1641_, v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___boxed(lean_object* v_00_u03b1_1644_, lean_object* v_00_u03b2_1645_, lean_object* v_00_u03c6_1646_, lean_object* v_n_1647_, lean_object* v_f_1648_, lean_object* v_as_1649_, lean_object* v_bs_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Vector_zipWith(v_00_u03b1_1644_, v_00_u03b2_1645_, v_00_u03c6_1646_, v_n_1647_, v_f_1648_, v_as_1649_, v_bs_1650_);
lean_dec(v_n_1647_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg(lean_object* v_xs_1652_){
_start:
{
lean_object* v___x_1653_; lean_object* v_fst_1654_; lean_object* v_snd_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
v___x_1653_ = l_Array_unzip___redArg(v_xs_1652_);
v_fst_1654_ = lean_ctor_get(v___x_1653_, 0);
v_snd_1655_ = lean_ctor_get(v___x_1653_, 1);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1653_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_snd_1655_);
lean_inc(v_fst_1654_);
lean_dec(v___x_1653_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_fst_1654_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_snd_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg___boxed(lean_object* v_xs_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Vector_unzip___redArg(v_xs_1663_);
lean_dec_ref(v_xs_1663_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip(lean_object* v_00_u03b1_1665_, lean_object* v_00_u03b2_1666_, lean_object* v_n_1667_, lean_object* v_xs_1668_){
_start:
{
lean_object* v___x_1669_; lean_object* v_fst_1670_; lean_object* v_snd_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
v___x_1669_ = l_Array_unzip___redArg(v_xs_1668_);
v_fst_1670_ = lean_ctor_get(v___x_1669_, 0);
v_snd_1671_ = lean_ctor_get(v___x_1669_, 1);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1669_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_snd_1671_);
lean_inc(v_fst_1670_);
lean_dec(v___x_1669_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_fst_1670_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_snd_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___boxed(lean_object* v_00_u03b1_1679_, lean_object* v_00_u03b2_1680_, lean_object* v_n_1681_, lean_object* v_xs_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Vector_unzip(v_00_u03b1_1679_, v_00_u03b2_1680_, v_n_1681_, v_xs_1682_);
lean_dec_ref(v_xs_1682_);
lean_dec(v_n_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn___redArg(lean_object* v_n_1684_, lean_object* v_f_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Array_ofFn___redArg(v_n_1684_, v_f_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn(lean_object* v_n_1687_, lean_object* v_00_u03b1_1688_, lean_object* v_f_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Array_ofFn___redArg(v_n_1687_, v_f_1689_);
return v___x_1690_;
}
}
static lean_object* _init_l_Vector_swap___auto__1(void){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1691_;
}
}
static lean_object* _init_l_Vector_swap___auto__3(void){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg(lean_object* v_xs_1693_, lean_object* v_i_1694_, lean_object* v_j_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_array_fswap(v_xs_1693_, v_i_1694_, v_j_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg___boxed(lean_object* v_xs_1697_, lean_object* v_i_1698_, lean_object* v_j_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Vector_swap___redArg(v_xs_1697_, v_i_1698_, v_j_1699_);
lean_dec(v_j_1699_);
lean_dec(v_i_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap(lean_object* v_00_u03b1_1701_, lean_object* v_n_1702_, lean_object* v_xs_1703_, lean_object* v_i_1704_, lean_object* v_j_1705_, lean_object* v_hi_1706_, lean_object* v_hj_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_array_fswap(v_xs_1703_, v_i_1704_, v_j_1705_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___boxed(lean_object* v_00_u03b1_1709_, lean_object* v_n_1710_, lean_object* v_xs_1711_, lean_object* v_i_1712_, lean_object* v_j_1713_, lean_object* v_hi_1714_, lean_object* v_hj_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Vector_swap(v_00_u03b1_1709_, v_n_1710_, v_xs_1711_, v_i_1712_, v_j_1713_, v_hi_1714_, v_hj_1715_);
lean_dec(v_j_1713_);
lean_dec(v_i_1712_);
lean_dec(v_n_1710_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg(lean_object* v_xs_1717_, lean_object* v_i_1718_, lean_object* v_j_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_array_swap(v_xs_1717_, v_i_1718_, v_j_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg___boxed(lean_object* v_xs_1721_, lean_object* v_i_1722_, lean_object* v_j_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Vector_swapIfInBounds___redArg(v_xs_1721_, v_i_1722_, v_j_1723_);
lean_dec(v_j_1723_);
lean_dec(v_i_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds(lean_object* v_00_u03b1_1725_, lean_object* v_n_1726_, lean_object* v_xs_1727_, lean_object* v_i_1728_, lean_object* v_j_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_array_swap(v_xs_1727_, v_i_1728_, v_j_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___boxed(lean_object* v_00_u03b1_1731_, lean_object* v_n_1732_, lean_object* v_xs_1733_, lean_object* v_i_1734_, lean_object* v_j_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Vector_swapIfInBounds(v_00_u03b1_1731_, v_n_1732_, v_xs_1733_, v_i_1734_, v_j_1735_);
lean_dec(v_j_1735_);
lean_dec(v_i_1734_);
lean_dec(v_n_1732_);
return v_res_1736_;
}
}
static lean_object* _init_l_Vector_swapAt___auto__1(void){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg(lean_object* v_xs_1738_, lean_object* v_i_1739_, lean_object* v_x_1740_){
_start:
{
lean_object* v_e_1741_; lean_object* v_xs_x27_1742_; lean_object* v___x_1743_; 
v_e_1741_ = lean_array_fget(v_xs_1738_, v_i_1739_);
v_xs_x27_1742_ = lean_array_fset(v_xs_1738_, v_i_1739_, v_x_1740_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_e_1741_);
lean_ctor_set(v___x_1743_, 1, v_xs_x27_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg___boxed(lean_object* v_xs_1744_, lean_object* v_i_1745_, lean_object* v_x_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Vector_swapAt___redArg(v_xs_1744_, v_i_1745_, v_x_1746_);
lean_dec(v_i_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt(lean_object* v_00_u03b1_1748_, lean_object* v_n_1749_, lean_object* v_xs_1750_, lean_object* v_i_1751_, lean_object* v_x_1752_, lean_object* v_hi_1753_){
_start:
{
lean_object* v_e_1754_; lean_object* v_xs_x27_1755_; lean_object* v___x_1756_; 
v_e_1754_ = lean_array_fget(v_xs_1750_, v_i_1751_);
v_xs_x27_1755_ = lean_array_fset(v_xs_1750_, v_i_1751_, v_x_1752_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_e_1754_);
lean_ctor_set(v___x_1756_, 1, v_xs_x27_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___boxed(lean_object* v_00_u03b1_1757_, lean_object* v_n_1758_, lean_object* v_xs_1759_, lean_object* v_i_1760_, lean_object* v_x_1761_, lean_object* v_hi_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Vector_swapAt(v_00_u03b1_1757_, v_n_1758_, v_xs_1759_, v_i_1760_, v_x_1761_, v_hi_1762_);
lean_dec(v_i_1760_);
lean_dec(v_n_1758_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___redArg(lean_object* v_xs_1768_, lean_object* v_i_1769_, lean_object* v_x_1770_){
_start:
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = lean_array_get_size(v_xs_1768_);
v___x_1772_ = lean_nat_dec_lt(v_i_1769_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v_this_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v_fst_1785_; lean_object* v_snd_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_this_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1773_, 0, v_x_1770_);
lean_ctor_set(v_this_1773_, 1, v_xs_1768_);
v___x_1774_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1775_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1776_ = lean_unsigned_to_nat(463u);
v___x_1777_ = lean_unsigned_to_nat(4u);
v___x_1778_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1779_ = l_Nat_reprFast(v_i_1769_);
v___x_1780_ = lean_string_append(v___x_1778_, v___x_1779_);
lean_dec_ref(v___x_1779_);
v___x_1781_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1782_ = lean_string_append(v___x_1780_, v___x_1781_);
v___x_1783_ = l_mkPanicMessageWithDecl(v___x_1774_, v___x_1775_, v___x_1776_, v___x_1777_, v___x_1782_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = l_panic___redArg(v_this_1773_, v___x_1783_);
lean_dec_ref_known(v_this_1773_, 2);
v_fst_1785_ = lean_ctor_get(v___x_1784_, 0);
v_snd_1786_ = lean_ctor_get(v___x_1784_, 1);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1784_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_snd_1786_);
lean_inc(v_fst_1785_);
lean_dec(v___x_1784_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_fst_1785_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_snd_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
else
{
lean_object* v_e_1794_; lean_object* v_xs_x27_1795_; lean_object* v___x_1796_; 
v_e_1794_ = lean_array_fget(v_xs_1768_, v_i_1769_);
v_xs_x27_1795_ = lean_array_fset(v_xs_1768_, v_i_1769_, v_x_1770_);
lean_dec(v_i_1769_);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v_e_1794_);
lean_ctor_set(v___x_1796_, 1, v_xs_x27_1795_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21(lean_object* v_00_u03b1_1797_, lean_object* v_n_1798_, lean_object* v_xs_1799_, lean_object* v_i_1800_, lean_object* v_x_1801_){
_start:
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = lean_array_get_size(v_xs_1799_);
v___x_1803_ = lean_nat_dec_lt(v_i_1800_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v_this_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v_fst_1816_; lean_object* v_snd_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_this_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1804_, 0, v_x_1801_);
lean_ctor_set(v_this_1804_, 1, v_xs_1799_);
v___x_1805_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1806_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1807_ = lean_unsigned_to_nat(463u);
v___x_1808_ = lean_unsigned_to_nat(4u);
v___x_1809_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1810_ = l_Nat_reprFast(v_i_1800_);
v___x_1811_ = lean_string_append(v___x_1809_, v___x_1810_);
lean_dec_ref(v___x_1810_);
v___x_1812_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1813_ = lean_string_append(v___x_1811_, v___x_1812_);
v___x_1814_ = l_mkPanicMessageWithDecl(v___x_1805_, v___x_1806_, v___x_1807_, v___x_1808_, v___x_1813_);
lean_dec_ref(v___x_1813_);
v___x_1815_ = l_panic___redArg(v_this_1804_, v___x_1814_);
lean_dec_ref_known(v_this_1804_, 2);
v_fst_1816_ = lean_ctor_get(v___x_1815_, 0);
v_snd_1817_ = lean_ctor_get(v___x_1815_, 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1815_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_snd_1817_);
lean_inc(v_fst_1816_);
lean_dec(v___x_1815_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_fst_1816_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_snd_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
lean_object* v_e_1825_; lean_object* v_xs_x27_1826_; lean_object* v___x_1827_; 
v_e_1825_ = lean_array_fget(v_xs_1799_, v_i_1800_);
v_xs_x27_1826_ = lean_array_fset(v_xs_1799_, v_i_1800_, v_x_1801_);
lean_dec(v_i_1800_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v_e_1825_);
lean_ctor_set(v___x_1827_, 1, v_xs_x27_1826_);
return v___x_1827_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___boxed(lean_object* v_00_u03b1_1828_, lean_object* v_n_1829_, lean_object* v_xs_1830_, lean_object* v_i_1831_, lean_object* v_x_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Vector_swapAt_x21(v_00_u03b1_1828_, v_n_1829_, v_xs_1830_, v_i_1831_, v_x_1832_);
lean_dec(v_n_1829_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Vector_range(lean_object* v_n_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Array_range(v_n_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Vector_range_x27(lean_object* v_start_1836_, lean_object* v_size_1837_, lean_object* v_step_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Array_range_x27(v_start_1836_, v_size_1837_, v_step_1838_);
return v___x_1839_;
}
}
uint8_t l_Vector_isEqv___redArg(lean_object* v_n_1840_, lean_object* v_xs_1841_, lean_object* v_ys_1842_, lean_object* v_r_1843_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = l_Array_isEqvAux___redArg(v_xs_1841_, v_ys_1842_, v_r_1843_, v_n_1840_);
return v___x_1844_;
}
}
LEAN_EXPORT void l_Vector_isEqv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1840_ = stack[0].m_obj;
lean_object* v_xs_1841_ = stack[1].m_obj;
lean_object* v_ys_1842_ = stack[2].m_obj;
lean_object* v_r_1843_ = stack[3].m_obj;
uint8_t v_res_1845_;
v_res_1845_ = l_Vector_isEqv___redArg(v_n_1840_, v_xs_1841_, v_ys_1842_, v_r_1843_);
stack->m_num = v_res_1845_;
}
LEAN_EXPORT lean_object* l_Vector_isEqv___redArg___boxed(lean_object* v_n_1846_, lean_object* v_xs_1847_, lean_object* v_ys_1848_, lean_object* v_r_1849_){
_start:
{
uint8_t v_res_1850_; lean_object* v_r_1851_; 
v_res_1850_ = l_Vector_isEqv___redArg(v_n_1846_, v_xs_1847_, v_ys_1848_, v_r_1849_);
lean_dec_ref(v_ys_1848_);
lean_dec_ref(v_xs_1847_);
v_r_1851_ = lean_box(v_res_1850_);
return v_r_1851_;
}
}
uint8_t l_Vector_isEqv(lean_object* v_00_u03b1_1852_, lean_object* v_n_1853_, lean_object* v_xs_1854_, lean_object* v_ys_1855_, lean_object* v_r_1856_){
_start:
{
uint8_t v___x_1857_; 
v___x_1857_ = l_Array_isEqvAux___redArg(v_xs_1854_, v_ys_1855_, v_r_1856_, v_n_1853_);
return v___x_1857_;
}
}
LEAN_EXPORT void l_Vector_isEqv_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1853_ = stack[1].m_obj;
lean_object* v_xs_1854_ = stack[2].m_obj;
lean_object* v_ys_1855_ = stack[3].m_obj;
lean_object* v_r_1856_ = stack[4].m_obj;
uint8_t v_res_1858_;
v_res_1858_ = l_Vector_isEqv(lean_box(0), v_n_1853_, v_xs_1854_, v_ys_1855_, v_r_1856_);
stack->m_num = v_res_1858_;
}
LEAN_EXPORT lean_object* l_Vector_isEqv___boxed(lean_object* v_00_u03b1_1859_, lean_object* v_n_1860_, lean_object* v_xs_1861_, lean_object* v_ys_1862_, lean_object* v_r_1863_){
_start:
{
uint8_t v_res_1864_; lean_object* v_r_1865_; 
v_res_1864_ = l_Vector_isEqv(v_00_u03b1_1859_, v_n_1860_, v_xs_1861_, v_ys_1862_, v_r_1863_);
lean_dec_ref(v_ys_1862_);
lean_dec_ref(v_xs_1861_);
v_r_1865_ = lean_box(v_res_1864_);
return v_r_1865_;
}
}
uint8_t l_Vector_instBEq___redArg___lam__0(lean_object* v_inst_1866_, lean_object* v_x1_1867_, lean_object* v_x2_1868_){
_start:
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = lean_apply_2(v_inst_1866_, v_x1_1867_, v_x2_1868_);
v___x_1870_ = lean_unbox(v___x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT void l_Vector_instBEq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1866_ = stack[0].m_obj;
lean_object* v_x1_1867_ = stack[1].m_obj;
lean_object* v_x2_1868_ = stack[2].m_obj;
uint8_t v_res_1871_;
v_res_1871_ = l_Vector_instBEq___redArg___lam__0(v_inst_1866_, v_x1_1867_, v_x2_1868_);
stack->m_num = v_res_1871_;
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__0___boxed(lean_object* v_inst_1872_, lean_object* v_x1_1873_, lean_object* v_x2_1874_){
_start:
{
uint8_t v_res_1875_; lean_object* v_r_1876_; 
v_res_1875_ = l_Vector_instBEq___redArg___lam__0(v_inst_1872_, v_x1_1873_, v_x2_1874_);
v_r_1876_ = lean_box(v_res_1875_);
return v_r_1876_;
}
}
uint8_t l_Vector_instBEq___redArg___lam__1(lean_object* v___f_1877_, lean_object* v_n_1878_, lean_object* v_xs_1879_, lean_object* v_ys_1880_){
_start:
{
uint8_t v___x_1881_; 
v___x_1881_ = l_Array_isEqvAux___redArg(v_xs_1879_, v_ys_1880_, v___f_1877_, v_n_1878_);
return v___x_1881_;
}
}
LEAN_EXPORT void l_Vector_instBEq___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1877_ = stack[0].m_obj;
lean_object* v_n_1878_ = stack[1].m_obj;
lean_object* v_xs_1879_ = stack[2].m_obj;
lean_object* v_ys_1880_ = stack[3].m_obj;
uint8_t v_res_1882_;
v_res_1882_ = l_Vector_instBEq___redArg___lam__1(v___f_1877_, v_n_1878_, v_xs_1879_, v_ys_1880_);
stack->m_num = v_res_1882_;
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__1___boxed(lean_object* v___f_1883_, lean_object* v_n_1884_, lean_object* v_xs_1885_, lean_object* v_ys_1886_){
_start:
{
uint8_t v_res_1887_; lean_object* v_r_1888_; 
v_res_1887_ = l_Vector_instBEq___redArg___lam__1(v___f_1883_, v_n_1884_, v_xs_1885_, v_ys_1886_);
lean_dec_ref(v_ys_1886_);
lean_dec_ref(v_xs_1885_);
v_r_1888_ = lean_box(v_res_1887_);
return v_r_1888_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg(lean_object* v_n_1889_, lean_object* v_inst_1890_){
_start:
{
lean_object* v___f_1891_; lean_object* v___f_1892_; 
v___f_1891_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1891_, 0, v_inst_1890_);
v___f_1892_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1892_, 0, v___f_1891_);
lean_closure_set(v___f_1892_, 1, v_n_1889_);
return v___f_1892_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq(lean_object* v_00_u03b1_1893_, lean_object* v_n_1894_, lean_object* v_inst_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Vector_instBEq___redArg(v_n_1894_, v_inst_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___redArg(lean_object* v_xs_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Array_reverse___redArg(v_xs_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse(lean_object* v_00_u03b1_1899_, lean_object* v_n_1900_, lean_object* v_xs_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Array_reverse___redArg(v_xs_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_n_1904_, lean_object* v_xs_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Vector_reverse(v_00_u03b1_1903_, v_n_1904_, v_xs_1905_);
lean_dec(v_n_1904_);
return v_res_1906_;
}
}
static lean_object* _init_l_Vector_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___redArg(lean_object* v_xs_1908_, lean_object* v_i_1909_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Array_eraseIdx___redArg(v_xs_1908_, v_i_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx(lean_object* v_00_u03b1_1911_, lean_object* v_n_1912_, lean_object* v_xs_1913_, lean_object* v_i_1914_, lean_object* v_h_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Array_eraseIdx___redArg(v_xs_1913_, v_i_1914_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___boxed(lean_object* v_00_u03b1_1917_, lean_object* v_n_1918_, lean_object* v_xs_1919_, lean_object* v_i_1920_, lean_object* v_h_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Vector_eraseIdx(v_00_u03b1_1917_, v_n_1918_, v_xs_1919_, v_i_1920_, v_h_1921_);
lean_dec(v_n_1918_);
return v_res_1922_;
}
}
static lean_object* _init_l_Vector_eraseIdx_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1926_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1927_ = lean_unsigned_to_nat(4u);
v___x_1928_ = lean_unsigned_to_nat(433u);
v___x_1929_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__1));
v___x_1930_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1931_ = l_mkPanicMessageWithDecl(v___x_1930_, v___x_1929_, v___x_1928_, v___x_1927_, v___x_1926_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg(lean_object* v_n_1932_, lean_object* v_xs_1933_, lean_object* v_i_1934_){
_start:
{
uint8_t v___x_1935_; 
v___x_1935_ = lean_nat_dec_lt(v_i_1934_, v_n_1932_);
if (v___x_1935_ == 0)
{
lean_object* v_this_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_dec(v_i_1934_);
v_this_1936_ = lean_array_pop(v_xs_1933_);
v___x_1937_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1938_ = l_panic___redArg(v_this_1936_, v___x_1937_);
lean_dec_ref(v_this_1936_);
return v___x_1938_;
}
else
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Array_eraseIdx___redArg(v_xs_1933_, v_i_1934_);
return v___x_1939_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg___boxed(lean_object* v_n_1940_, lean_object* v_xs_1941_, lean_object* v_i_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Vector_eraseIdx_x21___redArg(v_n_1940_, v_xs_1941_, v_i_1942_);
lean_dec(v_n_1940_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21(lean_object* v_00_u03b1_1944_, lean_object* v_n_1945_, lean_object* v_xs_1946_, lean_object* v_i_1947_){
_start:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_nat_dec_lt(v_i_1947_, v_n_1945_);
if (v___x_1948_ == 0)
{
lean_object* v_this_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v_i_1947_);
v_this_1949_ = lean_array_pop(v_xs_1946_);
v___x_1950_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1951_ = l_panic___redArg(v_this_1949_, v___x_1950_);
lean_dec_ref(v_this_1949_);
return v___x_1951_;
}
else
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Array_eraseIdx___redArg(v_xs_1946_, v_i_1947_);
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___boxed(lean_object* v_00_u03b1_1953_, lean_object* v_n_1954_, lean_object* v_xs_1955_, lean_object* v_i_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Vector_eraseIdx_x21(v_00_u03b1_1953_, v_n_1954_, v_xs_1955_, v_i_1956_);
lean_dec(v_n_1954_);
return v_res_1957_;
}
}
static lean_object* _init_l_Vector_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg(lean_object* v_xs_1959_, lean_object* v_i_1960_, lean_object* v_x_1961_){
_start:
{
lean_object* v_j_1962_; lean_object* v_as_1963_; lean_object* v___x_1964_; 
v_j_1962_ = lean_array_get_size(v_xs_1959_);
v_as_1963_ = lean_array_push(v_xs_1959_, v_x_1961_);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1960_, v_as_1963_, v_j_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg___boxed(lean_object* v_xs_1965_, lean_object* v_i_1966_, lean_object* v_x_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Vector_insertIdx___redArg(v_xs_1965_, v_i_1966_, v_x_1967_);
lean_dec(v_i_1966_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx(lean_object* v_00_u03b1_1969_, lean_object* v_n_1970_, lean_object* v_xs_1971_, lean_object* v_i_1972_, lean_object* v_x_1973_, lean_object* v_h_1974_){
_start:
{
lean_object* v_j_1975_; lean_object* v_as_1976_; lean_object* v___x_1977_; 
v_j_1975_ = lean_array_get_size(v_xs_1971_);
v_as_1976_ = lean_array_push(v_xs_1971_, v_x_1973_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1972_, v_as_1976_, v_j_1975_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___boxed(lean_object* v_00_u03b1_1978_, lean_object* v_n_1979_, lean_object* v_xs_1980_, lean_object* v_i_1981_, lean_object* v_x_1982_, lean_object* v_h_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Vector_insertIdx(v_00_u03b1_1978_, v_n_1979_, v_xs_1980_, v_i_1981_, v_x_1982_, v_h_1983_);
lean_dec(v_i_1981_);
lean_dec(v_n_1979_);
return v_res_1984_;
}
}
static lean_object* _init_l_Vector_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1986_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1987_ = lean_unsigned_to_nat(4u);
v___x_1988_ = lean_unsigned_to_nat(446u);
v___x_1989_ = ((lean_object*)(l_Vector_insertIdx_x21___redArg___closed__0));
v___x_1990_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1991_ = l_mkPanicMessageWithDecl(v___x_1990_, v___x_1989_, v___x_1988_, v___x_1987_, v___x_1986_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg(lean_object* v_n_1992_, lean_object* v_xs_1993_, lean_object* v_i_1994_, lean_object* v_x_1995_){
_start:
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_nat_dec_le(v_i_1994_, v_n_1992_);
if (v___x_1996_ == 0)
{
lean_object* v_this_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v_this_1997_ = lean_array_push(v_xs_1993_, v_x_1995_);
v___x_1998_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1999_ = l_panic___redArg(v_this_1997_, v___x_1998_);
lean_dec_ref(v_this_1997_);
return v___x_1999_;
}
else
{
lean_object* v_j_2000_; lean_object* v_as_2001_; lean_object* v___x_2002_; 
v_j_2000_ = lean_array_get_size(v_xs_1993_);
v_as_2001_ = lean_array_push(v_xs_1993_, v_x_1995_);
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1994_, v_as_2001_, v_j_2000_);
return v___x_2002_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg___boxed(lean_object* v_n_2003_, lean_object* v_xs_2004_, lean_object* v_i_2005_, lean_object* v_x_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Vector_insertIdx_x21___redArg(v_n_2003_, v_xs_2004_, v_i_2005_, v_x_2006_);
lean_dec(v_i_2005_);
lean_dec(v_n_2003_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21(lean_object* v_00_u03b1_2008_, lean_object* v_n_2009_, lean_object* v_xs_2010_, lean_object* v_i_2011_, lean_object* v_x_2012_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_nat_dec_le(v_i_2011_, v_n_2009_);
if (v___x_2013_ == 0)
{
lean_object* v_this_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_this_2014_ = lean_array_push(v_xs_2010_, v_x_2012_);
v___x_2015_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_2016_ = l_panic___redArg(v_this_2014_, v___x_2015_);
lean_dec_ref(v_this_2014_);
return v___x_2016_;
}
else
{
lean_object* v_j_2017_; lean_object* v_as_2018_; lean_object* v___x_2019_; 
v_j_2017_ = lean_array_get_size(v_xs_2010_);
v_as_2018_ = lean_array_push(v_xs_2010_, v_x_2012_);
v___x_2019_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_2011_, v_as_2018_, v_j_2017_);
return v___x_2019_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_n_2021_, lean_object* v_xs_2022_, lean_object* v_i_2023_, lean_object* v_x_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Vector_insertIdx_x21(v_00_u03b1_2020_, v_n_2021_, v_xs_2022_, v_i_2023_, v_x_2024_);
lean_dec(v_i_2023_);
lean_dec(v_n_2021_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg(lean_object* v_n_2026_, lean_object* v_xs_2027_){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2029_ = l_Array_extract___redArg(v_xs_2027_, v___x_2028_, v_n_2026_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg___boxed(lean_object* v_n_2030_, lean_object* v_xs_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Vector_tail___redArg(v_n_2030_, v_xs_2031_);
lean_dec_ref(v_xs_2031_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail(lean_object* v_00_u03b1_2033_, lean_object* v_n_2034_, lean_object* v_xs_2035_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_unsigned_to_nat(1u);
v___x_2037_ = l_Array_extract___redArg(v_xs_2035_, v___x_2036_, v_n_2034_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___boxed(lean_object* v_00_u03b1_2038_, lean_object* v_n_2039_, lean_object* v_xs_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Vector_tail(v_00_u03b1_2038_, v_n_2039_, v_xs_2040_);
lean_dec_ref(v_xs_2040_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg(lean_object* v_inst_2042_, lean_object* v_xs_2043_, lean_object* v_x_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Array_finIdxOf_x3f___redArg(v_inst_2042_, v_xs_2043_, v_x_2044_);
if (lean_obj_tag(v___x_2045_) == 0)
{
return v___x_2045_;
}
else
{
lean_object* v_val_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
v_val_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_val_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_val_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_2054_, lean_object* v_xs_2055_, lean_object* v_x_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Vector_finIdxOf_x3f___redArg(v_inst_2054_, v_xs_2055_, v_x_2056_);
lean_dec_ref(v_xs_2055_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f(lean_object* v_00_u03b1_2058_, lean_object* v_n_2059_, lean_object* v_inst_2060_, lean_object* v_xs_2061_, lean_object* v_x_2062_){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Array_finIdxOf_x3f___redArg(v_inst_2060_, v_xs_2061_, v_x_2062_);
if (lean_obj_tag(v___x_2063_) == 0)
{
return v___x_2063_;
}
else
{
lean_object* v_val_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
v_val_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_val_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_val_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_2072_, lean_object* v_n_2073_, lean_object* v_inst_2074_, lean_object* v_xs_2075_, lean_object* v_x_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Vector_finIdxOf_x3f(v_00_u03b1_2072_, v_n_2073_, v_inst_2074_, v_xs_2075_, v_x_2076_);
lean_dec_ref(v_xs_2075_);
lean_dec(v_n_2073_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg(lean_object* v_p_2078_, lean_object* v_xs_2079_){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2078_, v_xs_2079_, v___x_2080_);
if (lean_obj_tag(v___x_2081_) == 0)
{
return v___x_2081_;
}
else
{
lean_object* v_val_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_val_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_val_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_val_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2090_, lean_object* v_xs_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Vector_findFinIdx_x3f___redArg(v_p_2090_, v_xs_2091_);
lean_dec_ref(v_xs_2091_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f(lean_object* v_00_u03b1_2093_, lean_object* v_n_2094_, lean_object* v_p_2095_, lean_object* v_xs_2096_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_unsigned_to_nat(0u);
v___x_2098_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2095_, v_xs_2096_, v___x_2097_);
if (lean_obj_tag(v___x_2098_) == 0)
{
return v___x_2098_;
}
else
{
lean_object* v_val_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
v_val_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_val_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_val_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2107_, lean_object* v_n_2108_, lean_object* v_p_2109_, lean_object* v_xs_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Vector_findFinIdx_x3f(v_00_u03b1_2107_, v_n_2108_, v_p_2109_, v_xs_2110_);
lean_dec_ref(v_xs_2110_);
lean_dec(v_n_2108_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__0(lean_object* v_toPure_2112_, lean_object* v_____s_2113_){
_start:
{
lean_object* v_fst_2114_; 
v_fst_2114_ = lean_ctor_get(v_____s_2113_, 0);
lean_inc(v_fst_2114_);
lean_dec_ref(v_____s_2113_);
if (lean_obj_tag(v_fst_2114_) == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_box(0);
v___x_2116_ = lean_apply_2(v_toPure_2112_, lean_box(0), v___x_2115_);
return v___x_2116_;
}
else
{
lean_object* v_val_2117_; lean_object* v___x_2118_; 
v_val_2117_ = lean_ctor_get(v_fst_2114_, 0);
lean_inc(v_val_2117_);
lean_dec_ref_known(v_fst_2114_, 1);
v___x_2118_ = lean_apply_2(v_toPure_2112_, lean_box(0), v_val_2117_);
return v___x_2118_;
}
}
}
lean_object* l_Vector_findM_x3f___redArg___lam__1(lean_object* v___x_2119_, lean_object* v_toPure_2120_, lean_object* v_a_2121_, lean_object* v___x_2122_, uint8_t v_____do__lift_2123_){
_start:
{
if (v_____do__lift_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec(v_a_2121_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2119_);
v___x_2125_ = lean_apply_2(v_toPure_2120_, lean_box(0), v___x_2124_);
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_dec_ref(v___x_2119_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_a_2121_);
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v___x_2122_);
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
v___x_2130_ = lean_apply_2(v_toPure_2120_, lean_box(0), v___x_2129_);
return v___x_2130_;
}
}
}
LEAN_EXPORT void l_Vector_findM_x3f___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2119_ = stack[0].m_obj;
lean_object* v_toPure_2120_ = stack[1].m_obj;
lean_object* v_a_2121_ = stack[2].m_obj;
lean_object* v___x_2122_ = stack[3].m_obj;
uint8_t v_____do__lift_2123_ = stack[4].m_num;
lean_object* v_res_2131_;
v_res_2131_ = l_Vector_findM_x3f___redArg___lam__1(v___x_2119_, v_toPure_2120_, v_a_2121_, v___x_2122_, v_____do__lift_2123_);
stack->m_obj
 = v_res_2131_;
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_2132_, lean_object* v_toPure_2133_, lean_object* v_a_2134_, lean_object* v___x_2135_, lean_object* v_____do__lift_2136_){
_start:
{
uint8_t v_____do__lift_129__boxed_2137_; lean_object* v_res_2138_; 
v_____do__lift_129__boxed_2137_ = lean_unbox(v_____do__lift_2136_);
v_res_2138_ = l_Vector_findM_x3f___redArg___lam__1(v___x_2132_, v_toPure_2133_, v_a_2134_, v___x_2135_, v_____do__lift_129__boxed_2137_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2(lean_object* v___x_2139_, lean_object* v_toPure_2140_, lean_object* v___x_2141_, lean_object* v_f_2142_, lean_object* v_toBind_2143_, lean_object* v_a_2144_, lean_object* v_x_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___f_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_inc(v_a_2144_);
v___f_2147_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2147_, 0, v___x_2139_);
lean_closure_set(v___f_2147_, 1, v_toPure_2140_);
lean_closure_set(v___f_2147_, 2, v_a_2144_);
lean_closure_set(v___f_2147_, 3, v___x_2141_);
v___x_2148_ = lean_apply_1(v_f_2142_, v_a_2144_);
v___x_2149_ = lean_apply_4(v_toBind_2143_, lean_box(0), lean_box(0), v___x_2148_, v___f_2147_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2___boxed(lean_object* v___x_2150_, lean_object* v_toPure_2151_, lean_object* v___x_2152_, lean_object* v_f_2153_, lean_object* v_toBind_2154_, lean_object* v_a_2155_, lean_object* v_x_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Vector_findM_x3f___redArg___lam__2(v___x_2150_, v_toPure_2151_, v___x_2152_, v_f_2153_, v_toBind_2154_, v_a_2155_, v_x_2156_, v___y_2157_);
lean_dec_ref(v___y_2157_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg(lean_object* v_inst_2162_, lean_object* v_f_2163_, lean_object* v_as_2164_){
_start:
{
lean_object* v_toApplicative_2165_; lean_object* v_toBind_2166_; lean_object* v_toPure_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___f_2170_; lean_object* v___f_2171_; size_t v_sz_2172_; size_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_toApplicative_2165_ = lean_ctor_get(v_inst_2162_, 0);
v_toBind_2166_ = lean_ctor_get(v_inst_2162_, 1);
lean_inc_n(v_toBind_2166_, 2);
v_toPure_2167_ = lean_ctor_get(v_toApplicative_2165_, 1);
v___x_2168_ = lean_box(0);
v___x_2169_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2167_, 2);
v___f_2170_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2170_, 0, v_toPure_2167_);
v___f_2171_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2171_, 0, v___x_2169_);
lean_closure_set(v___f_2171_, 1, v_toPure_2167_);
lean_closure_set(v___f_2171_, 2, v___x_2168_);
lean_closure_set(v___f_2171_, 3, v_f_2163_);
lean_closure_set(v___f_2171_, 4, v_toBind_2166_);
v_sz_2172_ = lean_array_size(v_as_2164_);
v___x_2173_ = ((size_t)0ULL);
v___x_2174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2162_, v_as_2164_, v___f_2171_, v_sz_2172_, v___x_2173_, v___x_2169_);
v___x_2175_ = lean_apply_4(v_toBind_2166_, lean_box(0), lean_box(0), v___x_2174_, v___f_2170_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f(lean_object* v_n_2176_, lean_object* v_00_u03b1_2177_, lean_object* v_m_2178_, lean_object* v_inst_2179_, lean_object* v_f_2180_, lean_object* v_as_2181_){
_start:
{
lean_object* v_toApplicative_2182_; lean_object* v_toBind_2183_; lean_object* v_toPure_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___f_2187_; lean_object* v___f_2188_; size_t v_sz_2189_; size_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_toApplicative_2182_ = lean_ctor_get(v_inst_2179_, 0);
v_toBind_2183_ = lean_ctor_get(v_inst_2179_, 1);
lean_inc_n(v_toBind_2183_, 2);
v_toPure_2184_ = lean_ctor_get(v_toApplicative_2182_, 1);
v___x_2185_ = lean_box(0);
v___x_2186_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2184_, 2);
v___f_2187_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2187_, 0, v_toPure_2184_);
v___f_2188_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2188_, 0, v___x_2186_);
lean_closure_set(v___f_2188_, 1, v_toPure_2184_);
lean_closure_set(v___f_2188_, 2, v___x_2185_);
lean_closure_set(v___f_2188_, 3, v_f_2180_);
lean_closure_set(v___f_2188_, 4, v_toBind_2183_);
v_sz_2189_ = lean_array_size(v_as_2181_);
v___x_2190_ = ((size_t)0ULL);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2179_, v_as_2181_, v___f_2188_, v_sz_2189_, v___x_2190_, v___x_2186_);
v___x_2192_ = lean_apply_4(v_toBind_2183_, lean_box(0), lean_box(0), v___x_2191_, v___f_2187_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___boxed(lean_object* v_n_2193_, lean_object* v_00_u03b1_2194_, lean_object* v_m_2195_, lean_object* v_inst_2196_, lean_object* v_f_2197_, lean_object* v_as_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Vector_findM_x3f(v_n_2193_, v_00_u03b1_2194_, v_m_2195_, v_inst_2196_, v_f_2197_, v_as_2198_);
lean_dec(v_n_2193_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__1(lean_object* v___x_2200_, lean_object* v_toPure_2201_, lean_object* v___x_2202_, lean_object* v_____do__lift_2203_){
_start:
{
if (lean_obj_tag(v_____do__lift_2203_) == 1)
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec_ref(v___x_2202_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v_____do__lift_2203_);
v___x_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v___x_2200_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
v___x_2207_ = lean_apply_2(v_toPure_2201_, lean_box(0), v___x_2206_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec(v_____do__lift_2203_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2202_);
v___x_2209_ = lean_apply_2(v_toPure_2201_, lean_box(0), v___x_2208_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0(lean_object* v_f_2210_, lean_object* v_toBind_2211_, lean_object* v___f_2212_, lean_object* v_a_2213_, lean_object* v_x_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = lean_apply_1(v_f_2210_, v_a_2213_);
v___x_2217_ = lean_apply_4(v_toBind_2211_, lean_box(0), lean_box(0), v___x_2216_, v___f_2212_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0___boxed(lean_object* v_f_2218_, lean_object* v_toBind_2219_, lean_object* v___f_2220_, lean_object* v_a_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Vector_findSomeM_x3f___redArg___lam__0(v_f_2218_, v_toBind_2219_, v___f_2220_, v_a_2221_, v_x_2222_, v___y_2223_);
lean_dec_ref(v___y_2223_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg(lean_object* v_inst_2225_, lean_object* v_f_2226_, lean_object* v_as_2227_){
_start:
{
lean_object* v_toApplicative_2228_; lean_object* v_toBind_2229_; lean_object* v_toPure_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___f_2233_; lean_object* v___f_2234_; lean_object* v___f_2235_; size_t v_sz_2236_; size_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_toApplicative_2228_ = lean_ctor_get(v_inst_2225_, 0);
v_toBind_2229_ = lean_ctor_get(v_inst_2225_, 1);
lean_inc_n(v_toBind_2229_, 2);
v_toPure_2230_ = lean_ctor_get(v_toApplicative_2228_, 1);
v___x_2231_ = lean_box(0);
v___x_2232_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2230_, 2);
v___f_2233_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2233_, 0, v_toPure_2230_);
v___f_2234_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2234_, 0, v___x_2231_);
lean_closure_set(v___f_2234_, 1, v_toPure_2230_);
lean_closure_set(v___f_2234_, 2, v___x_2232_);
v___f_2235_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2235_, 0, v_f_2226_);
lean_closure_set(v___f_2235_, 1, v_toBind_2229_);
lean_closure_set(v___f_2235_, 2, v___f_2234_);
v_sz_2236_ = lean_array_size(v_as_2227_);
v___x_2237_ = ((size_t)0ULL);
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2225_, v_as_2227_, v___f_2235_, v_sz_2236_, v___x_2237_, v___x_2232_);
v___x_2239_ = lean_apply_4(v_toBind_2229_, lean_box(0), lean_box(0), v___x_2238_, v___f_2233_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f(lean_object* v_m_2240_, lean_object* v_00_u03b1_2241_, lean_object* v_00_u03b2_2242_, lean_object* v_n_2243_, lean_object* v_inst_2244_, lean_object* v_f_2245_, lean_object* v_as_2246_){
_start:
{
lean_object* v_toApplicative_2247_; lean_object* v_toBind_2248_; lean_object* v_toPure_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___f_2252_; lean_object* v___f_2253_; lean_object* v___f_2254_; size_t v_sz_2255_; size_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v_toApplicative_2247_ = lean_ctor_get(v_inst_2244_, 0);
v_toBind_2248_ = lean_ctor_get(v_inst_2244_, 1);
lean_inc_n(v_toBind_2248_, 2);
v_toPure_2249_ = lean_ctor_get(v_toApplicative_2247_, 1);
v___x_2250_ = lean_box(0);
v___x_2251_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2249_, 2);
v___f_2252_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2252_, 0, v_toPure_2249_);
v___f_2253_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2253_, 0, v___x_2250_);
lean_closure_set(v___f_2253_, 1, v_toPure_2249_);
lean_closure_set(v___f_2253_, 2, v___x_2251_);
v___f_2254_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2254_, 0, v_f_2245_);
lean_closure_set(v___f_2254_, 1, v_toBind_2248_);
lean_closure_set(v___f_2254_, 2, v___f_2253_);
v_sz_2255_ = lean_array_size(v_as_2246_);
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2244_, v_as_2246_, v___f_2254_, v_sz_2255_, v___x_2256_, v___x_2251_);
v___x_2258_ = lean_apply_4(v_toBind_2248_, lean_box(0), lean_box(0), v___x_2257_, v___f_2252_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___boxed(lean_object* v_m_2259_, lean_object* v_00_u03b1_2260_, lean_object* v_00_u03b2_2261_, lean_object* v_n_2262_, lean_object* v_inst_2263_, lean_object* v_f_2264_, lean_object* v_as_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Vector_findSomeM_x3f(v_m_2259_, v_00_u03b1_2260_, v_00_u03b2_2261_, v_n_2262_, v_inst_2263_, v_f_2264_, v_as_2265_);
lean_dec(v_n_2262_);
return v_res_2266_;
}
}
lean_object* l_Vector_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2267_, lean_object* v_a_2268_, uint8_t v_____do__lift_2269_){
_start:
{
if (v_____do__lift_2269_ == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_a_2268_);
v___x_2270_ = lean_box(0);
v___x_2271_ = lean_apply_2(v_toPure_2267_, lean_box(0), v___x_2270_);
return v___x_2271_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2272_, 0, v_a_2268_);
v___x_2273_ = lean_apply_2(v_toPure_2267_, lean_box(0), v___x_2272_);
return v___x_2273_;
}
}
}
LEAN_EXPORT void l_Vector_findRevM_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_2267_ = stack[0].m_obj;
lean_object* v_a_2268_ = stack[1].m_obj;
uint8_t v_____do__lift_2269_ = stack[2].m_num;
lean_object* v_res_2274_;
v_res_2274_ = l_Vector_findRevM_x3f___redArg___lam__0(v_toPure_2267_, v_a_2268_, v_____do__lift_2269_);
stack->m_obj
 = v_res_2274_;
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2275_, lean_object* v_a_2276_, lean_object* v_____do__lift_2277_){
_start:
{
uint8_t v_____do__lift_50__boxed_2278_; lean_object* v_res_2279_; 
v_____do__lift_50__boxed_2278_ = lean_unbox(v_____do__lift_2277_);
v_res_2279_ = l_Vector_findRevM_x3f___redArg___lam__0(v_toPure_2275_, v_a_2276_, v_____do__lift_50__boxed_2278_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2280_, lean_object* v_f_2281_, lean_object* v_toBind_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___f_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_inc(v_a_2283_);
v___f_2284_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2284_, 0, v_toPure_2280_);
lean_closure_set(v___f_2284_, 1, v_a_2283_);
v___x_2285_ = lean_apply_1(v_f_2281_, v_a_2283_);
v___x_2286_ = lean_apply_4(v_toBind_2282_, lean_box(0), lean_box(0), v___x_2285_, v___f_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg(lean_object* v_inst_2287_, lean_object* v_f_2288_, lean_object* v_as_2289_){
_start:
{
lean_object* v_toApplicative_2290_; lean_object* v_toBind_2291_; lean_object* v_toPure_2292_; lean_object* v___f_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v_toApplicative_2290_ = lean_ctor_get(v_inst_2287_, 0);
v_toBind_2291_ = lean_ctor_get(v_inst_2287_, 1);
v_toPure_2292_ = lean_ctor_get(v_toApplicative_2290_, 1);
lean_inc(v_toBind_2291_);
lean_inc(v_toPure_2292_);
v___f_2293_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2293_, 0, v_toPure_2292_);
lean_closure_set(v___f_2293_, 1, v_f_2288_);
lean_closure_set(v___f_2293_, 2, v_toBind_2291_);
v___x_2294_ = lean_array_get_size(v_as_2289_);
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2287_, v___f_2293_, v_as_2289_, v___x_2294_, lean_box(0));
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f(lean_object* v_n_2296_, lean_object* v_00_u03b1_2297_, lean_object* v_m_2298_, lean_object* v_inst_2299_, lean_object* v_f_2300_, lean_object* v_as_2301_){
_start:
{
lean_object* v_toApplicative_2302_; lean_object* v_toBind_2303_; lean_object* v_toPure_2304_; lean_object* v___f_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_toApplicative_2302_ = lean_ctor_get(v_inst_2299_, 0);
v_toBind_2303_ = lean_ctor_get(v_inst_2299_, 1);
v_toPure_2304_ = lean_ctor_get(v_toApplicative_2302_, 1);
lean_inc(v_toBind_2303_);
lean_inc(v_toPure_2304_);
v___f_2305_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2305_, 0, v_toPure_2304_);
lean_closure_set(v___f_2305_, 1, v_f_2300_);
lean_closure_set(v___f_2305_, 2, v_toBind_2303_);
v___x_2306_ = lean_array_get_size(v_as_2301_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2299_, v___f_2305_, v_as_2301_, v___x_2306_, lean_box(0));
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___boxed(lean_object* v_n_2308_, lean_object* v_00_u03b1_2309_, lean_object* v_m_2310_, lean_object* v_inst_2311_, lean_object* v_f_2312_, lean_object* v_as_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Vector_findRevM_x3f(v_n_2308_, v_00_u03b1_2309_, v_m_2310_, v_inst_2311_, v_f_2312_, v_as_2313_);
lean_dec(v_n_2308_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___redArg(lean_object* v_inst_2315_, lean_object* v_f_2316_, lean_object* v_as_2317_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_array_get_size(v_as_2317_);
v___x_2319_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2315_, v_f_2316_, v_as_2317_, v___x_2318_, lean_box(0));
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f(lean_object* v_m_2320_, lean_object* v_00_u03b1_2321_, lean_object* v_00_u03b2_2322_, lean_object* v_n_2323_, lean_object* v_inst_2324_, lean_object* v_f_2325_, lean_object* v_as_2326_){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_array_get_size(v_as_2326_);
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2324_, v_f_2325_, v_as_2326_, v___x_2327_, lean_box(0));
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___boxed(lean_object* v_m_2329_, lean_object* v_00_u03b1_2330_, lean_object* v_00_u03b2_2331_, lean_object* v_n_2332_, lean_object* v_inst_2333_, lean_object* v_f_2334_, lean_object* v_as_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Vector_findSomeRevM_x3f(v_m_2329_, v_00_u03b1_2330_, v_00_u03b2_2331_, v_n_2332_, v_inst_2333_, v_f_2334_, v_as_2335_);
lean_dec(v_n_2332_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0(lean_object* v_f_2337_, lean_object* v___x_2338_, lean_object* v___x_2339_, lean_object* v_a_2340_, lean_object* v_x_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
lean_inc(v_a_2340_);
v___x_2343_ = lean_apply_1(v_f_2337_, v_a_2340_);
v___x_2344_ = lean_unbox(v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_dec(v_a_2340_);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2338_);
return v___x_2345_;
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
lean_dec_ref(v___x_2338_);
v___x_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2346_, 0, v_a_2340_);
v___x_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v___x_2339_);
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0___boxed(lean_object* v_f_2350_, lean_object* v___x_2351_, lean_object* v___x_2352_, lean_object* v_a_2353_, lean_object* v_x_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Vector_find_x3f___redArg___lam__0(v_f_2350_, v___x_2351_, v___x_2352_, v_a_2353_, v_x_2354_, v___y_2355_);
lean_dec_ref(v___y_2355_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg(lean_object* v_f_2357_, lean_object* v_as_2358_){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___f_2363_; size_t v_sz_2364_; size_t v___x_2365_; lean_object* v___x_2366_; lean_object* v_fst_2367_; 
v___x_2359_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2360_ = lean_box(0);
v___x_2361_ = lean_box(0);
v___x_2362_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2363_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2363_, 0, v_f_2357_);
lean_closure_set(v___f_2363_, 1, v___x_2362_);
lean_closure_set(v___f_2363_, 2, v___x_2361_);
v_sz_2364_ = lean_array_size(v_as_2358_);
v___x_2365_ = ((size_t)0ULL);
v___x_2366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2359_, v_as_2358_, v___f_2363_, v_sz_2364_, v___x_2365_, v___x_2362_);
v_fst_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_fst_2367_);
lean_dec(v___x_2366_);
if (lean_obj_tag(v_fst_2367_) == 0)
{
return v___x_2360_;
}
else
{
lean_object* v_val_2368_; 
v_val_2368_ = lean_ctor_get(v_fst_2367_, 0);
lean_inc(v_val_2368_);
lean_dec_ref_known(v_fst_2367_, 1);
return v_val_2368_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f(lean_object* v_n_2369_, lean_object* v_00_u03b1_2370_, lean_object* v_f_2371_, lean_object* v_as_2372_){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; size_t v_sz_2378_; size_t v___x_2379_; lean_object* v___x_2380_; lean_object* v_fst_2381_; 
v___x_2373_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_box(0);
v___x_2376_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2377_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2377_, 0, v_f_2371_);
lean_closure_set(v___f_2377_, 1, v___x_2376_);
lean_closure_set(v___f_2377_, 2, v___x_2375_);
v_sz_2378_ = lean_array_size(v_as_2372_);
v___x_2379_ = ((size_t)0ULL);
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2373_, v_as_2372_, v___f_2377_, v_sz_2378_, v___x_2379_, v___x_2376_);
v_fst_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_fst_2381_);
lean_dec(v___x_2380_);
if (lean_obj_tag(v_fst_2381_) == 0)
{
return v___x_2374_;
}
else
{
lean_object* v_val_2382_; 
v_val_2382_ = lean_ctor_get(v_fst_2381_, 0);
lean_inc(v_val_2382_);
lean_dec_ref_known(v_fst_2381_, 1);
return v_val_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___boxed(lean_object* v_n_2383_, lean_object* v_00_u03b1_2384_, lean_object* v_f_2385_, lean_object* v_as_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Vector_find_x3f(v_n_2383_, v_00_u03b1_2384_, v_f_2385_, v_as_2386_);
lean_dec(v_n_2383_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg___lam__0(lean_object* v_f_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___x_2390_; uint8_t v___x_2391_; 
lean_inc(v_a_2389_);
v___x_2390_ = lean_apply_1(v_f_2388_, v_a_2389_);
v___x_2391_ = lean_unbox(v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; 
lean_dec(v_a_2389_);
v___x_2392_ = lean_box(0);
return v___x_2392_;
}
else
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v_a_2389_);
return v___x_2393_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg(lean_object* v_f_2394_, lean_object* v_as_2395_){
_start:
{
lean_object* v___f_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___f_2396_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2396_, 0, v_f_2394_);
v___x_2397_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2398_ = lean_array_get_size(v_as_2395_);
v___x_2399_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2397_, v___f_2396_, v_as_2395_, v___x_2398_, lean_box(0));
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f(lean_object* v_n_2400_, lean_object* v_00_u03b1_2401_, lean_object* v_f_2402_, lean_object* v_as_2403_){
_start:
{
lean_object* v___f_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___f_2404_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2404_, 0, v_f_2402_);
v___x_2405_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2406_ = lean_array_get_size(v_as_2403_);
v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2405_, v___f_2404_, v_as_2403_, v___x_2406_, lean_box(0));
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___boxed(lean_object* v_n_2408_, lean_object* v_00_u03b1_2409_, lean_object* v_f_2410_, lean_object* v_as_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Vector_findRev_x3f(v_n_2408_, v_00_u03b1_2409_, v_f_2410_, v_as_2411_);
lean_dec(v_n_2408_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0(lean_object* v_f_2413_, lean_object* v___x_2414_, lean_object* v___x_2415_, lean_object* v_a_2416_, lean_object* v_x_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_apply_1(v_f_2413_, v_a_2416_);
if (lean_obj_tag(v___x_2419_) == 1)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_dec_ref(v___x_2415_);
v___x_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
lean_ctor_set(v___x_2421_, 1, v___x_2414_);
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
return v___x_2422_;
}
else
{
lean_object* v___x_2423_; 
lean_dec(v___x_2419_);
v___x_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2415_);
return v___x_2423_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2424_, lean_object* v___x_2425_, lean_object* v___x_2426_, lean_object* v_a_2427_, lean_object* v_x_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Vector_findSome_x3f___redArg___lam__0(v_f_2424_, v___x_2425_, v___x_2426_, v_a_2427_, v_x_2428_, v___y_2429_);
lean_dec_ref(v___y_2429_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg(lean_object* v_f_2431_, lean_object* v_as_2432_){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___f_2437_; size_t v_sz_2438_; size_t v___x_2439_; lean_object* v___x_2440_; lean_object* v_fst_2441_; 
v___x_2433_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2434_ = lean_box(0);
v___x_2435_ = lean_box(0);
v___x_2436_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2437_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2437_, 0, v_f_2431_);
lean_closure_set(v___f_2437_, 1, v___x_2435_);
lean_closure_set(v___f_2437_, 2, v___x_2436_);
v_sz_2438_ = lean_array_size(v_as_2432_);
v___x_2439_ = ((size_t)0ULL);
v___x_2440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2433_, v_as_2432_, v___f_2437_, v_sz_2438_, v___x_2439_, v___x_2436_);
v_fst_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_fst_2441_);
lean_dec(v___x_2440_);
if (lean_obj_tag(v_fst_2441_) == 0)
{
return v___x_2434_;
}
else
{
lean_object* v_val_2442_; 
v_val_2442_ = lean_ctor_get(v_fst_2441_, 0);
lean_inc(v_val_2442_);
lean_dec_ref_known(v_fst_2441_, 1);
return v_val_2442_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f(lean_object* v_00_u03b1_2443_, lean_object* v_00_u03b2_2444_, lean_object* v_n_2445_, lean_object* v_f_2446_, lean_object* v_as_2447_){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___f_2452_; size_t v_sz_2453_; size_t v___x_2454_; lean_object* v___x_2455_; lean_object* v_fst_2456_; 
v___x_2448_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2449_ = lean_box(0);
v___x_2450_ = lean_box(0);
v___x_2451_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2452_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2452_, 0, v_f_2446_);
lean_closure_set(v___f_2452_, 1, v___x_2450_);
lean_closure_set(v___f_2452_, 2, v___x_2451_);
v_sz_2453_ = lean_array_size(v_as_2447_);
v___x_2454_ = ((size_t)0ULL);
v___x_2455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2448_, v_as_2447_, v___f_2452_, v_sz_2453_, v___x_2454_, v___x_2451_);
v_fst_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_fst_2456_);
lean_dec(v___x_2455_);
if (lean_obj_tag(v_fst_2456_) == 0)
{
return v___x_2449_;
}
else
{
lean_object* v_val_2457_; 
v_val_2457_ = lean_ctor_get(v_fst_2456_, 0);
lean_inc(v_val_2457_);
lean_dec_ref_known(v_fst_2456_, 1);
return v_val_2457_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___boxed(lean_object* v_00_u03b1_2458_, lean_object* v_00_u03b2_2459_, lean_object* v_n_2460_, lean_object* v_f_2461_, lean_object* v_as_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Vector_findSome_x3f(v_00_u03b1_2458_, v_00_u03b2_2459_, v_n_2460_, v_f_2461_, v_as_2462_);
lean_dec(v_n_2460_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2464_, lean_object* v_x_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_apply_1(v_f_2464_, v_x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg(lean_object* v_f_2467_, lean_object* v_as_2468_){
_start:
{
lean_object* v___f_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___f_2469_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2469_, 0, v_f_2467_);
v___x_2470_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2471_ = lean_array_get_size(v_as_2468_);
v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2470_, v___f_2469_, v_as_2468_, v___x_2471_, lean_box(0));
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f(lean_object* v_00_u03b1_2473_, lean_object* v_00_u03b2_2474_, lean_object* v_n_2475_, lean_object* v_f_2476_, lean_object* v_as_2477_){
_start:
{
lean_object* v___f_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___f_2478_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2478_, 0, v_f_2476_);
v___x_2479_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2480_ = lean_array_get_size(v_as_2477_);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2479_, v___f_2478_, v_as_2477_, v___x_2480_, lean_box(0));
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___boxed(lean_object* v_00_u03b1_2482_, lean_object* v_00_u03b2_2483_, lean_object* v_n_2484_, lean_object* v_f_2485_, lean_object* v_as_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Vector_findSomeRev_x3f(v_00_u03b1_2482_, v_00_u03b2_2483_, v_n_2484_, v_f_2485_, v_as_2486_);
lean_dec(v_n_2484_);
return v_res_2487_;
}
}
uint8_t l_Vector_isPrefixOf___redArg(lean_object* v_inst_2488_, lean_object* v_xs_2489_, lean_object* v_ys_2490_){
_start:
{
uint8_t v___x_2491_; 
v___x_2491_ = l_Array_isPrefixOf___redArg(v_inst_2488_, v_xs_2489_, v_ys_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT void l_Vector_isPrefixOf___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2488_ = stack[0].m_obj;
lean_object* v_xs_2489_ = stack[1].m_obj;
lean_object* v_ys_2490_ = stack[2].m_obj;
uint8_t v_res_2492_;
v_res_2492_ = l_Vector_isPrefixOf___redArg(v_inst_2488_, v_xs_2489_, v_ys_2490_);
stack->m_num = v_res_2492_;
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___redArg___boxed(lean_object* v_inst_2493_, lean_object* v_xs_2494_, lean_object* v_ys_2495_){
_start:
{
uint8_t v_res_2496_; lean_object* v_r_2497_; 
v_res_2496_ = l_Vector_isPrefixOf___redArg(v_inst_2493_, v_xs_2494_, v_ys_2495_);
lean_dec_ref(v_ys_2495_);
lean_dec_ref(v_xs_2494_);
v_r_2497_ = lean_box(v_res_2496_);
return v_r_2497_;
}
}
uint8_t l_Vector_isPrefixOf(lean_object* v_00_u03b1_2498_, lean_object* v_m_2499_, lean_object* v_n_2500_, lean_object* v_inst_2501_, lean_object* v_xs_2502_, lean_object* v_ys_2503_){
_start:
{
uint8_t v___x_2504_; 
v___x_2504_ = l_Array_isPrefixOf___redArg(v_inst_2501_, v_xs_2502_, v_ys_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT void l_Vector_isPrefixOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2499_ = stack[1].m_obj;
lean_object* v_n_2500_ = stack[2].m_obj;
lean_object* v_inst_2501_ = stack[3].m_obj;
lean_object* v_xs_2502_ = stack[4].m_obj;
lean_object* v_ys_2503_ = stack[5].m_obj;
uint8_t v_res_2505_;
v_res_2505_ = l_Vector_isPrefixOf(lean_box(0), v_m_2499_, v_n_2500_, v_inst_2501_, v_xs_2502_, v_ys_2503_);
stack->m_num = v_res_2505_;
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___boxed(lean_object* v_00_u03b1_2506_, lean_object* v_m_2507_, lean_object* v_n_2508_, lean_object* v_inst_2509_, lean_object* v_xs_2510_, lean_object* v_ys_2511_){
_start:
{
uint8_t v_res_2512_; lean_object* v_r_2513_; 
v_res_2512_ = l_Vector_isPrefixOf(v_00_u03b1_2506_, v_m_2507_, v_n_2508_, v_inst_2509_, v_xs_2510_, v_ys_2511_);
lean_dec_ref(v_ys_2511_);
lean_dec_ref(v_xs_2510_);
lean_dec(v_n_2508_);
lean_dec(v_m_2507_);
v_r_2513_ = lean_box(v_res_2512_);
return v_r_2513_;
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___redArg(lean_object* v_inst_2514_, lean_object* v_p_2515_, lean_object* v_xs_2516_){
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
LEAN_EXPORT lean_object* l_Vector_anyM(lean_object* v_m_2529_, lean_object* v_00_u03b1_2530_, lean_object* v_n_2531_, lean_object* v_inst_2532_, lean_object* v_p_2533_, lean_object* v_xs_2534_){
_start:
{
lean_object* v_toApplicative_2535_; lean_object* v_toPure_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v_toApplicative_2535_ = lean_ctor_get(v_inst_2532_, 0);
v_toPure_2536_ = lean_ctor_get(v_toApplicative_2535_, 1);
v___x_2537_ = lean_unsigned_to_nat(0u);
v___x_2538_ = lean_array_get_size(v_xs_2534_);
v___x_2539_ = lean_nat_dec_lt(v___x_2537_, v___x_2538_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
lean_inc(v_toPure_2536_);
lean_dec_ref(v_xs_2534_);
lean_dec(v_p_2533_);
lean_dec_ref(v_inst_2532_);
v___x_2540_ = lean_box(v___x_2539_);
v___x_2541_ = lean_apply_2(v_toPure_2536_, lean_box(0), v___x_2540_);
return v___x_2541_;
}
else
{
if (v___x_2539_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_inc(v_toPure_2536_);
lean_dec_ref(v_xs_2534_);
lean_dec(v_p_2533_);
lean_dec_ref(v_inst_2532_);
v___x_2542_ = lean_box(v___x_2539_);
v___x_2543_ = lean_apply_2(v_toPure_2536_, lean_box(0), v___x_2542_);
return v___x_2543_;
}
else
{
size_t v___x_2544_; size_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = ((size_t)0ULL);
v___x_2545_ = lean_usize_of_nat(v___x_2538_);
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2532_, v_p_2533_, v_xs_2534_, v___x_2544_, v___x_2545_);
return v___x_2546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___boxed(lean_object* v_m_2547_, lean_object* v_00_u03b1_2548_, lean_object* v_n_2549_, lean_object* v_inst_2550_, lean_object* v_p_2551_, lean_object* v_xs_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Vector_anyM(v_m_2547_, v_00_u03b1_2548_, v_n_2549_, v_inst_2550_, v_p_2551_, v_xs_2552_);
lean_dec(v_n_2549_);
return v_res_2553_;
}
}
lean_object* l_Vector_allM___redArg___lam__0(lean_object* v_toPure_2554_, uint8_t v_____do__lift_2555_){
_start:
{
if (v_____do__lift_2555_ == 0)
{
uint8_t v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2556_ = 1;
v___x_2557_ = lean_box(v___x_2556_);
v___x_2558_ = lean_apply_2(v_toPure_2554_, lean_box(0), v___x_2557_);
return v___x_2558_;
}
else
{
uint8_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = 0;
v___x_2560_ = lean_box(v___x_2559_);
v___x_2561_ = lean_apply_2(v_toPure_2554_, lean_box(0), v___x_2560_);
return v___x_2561_;
}
}
}
LEAN_EXPORT void l_Vector_allM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_2554_ = stack[0].m_obj;
uint8_t v_____do__lift_2555_ = stack[1].m_num;
lean_object* v_res_2562_;
v_res_2562_ = l_Vector_allM___redArg___lam__0(v_toPure_2554_, v_____do__lift_2555_);
stack->m_obj
 = v_res_2562_;
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0___boxed(lean_object* v_toPure_2563_, lean_object* v_____do__lift_2564_){
_start:
{
uint8_t v_____do__lift_112__boxed_2565_; lean_object* v_res_2566_; 
v_____do__lift_112__boxed_2565_ = lean_unbox(v_____do__lift_2564_);
v_res_2566_ = l_Vector_allM___redArg___lam__0(v_toPure_2563_, v_____do__lift_112__boxed_2565_);
return v_res_2566_;
}
}
lean_object* l_Vector_allM___redArg___lam__1(lean_object* v_toPure_2567_, uint8_t v___x_2568_, uint8_t v_____do__lift_2569_){
_start:
{
if (v_____do__lift_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_box(v___x_2568_);
v___x_2571_ = lean_apply_2(v_toPure_2567_, lean_box(0), v___x_2570_);
return v___x_2571_;
}
else
{
uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = 0;
v___x_2573_ = lean_box(v___x_2572_);
v___x_2574_ = lean_apply_2(v_toPure_2567_, lean_box(0), v___x_2573_);
return v___x_2574_;
}
}
}
LEAN_EXPORT void l_Vector_allM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_2567_ = stack[0].m_obj;
uint8_t v___x_2568_ = stack[1].m_num;
uint8_t v_____do__lift_2569_ = stack[2].m_num;
lean_object* v_res_2575_;
v_res_2575_ = l_Vector_allM___redArg___lam__1(v_toPure_2567_, v___x_2568_, v_____do__lift_2569_);
stack->m_obj
 = v_res_2575_;
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1___boxed(lean_object* v_toPure_2576_, lean_object* v___x_2577_, lean_object* v_____do__lift_2578_){
_start:
{
uint8_t v___x_135__boxed_2579_; uint8_t v_____do__lift_136__boxed_2580_; lean_object* v_res_2581_; 
v___x_135__boxed_2579_ = lean_unbox(v___x_2577_);
v_____do__lift_136__boxed_2580_ = lean_unbox(v_____do__lift_2578_);
v_res_2581_ = l_Vector_allM___redArg___lam__1(v_toPure_2576_, v___x_135__boxed_2579_, v_____do__lift_136__boxed_2580_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__2(lean_object* v_p_2582_, lean_object* v_toBind_2583_, lean_object* v___f_2584_, lean_object* v_v_2585_){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_apply_1(v_p_2582_, v_v_2585_);
v___x_2587_ = lean_apply_4(v_toBind_2583_, lean_box(0), lean_box(0), v___x_2586_, v___f_2584_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg(lean_object* v_inst_2588_, lean_object* v_p_2589_, lean_object* v_xs_2590_){
_start:
{
lean_object* v_toApplicative_2591_; lean_object* v_toBind_2592_; lean_object* v_toPure_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___f_2596_; uint8_t v___x_2597_; 
v_toApplicative_2591_ = lean_ctor_get(v_inst_2588_, 0);
v_toBind_2592_ = lean_ctor_get(v_inst_2588_, 1);
lean_inc(v_toBind_2592_);
v_toPure_2593_ = lean_ctor_get(v_toApplicative_2591_, 1);
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = lean_array_get_size(v_xs_2590_);
lean_inc(v_toPure_2593_);
v___f_2596_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2596_, 0, v_toPure_2593_);
v___x_2597_ = lean_nat_dec_lt(v___x_2594_, v___x_2595_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_inc(v_toPure_2593_);
lean_dec_ref(v_xs_2590_);
lean_dec(v_p_2589_);
lean_dec_ref(v_inst_2588_);
v___x_2598_ = lean_box(v___x_2597_);
v___x_2599_ = lean_apply_2(v_toPure_2593_, lean_box(0), v___x_2598_);
v___x_2600_ = lean_apply_4(v_toBind_2592_, lean_box(0), lean_box(0), v___x_2599_, v___f_2596_);
return v___x_2600_;
}
else
{
if (v___x_2597_ == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_inc(v_toPure_2593_);
lean_dec_ref(v_xs_2590_);
lean_dec(v_p_2589_);
lean_dec_ref(v_inst_2588_);
v___x_2601_ = lean_box(v___x_2597_);
v___x_2602_ = lean_apply_2(v_toPure_2593_, lean_box(0), v___x_2601_);
v___x_2603_ = lean_apply_4(v_toBind_2592_, lean_box(0), lean_box(0), v___x_2602_, v___f_2596_);
return v___x_2603_;
}
else
{
lean_object* v___x_2604_; lean_object* v___f_2605_; lean_object* v___f_2606_; size_t v___x_2607_; size_t v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2604_ = lean_box(v___x_2597_);
lean_inc(v_toPure_2593_);
v___f_2605_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2605_, 0, v_toPure_2593_);
lean_closure_set(v___f_2605_, 1, v___x_2604_);
lean_inc(v_toBind_2592_);
v___f_2606_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2606_, 0, v_p_2589_);
lean_closure_set(v___f_2606_, 1, v_toBind_2592_);
lean_closure_set(v___f_2606_, 2, v___f_2605_);
v___x_2607_ = ((size_t)0ULL);
v___x_2608_ = lean_usize_of_nat(v___x_2595_);
v___x_2609_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2588_, v___f_2606_, v_xs_2590_, v___x_2607_, v___x_2608_);
v___x_2610_ = lean_apply_4(v_toBind_2592_, lean_box(0), lean_box(0), v___x_2609_, v___f_2596_);
return v___x_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM(lean_object* v_m_2611_, lean_object* v_00_u03b1_2612_, lean_object* v_n_2613_, lean_object* v_inst_2614_, lean_object* v_p_2615_, lean_object* v_xs_2616_){
_start:
{
lean_object* v_toApplicative_2617_; lean_object* v_toBind_2618_; lean_object* v_toPure_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___f_2622_; uint8_t v___x_2623_; 
v_toApplicative_2617_ = lean_ctor_get(v_inst_2614_, 0);
v_toBind_2618_ = lean_ctor_get(v_inst_2614_, 1);
lean_inc(v_toBind_2618_);
v_toPure_2619_ = lean_ctor_get(v_toApplicative_2617_, 1);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_array_get_size(v_xs_2616_);
lean_inc(v_toPure_2619_);
v___f_2622_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2622_, 0, v_toPure_2619_);
v___x_2623_ = lean_nat_dec_lt(v___x_2620_, v___x_2621_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_inc(v_toPure_2619_);
lean_dec_ref(v_xs_2616_);
lean_dec(v_p_2615_);
lean_dec_ref(v_inst_2614_);
v___x_2624_ = lean_box(v___x_2623_);
v___x_2625_ = lean_apply_2(v_toPure_2619_, lean_box(0), v___x_2624_);
v___x_2626_ = lean_apply_4(v_toBind_2618_, lean_box(0), lean_box(0), v___x_2625_, v___f_2622_);
return v___x_2626_;
}
else
{
if (v___x_2623_ == 0)
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
lean_inc(v_toPure_2619_);
lean_dec_ref(v_xs_2616_);
lean_dec(v_p_2615_);
lean_dec_ref(v_inst_2614_);
v___x_2627_ = lean_box(v___x_2623_);
v___x_2628_ = lean_apply_2(v_toPure_2619_, lean_box(0), v___x_2627_);
v___x_2629_ = lean_apply_4(v_toBind_2618_, lean_box(0), lean_box(0), v___x_2628_, v___f_2622_);
return v___x_2629_;
}
else
{
lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___f_2632_; size_t v___x_2633_; size_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2630_ = lean_box(v___x_2623_);
lean_inc(v_toPure_2619_);
v___f_2631_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2631_, 0, v_toPure_2619_);
lean_closure_set(v___f_2631_, 1, v___x_2630_);
lean_inc(v_toBind_2618_);
v___f_2632_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2632_, 0, v_p_2615_);
lean_closure_set(v___f_2632_, 1, v_toBind_2618_);
lean_closure_set(v___f_2632_, 2, v___f_2631_);
v___x_2633_ = ((size_t)0ULL);
v___x_2634_ = lean_usize_of_nat(v___x_2621_);
v___x_2635_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2614_, v___f_2632_, v_xs_2616_, v___x_2633_, v___x_2634_);
v___x_2636_ = lean_apply_4(v_toBind_2618_, lean_box(0), lean_box(0), v___x_2635_, v___f_2622_);
return v___x_2636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___boxed(lean_object* v_m_2637_, lean_object* v_00_u03b1_2638_, lean_object* v_n_2639_, lean_object* v_inst_2640_, lean_object* v_p_2641_, lean_object* v_xs_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Vector_allM(v_m_2637_, v_00_u03b1_2638_, v_n_2639_, v_inst_2640_, v_p_2641_, v_xs_2642_);
lean_dec(v_n_2639_);
return v_res_2643_;
}
}
uint8_t l_Vector_any___redArg___lam__0(lean_object* v_p_2644_, lean_object* v_x_2645_){
_start:
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = lean_apply_1(v_p_2644_, v_x_2645_);
v___x_2647_ = lean_unbox(v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT void l_Vector_any___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2644_ = stack[0].m_obj;
lean_object* v_x_2645_ = stack[1].m_obj;
uint8_t v_res_2648_;
v_res_2648_ = l_Vector_any___redArg___lam__0(v_p_2644_, v_x_2645_);
stack->m_num = v_res_2648_;
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___lam__0___boxed(lean_object* v_p_2649_, lean_object* v_x_2650_){
_start:
{
uint8_t v_res_2651_; lean_object* v_r_2652_; 
v_res_2651_ = l_Vector_any___redArg___lam__0(v_p_2649_, v_x_2650_);
v_r_2652_ = lean_box(v_res_2651_);
return v_r_2652_;
}
}
uint8_t l_Vector_any___redArg(lean_object* v_xs_2653_, lean_object* v_p_2654_){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2655_ = lean_unsigned_to_nat(0u);
v___x_2656_ = lean_array_get_size(v_xs_2653_);
v___x_2657_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2658_ = lean_nat_dec_lt(v___x_2655_, v___x_2656_);
if (v___x_2658_ == 0)
{
lean_dec_ref(v_p_2654_);
lean_dec_ref(v_xs_2653_);
return v___x_2658_;
}
else
{
if (v___x_2658_ == 0)
{
lean_dec_ref(v_p_2654_);
lean_dec_ref(v_xs_2653_);
return v___x_2658_;
}
else
{
lean_object* v___f_2659_; size_t v___x_2660_; size_t v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___f_2659_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2659_, 0, v_p_2654_);
v___x_2660_ = ((size_t)0ULL);
v___x_2661_ = lean_usize_of_nat(v___x_2656_);
v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2657_, v___f_2659_, v_xs_2653_, v___x_2660_, v___x_2661_);
v___x_2663_ = lean_unbox(v___x_2662_);
lean_dec(v___x_2662_);
return v___x_2663_;
}
}
}
}
LEAN_EXPORT void l_Vector_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2653_ = stack[0].m_obj;
lean_object* v_p_2654_ = stack[1].m_obj;
uint8_t v_res_2664_;
v_res_2664_ = l_Vector_any___redArg(v_xs_2653_, v_p_2654_);
stack->m_num = v_res_2664_;
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___boxed(lean_object* v_xs_2665_, lean_object* v_p_2666_){
_start:
{
uint8_t v_res_2667_; lean_object* v_r_2668_; 
v_res_2667_ = l_Vector_any___redArg(v_xs_2665_, v_p_2666_);
v_r_2668_ = lean_box(v_res_2667_);
return v_r_2668_;
}
}
uint8_t l_Vector_any(lean_object* v_00_u03b1_2669_, lean_object* v_n_2670_, lean_object* v_xs_2671_, lean_object* v_p_2672_){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2673_ = lean_unsigned_to_nat(0u);
v___x_2674_ = lean_array_get_size(v_xs_2671_);
v___x_2675_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2676_ = lean_nat_dec_lt(v___x_2673_, v___x_2674_);
if (v___x_2676_ == 0)
{
lean_dec_ref(v_p_2672_);
lean_dec_ref(v_xs_2671_);
return v___x_2676_;
}
else
{
if (v___x_2676_ == 0)
{
lean_dec_ref(v_p_2672_);
lean_dec_ref(v_xs_2671_);
return v___x_2676_;
}
else
{
lean_object* v___f_2677_; size_t v___x_2678_; size_t v___x_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v___f_2677_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2677_, 0, v_p_2672_);
v___x_2678_ = ((size_t)0ULL);
v___x_2679_ = lean_usize_of_nat(v___x_2674_);
v___x_2680_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2675_, v___f_2677_, v_xs_2671_, v___x_2678_, v___x_2679_);
v___x_2681_ = lean_unbox(v___x_2680_);
lean_dec(v___x_2680_);
return v___x_2681_;
}
}
}
}
LEAN_EXPORT void l_Vector_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2670_ = stack[1].m_obj;
lean_object* v_xs_2671_ = stack[2].m_obj;
lean_object* v_p_2672_ = stack[3].m_obj;
uint8_t v_res_2682_;
v_res_2682_ = l_Vector_any(lean_box(0), v_n_2670_, v_xs_2671_, v_p_2672_);
stack->m_num = v_res_2682_;
}
LEAN_EXPORT lean_object* l_Vector_any___boxed(lean_object* v_00_u03b1_2683_, lean_object* v_n_2684_, lean_object* v_xs_2685_, lean_object* v_p_2686_){
_start:
{
uint8_t v_res_2687_; lean_object* v_r_2688_; 
v_res_2687_ = l_Vector_any(v_00_u03b1_2683_, v_n_2684_, v_xs_2685_, v_p_2686_);
lean_dec(v_n_2684_);
v_r_2688_ = lean_box(v_res_2687_);
return v_r_2688_;
}
}
uint8_t l_Vector_all___redArg___lam__0(lean_object* v_p_2689_, uint8_t v___x_2690_, lean_object* v_v_2691_){
_start:
{
lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = lean_apply_1(v_p_2689_, v_v_2691_);
v___x_2693_ = lean_unbox(v___x_2692_);
if (v___x_2693_ == 0)
{
return v___x_2690_;
}
else
{
uint8_t v___x_2694_; 
v___x_2694_ = 0;
return v___x_2694_;
}
}
}
LEAN_EXPORT void l_Vector_all___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2689_ = stack[0].m_obj;
uint8_t v___x_2690_ = stack[1].m_num;
lean_object* v_v_2691_ = stack[2].m_obj;
uint8_t v_res_2695_;
v_res_2695_ = l_Vector_all___redArg___lam__0(v_p_2689_, v___x_2690_, v_v_2691_);
stack->m_num = v_res_2695_;
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___lam__0___boxed(lean_object* v_p_2696_, lean_object* v___x_2697_, lean_object* v_v_2698_){
_start:
{
uint8_t v___x_75__boxed_2699_; uint8_t v_res_2700_; lean_object* v_r_2701_; 
v___x_75__boxed_2699_ = lean_unbox(v___x_2697_);
v_res_2700_ = l_Vector_all___redArg___lam__0(v_p_2696_, v___x_75__boxed_2699_, v_v_2698_);
v_r_2701_ = lean_box(v_res_2700_);
return v_r_2701_;
}
}
uint8_t l_Vector_all___redArg(lean_object* v_xs_2702_, lean_object* v_p_2703_){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2704_ = lean_unsigned_to_nat(0u);
v___x_2705_ = lean_array_get_size(v_xs_2702_);
v___x_2706_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2707_ = lean_nat_dec_lt(v___x_2704_, v___x_2705_);
if (v___x_2707_ == 0)
{
uint8_t v___x_2708_; 
lean_dec_ref(v_p_2703_);
lean_dec_ref(v_xs_2702_);
v___x_2708_ = 1;
return v___x_2708_;
}
else
{
if (v___x_2707_ == 0)
{
lean_dec_ref(v_p_2703_);
lean_dec_ref(v_xs_2702_);
return v___x_2707_;
}
else
{
lean_object* v___x_2709_; lean_object* v___f_2710_; size_t v___x_2711_; size_t v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2709_ = lean_box(v___x_2707_);
v___f_2710_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2710_, 0, v_p_2703_);
lean_closure_set(v___f_2710_, 1, v___x_2709_);
v___x_2711_ = ((size_t)0ULL);
v___x_2712_ = lean_usize_of_nat(v___x_2705_);
v___x_2713_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2706_, v___f_2710_, v_xs_2702_, v___x_2711_, v___x_2712_);
v___x_2714_ = lean_unbox(v___x_2713_);
lean_dec(v___x_2713_);
if (v___x_2714_ == 0)
{
return v___x_2707_;
}
else
{
uint8_t v___x_2715_; 
v___x_2715_ = 0;
return v___x_2715_;
}
}
}
}
}
LEAN_EXPORT void l_Vector_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2702_ = stack[0].m_obj;
lean_object* v_p_2703_ = stack[1].m_obj;
uint8_t v_res_2716_;
v_res_2716_ = l_Vector_all___redArg(v_xs_2702_, v_p_2703_);
stack->m_num = v_res_2716_;
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___boxed(lean_object* v_xs_2717_, lean_object* v_p_2718_){
_start:
{
uint8_t v_res_2719_; lean_object* v_r_2720_; 
v_res_2719_ = l_Vector_all___redArg(v_xs_2717_, v_p_2718_);
v_r_2720_ = lean_box(v_res_2719_);
return v_r_2720_;
}
}
uint8_t l_Vector_all(lean_object* v_00_u03b1_2721_, lean_object* v_n_2722_, lean_object* v_xs_2723_, lean_object* v_p_2724_){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2725_ = lean_unsigned_to_nat(0u);
v___x_2726_ = lean_array_get_size(v_xs_2723_);
v___x_2727_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2728_ = lean_nat_dec_lt(v___x_2725_, v___x_2726_);
if (v___x_2728_ == 0)
{
uint8_t v___x_2729_; 
lean_dec_ref(v_p_2724_);
lean_dec_ref(v_xs_2723_);
v___x_2729_ = 1;
return v___x_2729_;
}
else
{
if (v___x_2728_ == 0)
{
lean_dec_ref(v_p_2724_);
lean_dec_ref(v_xs_2723_);
return v___x_2728_;
}
else
{
lean_object* v___x_2730_; lean_object* v___f_2731_; size_t v___x_2732_; size_t v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2730_ = lean_box(v___x_2728_);
v___f_2731_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2731_, 0, v_p_2724_);
lean_closure_set(v___f_2731_, 1, v___x_2730_);
v___x_2732_ = ((size_t)0ULL);
v___x_2733_ = lean_usize_of_nat(v___x_2726_);
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2727_, v___f_2731_, v_xs_2723_, v___x_2732_, v___x_2733_);
v___x_2735_ = lean_unbox(v___x_2734_);
lean_dec(v___x_2734_);
if (v___x_2735_ == 0)
{
return v___x_2728_;
}
else
{
uint8_t v___x_2736_; 
v___x_2736_ = 0;
return v___x_2736_;
}
}
}
}
}
LEAN_EXPORT void l_Vector_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2722_ = stack[1].m_obj;
lean_object* v_xs_2723_ = stack[2].m_obj;
lean_object* v_p_2724_ = stack[3].m_obj;
uint8_t v_res_2737_;
v_res_2737_ = l_Vector_all(lean_box(0), v_n_2722_, v_xs_2723_, v_p_2724_);
stack->m_num = v_res_2737_;
}
LEAN_EXPORT lean_object* l_Vector_all___boxed(lean_object* v_00_u03b1_2738_, lean_object* v_n_2739_, lean_object* v_xs_2740_, lean_object* v_p_2741_){
_start:
{
uint8_t v_res_2742_; lean_object* v_r_2743_; 
v_res_2742_ = l_Vector_all(v_00_u03b1_2738_, v_n_2739_, v_xs_2740_, v_p_2741_);
lean_dec(v_n_2739_);
v_r_2743_ = lean_box(v_res_2742_);
return v_r_2743_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0(lean_object* v_p_2744_, lean_object* v_x1_2745_, lean_object* v_x2_2746_){
_start:
{
lean_object* v___x_2747_; uint8_t v___x_2748_; 
v___x_2747_ = lean_apply_1(v_p_2744_, v_x1_2745_);
v___x_2748_ = lean_unbox(v___x_2747_);
if (v___x_2748_ == 0)
{
lean_inc(v_x2_2746_);
return v_x2_2746_;
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_unsigned_to_nat(1u);
v___x_2750_ = lean_nat_add(v_x2_2746_, v___x_2749_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0___boxed(lean_object* v_p_2751_, lean_object* v_x1_2752_, lean_object* v_x2_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Vector_countP___redArg___lam__0(v_p_2751_, v_x1_2752_, v_x2_2753_);
lean_dec(v_x2_2753_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg(lean_object* v_p_2755_, lean_object* v_xs_2756_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2757_ = lean_unsigned_to_nat(0u);
v___x_2758_ = lean_array_get_size(v_xs_2756_);
v___x_2759_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2760_ = lean_nat_dec_lt(v___x_2757_, v___x_2758_);
if (v___x_2760_ == 0)
{
lean_dec_ref(v_xs_2756_);
lean_dec_ref(v_p_2755_);
return v___x_2757_;
}
else
{
lean_object* v___f_2761_; size_t v___x_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
v___f_2761_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2761_, 0, v_p_2755_);
v___x_2762_ = lean_usize_of_nat(v___x_2758_);
v___x_2763_ = ((size_t)0ULL);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2759_, v___f_2761_, v_xs_2756_, v___x_2762_, v___x_2763_, v___x_2757_);
return v___x_2764_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP(lean_object* v_00_u03b1_2765_, lean_object* v_n_2766_, lean_object* v_p_2767_, lean_object* v_xs_2768_){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2769_ = lean_unsigned_to_nat(0u);
v___x_2770_ = lean_array_get_size(v_xs_2768_);
v___x_2771_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2772_ = lean_nat_dec_lt(v___x_2769_, v___x_2770_);
if (v___x_2772_ == 0)
{
lean_dec_ref(v_xs_2768_);
lean_dec_ref(v_p_2767_);
return v___x_2769_;
}
else
{
lean_object* v___f_2773_; size_t v___x_2774_; size_t v___x_2775_; lean_object* v___x_2776_; 
v___f_2773_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2773_, 0, v_p_2767_);
v___x_2774_ = lean_usize_of_nat(v___x_2770_);
v___x_2775_ = ((size_t)0ULL);
v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2771_, v___f_2773_, v_xs_2768_, v___x_2774_, v___x_2775_, v___x_2769_);
return v___x_2776_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___boxed(lean_object* v_00_u03b1_2777_, lean_object* v_n_2778_, lean_object* v_p_2779_, lean_object* v_xs_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Vector_countP(v_00_u03b1_2777_, v_n_2778_, v_p_2779_, v_xs_2780_);
lean_dec(v_n_2778_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0(lean_object* v_inst_2782_, lean_object* v_a_2783_, lean_object* v_x1_2784_, lean_object* v_x2_2785_){
_start:
{
lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2786_ = lean_apply_2(v_inst_2782_, v_x1_2784_, v_a_2783_);
v___x_2787_ = lean_unbox(v___x_2786_);
if (v___x_2787_ == 0)
{
lean_inc(v_x2_2785_);
return v_x2_2785_;
}
else
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_unsigned_to_nat(1u);
v___x_2789_ = lean_nat_add(v_x2_2785_, v___x_2788_);
return v___x_2789_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0___boxed(lean_object* v_inst_2790_, lean_object* v_a_2791_, lean_object* v_x1_2792_, lean_object* v_x2_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Vector_count___redArg___lam__0(v_inst_2790_, v_a_2791_, v_x1_2792_, v_x2_2793_);
lean_dec(v_x2_2793_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg(lean_object* v_inst_2795_, lean_object* v_a_2796_, lean_object* v_xs_2797_){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v___x_2798_ = lean_unsigned_to_nat(0u);
v___x_2799_ = lean_array_get_size(v_xs_2797_);
v___x_2800_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2801_ = lean_nat_dec_lt(v___x_2798_, v___x_2799_);
if (v___x_2801_ == 0)
{
lean_dec_ref(v_xs_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_inst_2795_);
return v___x_2798_;
}
else
{
lean_object* v___f_2802_; size_t v___x_2803_; size_t v___x_2804_; lean_object* v___x_2805_; 
v___f_2802_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2802_, 0, v_inst_2795_);
lean_closure_set(v___f_2802_, 1, v_a_2796_);
v___x_2803_ = lean_usize_of_nat(v___x_2799_);
v___x_2804_ = ((size_t)0ULL);
v___x_2805_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2800_, v___f_2802_, v_xs_2797_, v___x_2803_, v___x_2804_, v___x_2798_);
return v___x_2805_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count(lean_object* v_00_u03b1_2806_, lean_object* v_n_2807_, lean_object* v_inst_2808_, lean_object* v_a_2809_, lean_object* v_xs_2810_){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2811_ = lean_unsigned_to_nat(0u);
v___x_2812_ = lean_array_get_size(v_xs_2810_);
v___x_2813_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2814_ = lean_nat_dec_lt(v___x_2811_, v___x_2812_);
if (v___x_2814_ == 0)
{
lean_dec_ref(v_xs_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_inst_2808_);
return v___x_2811_;
}
else
{
lean_object* v___f_2815_; size_t v___x_2816_; size_t v___x_2817_; lean_object* v___x_2818_; 
v___f_2815_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2815_, 0, v_inst_2808_);
lean_closure_set(v___f_2815_, 1, v_a_2809_);
v___x_2816_ = lean_usize_of_nat(v___x_2812_);
v___x_2817_ = ((size_t)0ULL);
v___x_2818_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2813_, v___f_2815_, v_xs_2810_, v___x_2816_, v___x_2817_, v___x_2811_);
return v___x_2818_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___boxed(lean_object* v_00_u03b1_2819_, lean_object* v_n_2820_, lean_object* v_inst_2821_, lean_object* v_a_2822_, lean_object* v_xs_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Vector_count(v_00_u03b1_2819_, v_n_2820_, v_inst_2821_, v_a_2822_, v_xs_2823_);
lean_dec(v_n_2820_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___redArg(lean_object* v_inst_2825_, lean_object* v_xs_2826_, lean_object* v_a_2827_, lean_object* v_b_2828_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Array_replace___redArg(v_inst_2825_, v_xs_2826_, v_a_2827_, v_b_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace(lean_object* v_00_u03b1_2830_, lean_object* v_n_2831_, lean_object* v_inst_2832_, lean_object* v_xs_2833_, lean_object* v_a_2834_, lean_object* v_b_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Array_replace___redArg(v_inst_2832_, v_xs_2833_, v_a_2834_, v_b_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___boxed(lean_object* v_00_u03b1_2837_, lean_object* v_n_2838_, lean_object* v_inst_2839_, lean_object* v_xs_2840_, lean_object* v_a_2841_, lean_object* v_b_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Vector_replace(v_00_u03b1_2837_, v_n_2838_, v_inst_2839_, v_xs_2840_, v_a_2841_, v_b_2842_);
lean_dec(v_n_2838_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg___lam__0(lean_object* v_inst_2844_, lean_object* v_x1_2845_, lean_object* v_x2_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_apply_2(v_inst_2844_, v_x1_2845_, v_x2_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg(lean_object* v_inst_2848_, lean_object* v_inst_2849_, lean_object* v_xs_2850_){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v___x_2851_ = lean_array_get_size(v_xs_2850_);
v___x_2852_ = lean_unsigned_to_nat(0u);
v___x_2853_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2854_ = lean_nat_dec_lt(v___x_2852_, v___x_2851_);
if (v___x_2854_ == 0)
{
lean_dec_ref(v_xs_2850_);
lean_dec(v_inst_2848_);
return v_inst_2849_;
}
else
{
lean_object* v___f_2855_; size_t v___x_2856_; size_t v___x_2857_; lean_object* v___x_2858_; 
v___f_2855_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2855_, 0, v_inst_2848_);
v___x_2856_ = lean_usize_of_nat(v___x_2851_);
v___x_2857_ = ((size_t)0ULL);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2853_, v___f_2855_, v_xs_2850_, v___x_2856_, v___x_2857_, v_inst_2849_);
return v___x_2858_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum(lean_object* v_00_u03b1_2859_, lean_object* v_n_2860_, lean_object* v_inst_2861_, lean_object* v_inst_2862_, lean_object* v_xs_2863_){
_start:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2864_ = lean_array_get_size(v_xs_2863_);
v___x_2865_ = lean_unsigned_to_nat(0u);
v___x_2866_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2867_ = lean_nat_dec_lt(v___x_2865_, v___x_2864_);
if (v___x_2867_ == 0)
{
lean_dec_ref(v_xs_2863_);
lean_dec(v_inst_2861_);
return v_inst_2862_;
}
else
{
lean_object* v___f_2868_; size_t v___x_2869_; size_t v___x_2870_; lean_object* v___x_2871_; 
v___f_2868_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2868_, 0, v_inst_2861_);
v___x_2869_ = lean_usize_of_nat(v___x_2864_);
v___x_2870_ = ((size_t)0ULL);
v___x_2871_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2866_, v___f_2868_, v_xs_2863_, v___x_2869_, v___x_2870_, v_inst_2862_);
return v___x_2871_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum___boxed(lean_object* v_00_u03b1_2872_, lean_object* v_n_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_xs_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Vector_sum(v_00_u03b1_2872_, v_n_2873_, v_inst_2874_, v_inst_2875_, v_xs_2876_);
lean_dec(v_n_2873_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Vector_prod___redArg(lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_xs_2880_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2881_ = lean_array_get_size(v_xs_2880_);
v___x_2882_ = lean_unsigned_to_nat(0u);
v___x_2883_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2884_ = lean_nat_dec_lt(v___x_2882_, v___x_2881_);
if (v___x_2884_ == 0)
{
lean_dec_ref(v_xs_2880_);
lean_dec(v_inst_2878_);
return v_inst_2879_;
}
else
{
lean_object* v___f_2885_; size_t v___x_2886_; size_t v___x_2887_; lean_object* v___x_2888_; 
v___f_2885_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2885_, 0, v_inst_2878_);
v___x_2886_ = lean_usize_of_nat(v___x_2881_);
v___x_2887_ = ((size_t)0ULL);
v___x_2888_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2883_, v___f_2885_, v_xs_2880_, v___x_2886_, v___x_2887_, v_inst_2879_);
return v___x_2888_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod(lean_object* v_00_u03b1_2889_, lean_object* v_n_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_xs_2893_){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; 
v___x_2894_ = lean_array_get_size(v_xs_2893_);
v___x_2895_ = lean_unsigned_to_nat(0u);
v___x_2896_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2897_ = lean_nat_dec_lt(v___x_2895_, v___x_2894_);
if (v___x_2897_ == 0)
{
lean_dec_ref(v_xs_2893_);
lean_dec(v_inst_2891_);
return v_inst_2892_;
}
else
{
lean_object* v___f_2898_; size_t v___x_2899_; size_t v___x_2900_; lean_object* v___x_2901_; 
v___f_2898_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2898_, 0, v_inst_2891_);
v___x_2899_ = lean_usize_of_nat(v___x_2894_);
v___x_2900_ = ((size_t)0ULL);
v___x_2901_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2896_, v___f_2898_, v_xs_2893_, v___x_2899_, v___x_2900_, v_inst_2892_);
return v___x_2901_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod___boxed(lean_object* v_00_u03b1_2902_, lean_object* v_n_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_xs_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Vector_prod(v_00_u03b1_2902_, v_n_2903_, v_inst_2904_, v_inst_2905_, v_xs_2906_);
lean_dec(v_n_2903_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg(lean_object* v_m_2908_, lean_object* v_n_2909_, lean_object* v_a_2910_, lean_object* v_xs_2911_){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = lean_nat_sub(v_n_2909_, v_m_2908_);
v___x_2913_ = lean_mk_array(v___x_2912_, v_a_2910_);
v___x_2914_ = l_Array_append___redArg(v___x_2913_, v_xs_2911_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg___boxed(lean_object* v_m_2915_, lean_object* v_n_2916_, lean_object* v_a_2917_, lean_object* v_xs_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Vector_leftpad___redArg(v_m_2915_, v_n_2916_, v_a_2917_, v_xs_2918_);
lean_dec_ref(v_xs_2918_);
lean_dec(v_n_2916_);
lean_dec(v_m_2915_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad(lean_object* v_00_u03b1_2920_, lean_object* v_m_2921_, lean_object* v_n_2922_, lean_object* v_a_2923_, lean_object* v_xs_2924_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = lean_nat_sub(v_n_2922_, v_m_2921_);
v___x_2926_ = lean_mk_array(v___x_2925_, v_a_2923_);
v___x_2927_ = l_Array_append___redArg(v___x_2926_, v_xs_2924_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___boxed(lean_object* v_00_u03b1_2928_, lean_object* v_m_2929_, lean_object* v_n_2930_, lean_object* v_a_2931_, lean_object* v_xs_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Vector_leftpad(v_00_u03b1_2928_, v_m_2929_, v_n_2930_, v_a_2931_, v_xs_2932_);
lean_dec_ref(v_xs_2932_);
lean_dec(v_n_2930_);
lean_dec(v_m_2929_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg(lean_object* v_m_2934_, lean_object* v_n_2935_, lean_object* v_a_2936_, lean_object* v_xs_2937_){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = lean_nat_sub(v_n_2935_, v_m_2934_);
v___x_2939_ = lean_mk_array(v___x_2938_, v_a_2936_);
v___x_2940_ = l_Array_append___redArg(v_xs_2937_, v___x_2939_);
lean_dec_ref(v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg___boxed(lean_object* v_m_2941_, lean_object* v_n_2942_, lean_object* v_a_2943_, lean_object* v_xs_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Vector_rightpad___redArg(v_m_2941_, v_n_2942_, v_a_2943_, v_xs_2944_);
lean_dec(v_n_2942_);
lean_dec(v_m_2941_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad(lean_object* v_00_u03b1_2946_, lean_object* v_m_2947_, lean_object* v_n_2948_, lean_object* v_a_2949_, lean_object* v_xs_2950_){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_nat_sub(v_n_2948_, v_m_2947_);
v___x_2952_ = lean_mk_array(v___x_2951_, v_a_2949_);
v___x_2953_ = l_Array_append___redArg(v_xs_2950_, v___x_2952_);
lean_dec_ref(v___x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___boxed(lean_object* v_00_u03b1_2954_, lean_object* v_m_2955_, lean_object* v_n_2956_, lean_object* v_a_2957_, lean_object* v_xs_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Vector_rightpad(v_00_u03b1_2954_, v_m_2955_, v_n_2956_, v_a_2957_, v_xs_2958_);
lean_dec(v_n_2956_);
lean_dec(v_m_2955_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_f_2960_, lean_object* v_a_2961_, lean_object* v_h_2962_, lean_object* v_b_2963_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_apply_3(v_f_2960_, v_a_2961_, lean_box(0), v_b_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_inst_2965_, lean_object* v_00_u03b2_2966_, lean_object* v_xs_2967_, lean_object* v_b_2968_, lean_object* v_f_2969_){
_start:
{
lean_object* v___f_2970_; size_t v_sz_2971_; size_t v___x_2972_; lean_object* v___x_2973_; 
v___f_2970_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2970_, 0, v_f_2969_);
v_sz_2971_ = lean_array_size(v_xs_2967_);
v___x_2972_ = ((size_t)0ULL);
v___x_2973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2965_, v_xs_2967_, v___f_2970_, v_sz_2971_, v___x_2972_, v_b_2968_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_2974_){
_start:
{
lean_object* v___f_2975_; 
v___f_2975_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2975_, 0, v_inst_2974_);
return v___f_2975_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_2976_, lean_object* v_00_u03b1_2977_, lean_object* v_n_2978_, lean_object* v_inst_2979_){
_start:
{
lean_object* v___f_2980_; 
v___f_2980_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2980_, 0, v_inst_2979_);
return v___f_2980_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(lean_object* v_m_2981_, lean_object* v_00_u03b1_2982_, lean_object* v_n_2983_, lean_object* v_inst_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Vector_instForIn_x27InferInstanceMembershipOfMonad(v_m_2981_, v_00_u03b1_2982_, v_n_2983_, v_inst_2984_);
lean_dec(v_n_2983_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad___redArg(lean_object* v_n_2986_, lean_object* v_inst_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2988_, 0, lean_box(0));
lean_closure_set(v___x_2988_, 1, lean_box(0));
lean_closure_set(v___x_2988_, 2, v_n_2986_);
lean_closure_set(v___x_2988_, 3, v_inst_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad(lean_object* v_m_2989_, lean_object* v_00_u03b1_2990_, lean_object* v_n_2991_, lean_object* v_inst_2992_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2993_, 0, lean_box(0));
lean_closure_set(v___x_2993_, 1, lean_box(0));
lean_closure_set(v___x_2993_, 2, v_n_2991_);
lean_closure_set(v___x_2993_, 3, v_inst_2992_);
return v___x_2993_;
}
}
lean_object* l_Vector_instLT___redArg(){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_box(0);
return v___x_2995_;
}
}
LEAN_EXPORT void l_Vector_instLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2996_;
v_res_2996_ = l_Vector_instLT___redArg();
stack->m_obj
 = v_res_2996_;
}
LEAN_EXPORT lean_object* l_Vector_instLT___redArg___boxed(lean_object* v___dummy_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Vector_instLT___redArg();
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object* v_00_u03b1_2999_, lean_object* v_n_3000_, lean_object* v_inst_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_box(0);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object* v_00_u03b1_3003_, lean_object* v_n_3004_, lean_object* v_inst_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Vector_instLT(v_00_u03b1_3003_, v_n_3004_, v_inst_3005_);
lean_dec(v_n_3004_);
return v_res_3006_;
}
}
lean_object* l_Vector_instLE___redArg(){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_box(0);
return v___x_3008_;
}
}
LEAN_EXPORT void l_Vector_instLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3009_;
v_res_3009_ = l_Vector_instLE___redArg();
stack->m_obj
 = v_res_3009_;
}
LEAN_EXPORT lean_object* l_Vector_instLE___redArg___boxed(lean_object* v___dummy_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Vector_instLE___redArg();
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE(lean_object* v_00_u03b1_3012_, lean_object* v_n_3013_, lean_object* v_inst_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_box(0);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___boxed(lean_object* v_00_u03b1_3016_, lean_object* v_n_3017_, lean_object* v_inst_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Vector_instLE(v_00_u03b1_3016_, v_n_3017_, v_inst_3018_);
lean_dec(v_n_3017_);
return v_res_3019_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = ((lean_object*)(l_Vector_lex___auto__1___closed__0));
v___x_3027_ = l_Lean_mkAtom(v___x_3026_);
return v___x_3027_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3028_ = lean_obj_once(&l_Vector_lex___auto__1___closed__2, &l_Vector_lex___auto__1___closed__2_once, _init_l_Vector_lex___auto__1___closed__2);
v___x_3029_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3030_ = lean_array_push(v___x_3029_, v___x_3028_);
return v___x_3030_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_3044_ = l_Lean_mkAtom(v___x_3043_);
return v___x_3044_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = lean_obj_once(&l_Vector_lex___auto__1___closed__8, &l_Vector_lex___auto__1___closed__8_once, _init_l_Vector_lex___auto__1___closed__8);
v___x_3046_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3047_ = lean_array_push(v___x_3046_, v___x_3045_);
return v___x_3047_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = ((lean_object*)(l_Vector_lex___auto__1___closed__14));
v___x_3062_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3063_ = lean_array_push(v___x_3062_, v___x_3061_);
return v___x_3063_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3064_ = lean_obj_once(&l_Vector_lex___auto__1___closed__15, &l_Vector_lex___auto__1___closed__15_once, _init_l_Vector_lex___auto__1___closed__15);
v___x_3065_ = ((lean_object*)(l_Vector_lex___auto__1___closed__11));
v___x_3066_ = lean_box(2);
v___x_3067_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v___x_3065_);
lean_ctor_set(v___x_3067_, 2, v___x_3064_);
return v___x_3067_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_3069_ = lean_obj_once(&l_Vector_lex___auto__1___closed__9, &l_Vector_lex___auto__1___closed__9_once, _init_l_Vector_lex___auto__1___closed__9);
v___x_3070_ = lean_array_push(v___x_3069_, v___x_3068_);
return v___x_3070_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3071_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3072_ = ((lean_object*)(l_Vector_lex___auto__1___closed__7));
v___x_3073_ = lean_box(2);
v___x_3074_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v___x_3072_);
lean_ctor_set(v___x_3074_, 2, v___x_3071_);
return v___x_3074_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_obj_once(&l_Vector_lex___auto__1___closed__18, &l_Vector_lex___auto__1___closed__18_once, _init_l_Vector_lex___auto__1___closed__18);
v___x_3076_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3077_ = lean_array_push(v___x_3076_, v___x_3075_);
return v___x_3077_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = ((lean_object*)(l_Vector_lex___auto__1___closed__24));
v___x_3089_ = l_Lean_mkAtom(v___x_3088_);
return v___x_3089_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_obj_once(&l_Vector_lex___auto__1___closed__25, &l_Vector_lex___auto__1___closed__25_once, _init_l_Vector_lex___auto__1___closed__25);
v___x_3091_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3092_ = lean_array_push(v___x_3091_, v___x_3090_);
return v___x_3092_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_3094_ = lean_obj_once(&l_Vector_lex___auto__1___closed__26, &l_Vector_lex___auto__1___closed__26_once, _init_l_Vector_lex___auto__1___closed__26);
v___x_3095_ = lean_array_push(v___x_3094_, v___x_3093_);
return v___x_3095_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3096_ = lean_obj_once(&l_Vector_lex___auto__1___closed__27, &l_Vector_lex___auto__1___closed__27_once, _init_l_Vector_lex___auto__1___closed__27);
v___x_3097_ = ((lean_object*)(l_Vector_lex___auto__1___closed__23));
v___x_3098_ = lean_box(2);
v___x_3099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
lean_ctor_set(v___x_3099_, 1, v___x_3097_);
lean_ctor_set(v___x_3099_, 2, v___x_3096_);
return v___x_3099_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3101_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3102_ = lean_array_push(v___x_3101_, v___x_3100_);
return v___x_3102_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__31(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = ((lean_object*)(l_Vector_lex___auto__1___closed__30));
v___x_3105_ = l_Lean_mkAtom(v___x_3104_);
return v___x_3105_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = lean_obj_once(&l_Vector_lex___auto__1___closed__31, &l_Vector_lex___auto__1___closed__31_once, _init_l_Vector_lex___auto__1___closed__31);
v___x_3107_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3108_ = lean_array_push(v___x_3107_, v___x_3106_);
return v___x_3108_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__33(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3110_ = lean_obj_once(&l_Vector_lex___auto__1___closed__32, &l_Vector_lex___auto__1___closed__32_once, _init_l_Vector_lex___auto__1___closed__32);
v___x_3111_ = lean_array_push(v___x_3110_, v___x_3109_);
return v___x_3111_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__34(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3112_ = lean_obj_once(&l_Vector_lex___auto__1___closed__33, &l_Vector_lex___auto__1___closed__33_once, _init_l_Vector_lex___auto__1___closed__33);
v___x_3113_ = ((lean_object*)(l_Vector_lex___auto__1___closed__21));
v___x_3114_ = lean_box(2);
v___x_3115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
lean_ctor_set(v___x_3115_, 1, v___x_3113_);
lean_ctor_set(v___x_3115_, 2, v___x_3112_);
return v___x_3115_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__35(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3116_ = lean_obj_once(&l_Vector_lex___auto__1___closed__34, &l_Vector_lex___auto__1___closed__34_once, _init_l_Vector_lex___auto__1___closed__34);
v___x_3117_ = lean_obj_once(&l_Vector_lex___auto__1___closed__19, &l_Vector_lex___auto__1___closed__19_once, _init_l_Vector_lex___auto__1___closed__19);
v___x_3118_ = lean_array_push(v___x_3117_, v___x_3116_);
return v___x_3118_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__36(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_3120_ = l_Lean_mkAtom(v___x_3119_);
return v___x_3120_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3121_ = lean_obj_once(&l_Vector_lex___auto__1___closed__36, &l_Vector_lex___auto__1___closed__36_once, _init_l_Vector_lex___auto__1___closed__36);
v___x_3122_ = lean_obj_once(&l_Vector_lex___auto__1___closed__35, &l_Vector_lex___auto__1___closed__35_once, _init_l_Vector_lex___auto__1___closed__35);
v___x_3123_ = lean_array_push(v___x_3122_, v___x_3121_);
return v___x_3123_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3124_ = lean_obj_once(&l_Vector_lex___auto__1___closed__37, &l_Vector_lex___auto__1___closed__37_once, _init_l_Vector_lex___auto__1___closed__37);
v___x_3125_ = ((lean_object*)(l_Vector_lex___auto__1___closed__5));
v___x_3126_ = lean_box(2);
v___x_3127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
lean_ctor_set(v___x_3127_, 1, v___x_3125_);
lean_ctor_set(v___x_3127_, 2, v___x_3124_);
return v___x_3127_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = lean_obj_once(&l_Vector_lex___auto__1___closed__38, &l_Vector_lex___auto__1___closed__38_once, _init_l_Vector_lex___auto__1___closed__38);
v___x_3129_ = lean_obj_once(&l_Vector_lex___auto__1___closed__3, &l_Vector_lex___auto__1___closed__3_once, _init_l_Vector_lex___auto__1___closed__3);
v___x_3130_ = lean_array_push(v___x_3129_, v___x_3128_);
return v___x_3130_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3131_ = lean_obj_once(&l_Vector_lex___auto__1___closed__39, &l_Vector_lex___auto__1___closed__39_once, _init_l_Vector_lex___auto__1___closed__39);
v___x_3132_ = ((lean_object*)(l_Vector_lex___auto__1___closed__1));
v___x_3133_ = lean_box(2);
v___x_3134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
lean_ctor_set(v___x_3134_, 1, v___x_3132_);
lean_ctor_set(v___x_3134_, 2, v___x_3131_);
return v___x_3134_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_obj_once(&l_Vector_lex___auto__1___closed__40, &l_Vector_lex___auto__1___closed__40_once, _init_l_Vector_lex___auto__1___closed__40);
v___x_3136_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3137_ = lean_array_push(v___x_3136_, v___x_3135_);
return v___x_3137_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3138_ = lean_obj_once(&l_Vector_lex___auto__1___closed__41, &l_Vector_lex___auto__1___closed__41_once, _init_l_Vector_lex___auto__1___closed__41);
v___x_3139_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_3140_ = lean_box(2);
v___x_3141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v___x_3139_);
lean_ctor_set(v___x_3141_, 2, v___x_3138_);
return v___x_3141_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = lean_obj_once(&l_Vector_lex___auto__1___closed__42, &l_Vector_lex___auto__1___closed__42_once, _init_l_Vector_lex___auto__1___closed__42);
v___x_3143_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3144_ = lean_array_push(v___x_3143_, v___x_3142_);
return v___x_3144_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3145_ = lean_obj_once(&l_Vector_lex___auto__1___closed__43, &l_Vector_lex___auto__1___closed__43_once, _init_l_Vector_lex___auto__1___closed__43);
v___x_3146_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_3147_ = lean_box(2);
v___x_3148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v___x_3146_);
lean_ctor_set(v___x_3148_, 2, v___x_3145_);
return v___x_3148_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3149_ = lean_obj_once(&l_Vector_lex___auto__1___closed__44, &l_Vector_lex___auto__1___closed__44_once, _init_l_Vector_lex___auto__1___closed__44);
v___x_3150_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3151_ = lean_array_push(v___x_3150_, v___x_3149_);
return v___x_3151_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3152_ = lean_obj_once(&l_Vector_lex___auto__1___closed__45, &l_Vector_lex___auto__1___closed__45_once, _init_l_Vector_lex___auto__1___closed__45);
v___x_3153_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_3154_ = lean_box(2);
v___x_3155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
lean_ctor_set(v___x_3155_, 1, v___x_3153_);
lean_ctor_set(v___x_3155_, 2, v___x_3152_);
return v___x_3155_;
}
}
static lean_object* _init_l_Vector_lex___auto__1(void){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_obj_once(&l_Vector_lex___auto__1___closed__46, &l_Vector_lex___auto__1___closed__46_once, _init_l_Vector_lex___auto__1___closed__46);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0(lean_object* v_n_3157_, lean_object* v_xs_3158_, lean_object* v_ys_3159_, lean_object* v_lt_3160_, lean_object* v_inst_3161_, lean_object* v___x_3162_, lean_object* v___x_3163_, lean_object* v_next_3164_, lean_object* v_acc_3165_, lean_object* v_h_3166_, lean_object* v_G_3167_){
_start:
{
uint8_t v___x_3168_; 
v___x_3168_ = lean_nat_dec_lt(v_next_3164_, v_n_3157_);
if (v___x_3168_ == 0)
{
lean_dec_ref(v_G_3167_);
lean_dec_ref(v___x_3163_);
lean_dec_ref(v_inst_3161_);
lean_dec_ref(v_lt_3160_);
lean_inc_ref(v_acc_3165_);
return v_acc_3165_;
}
else
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v___x_3169_ = lean_array_fget_borrowed(v_xs_3158_, v_next_3164_);
v___x_3170_ = lean_array_fget_borrowed(v_ys_3159_, v_next_3164_);
lean_inc(v___x_3170_);
lean_inc(v___x_3169_);
v___x_3171_ = lean_apply_2(v_lt_3160_, v___x_3169_, v___x_3170_);
v___x_3172_ = lean_unbox(v___x_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; uint8_t v___x_3174_; 
lean_inc(v___x_3170_);
lean_inc(v___x_3169_);
v___x_3173_ = lean_apply_2(v_inst_3161_, v___x_3169_, v___x_3170_);
v___x_3174_ = lean_unbox(v___x_3173_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_dec_ref(v_G_3167_);
lean_dec_ref(v___x_3163_);
v___x_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3171_);
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v___x_3162_);
return v___x_3176_;
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = lean_unsigned_to_nat(1u);
v___x_3178_ = lean_nat_add(v_next_3164_, v___x_3177_);
v___x_3179_ = lean_apply_4(v_G_3167_, v___x_3178_, v___x_3163_, lean_box(0), lean_box(0));
return v___x_3179_;
}
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec_ref(v_G_3167_);
lean_dec_ref(v___x_3163_);
lean_dec_ref(v_inst_3161_);
v___x_3180_ = lean_box(v___x_3168_);
v___x_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
lean_ctor_set(v___x_3182_, 1, v___x_3162_);
return v___x_3182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0___boxed(lean_object* v_n_3183_, lean_object* v_xs_3184_, lean_object* v_ys_3185_, lean_object* v_lt_3186_, lean_object* v_inst_3187_, lean_object* v___x_3188_, lean_object* v___x_3189_, lean_object* v_next_3190_, lean_object* v_acc_3191_, lean_object* v_h_3192_, lean_object* v_G_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Vector_lex___redArg___lam__0(v_n_3183_, v_xs_3184_, v_ys_3185_, v_lt_3186_, v_inst_3187_, v___x_3188_, v___x_3189_, v_next_3190_, v_acc_3191_, v_h_3192_, v_G_3193_);
lean_dec_ref(v_acc_3191_);
lean_dec(v_next_3190_);
lean_dec_ref(v_ys_3185_);
lean_dec_ref(v_xs_3184_);
lean_dec(v_n_3183_);
return v_res_3194_;
}
}
uint8_t l_Vector_lex___redArg(lean_object* v_n_3198_, lean_object* v_inst_3199_, lean_object* v_xs_3200_, lean_object* v_ys_3201_, lean_object* v_lt_3202_){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___f_3206_; lean_object* v___x_3207_; lean_object* v_fst_3208_; 
v___x_3203_ = lean_unsigned_to_nat(0u);
v___x_3204_ = lean_box(0);
v___x_3205_ = ((lean_object*)(l_Vector_lex___redArg___closed__0));
v___f_3206_ = lean_alloc_closure((void*)(l_Vector_lex___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_3206_, 0, v_n_3198_);
lean_closure_set(v___f_3206_, 1, v_xs_3200_);
lean_closure_set(v___f_3206_, 2, v_ys_3201_);
lean_closure_set(v___f_3206_, 3, v_lt_3202_);
lean_closure_set(v___f_3206_, 4, v_inst_3199_);
lean_closure_set(v___f_3206_, 5, v___x_3204_);
lean_closure_set(v___f_3206_, 6, v___x_3205_);
v___x_3207_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3206_, v___x_3203_, v___x_3205_, lean_box(0));
v_fst_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_fst_3208_);
lean_dec(v___x_3207_);
if (lean_obj_tag(v_fst_3208_) == 0)
{
uint8_t v___x_3209_; 
v___x_3209_ = 0;
return v___x_3209_;
}
else
{
lean_object* v_val_3210_; uint8_t v___x_3211_; 
v_val_3210_ = lean_ctor_get(v_fst_3208_, 0);
lean_inc(v_val_3210_);
lean_dec_ref_known(v_fst_3208_, 1);
v___x_3211_ = lean_unbox(v_val_3210_);
lean_dec(v_val_3210_);
return v___x_3211_;
}
}
}
LEAN_EXPORT void l_Vector_lex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3198_ = stack[0].m_obj;
lean_object* v_inst_3199_ = stack[1].m_obj;
lean_object* v_xs_3200_ = stack[2].m_obj;
lean_object* v_ys_3201_ = stack[3].m_obj;
lean_object* v_lt_3202_ = stack[4].m_obj;
uint8_t v_res_3212_;
v_res_3212_ = l_Vector_lex___redArg(v_n_3198_, v_inst_3199_, v_xs_3200_, v_ys_3201_, v_lt_3202_);
stack->m_num = v_res_3212_;
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object* v_n_3213_, lean_object* v_inst_3214_, lean_object* v_xs_3215_, lean_object* v_ys_3216_, lean_object* v_lt_3217_){
_start:
{
uint8_t v_res_3218_; lean_object* v_r_3219_; 
v_res_3218_ = l_Vector_lex___redArg(v_n_3213_, v_inst_3214_, v_xs_3215_, v_ys_3216_, v_lt_3217_);
v_r_3219_ = lean_box(v_res_3218_);
return v_r_3219_;
}
}
uint8_t l_Vector_lex(lean_object* v_00_u03b1_3220_, lean_object* v_n_3221_, lean_object* v_inst_3222_, lean_object* v_xs_3223_, lean_object* v_ys_3224_, lean_object* v_lt_3225_){
_start:
{
uint8_t v___x_3226_; 
v___x_3226_ = l_Vector_lex___redArg(v_n_3221_, v_inst_3222_, v_xs_3223_, v_ys_3224_, v_lt_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT void l_Vector_lex_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3221_ = stack[1].m_obj;
lean_object* v_inst_3222_ = stack[2].m_obj;
lean_object* v_xs_3223_ = stack[3].m_obj;
lean_object* v_ys_3224_ = stack[4].m_obj;
lean_object* v_lt_3225_ = stack[5].m_obj;
uint8_t v_res_3227_;
v_res_3227_ = l_Vector_lex(lean_box(0), v_n_3221_, v_inst_3222_, v_xs_3223_, v_ys_3224_, v_lt_3225_);
stack->m_num = v_res_3227_;
}
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object* v_00_u03b1_3228_, lean_object* v_n_3229_, lean_object* v_inst_3230_, lean_object* v_xs_3231_, lean_object* v_ys_3232_, lean_object* v_lt_3233_){
_start:
{
uint8_t v_res_3234_; lean_object* v_r_3235_; 
v_res_3234_ = l_Vector_lex(v_00_u03b1_3228_, v_n_3229_, v_inst_3230_, v_xs_3231_, v_ys_3232_, v_lt_3233_);
v_r_3235_ = lean_box(v_res_3234_);
return v_r_3235_;
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
