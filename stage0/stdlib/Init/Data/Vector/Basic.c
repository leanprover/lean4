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
static lean_object* _init_l_Vector_set___auto__1___closed__9(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l_Vector_set___auto__1___closed__8));
v___x_636_ = l_Lean_mkAtom(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__10(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_obj_once(&l_Vector_set___auto__1___closed__9, &l_Vector_set___auto__1___closed__9_once, _init_l_Vector_set___auto__1___closed__9);
v___x_638_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_639_ = lean_array_push(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__11(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = lean_obj_once(&l_Vector_set___auto__1___closed__10, &l_Vector_set___auto__1___closed__10_once, _init_l_Vector_set___auto__1___closed__10);
v___x_641_ = ((lean_object*)(l_Vector_set___auto__1___closed__7));
v___x_642_ = lean_box(2);
v___x_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
lean_ctor_set(v___x_643_, 2, v___x_640_);
return v___x_643_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__12(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_obj_once(&l_Vector_set___auto__1___closed__11, &l_Vector_set___auto__1___closed__11_once, _init_l_Vector_set___auto__1___closed__11);
v___x_645_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_646_ = lean_array_push(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__13(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_647_ = lean_obj_once(&l_Vector_set___auto__1___closed__12, &l_Vector_set___auto__1___closed__12_once, _init_l_Vector_set___auto__1___closed__12);
v___x_648_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_649_ = lean_box(2);
v___x_650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v___x_648_);
lean_ctor_set(v___x_650_, 2, v___x_647_);
return v___x_650_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__14(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = lean_obj_once(&l_Vector_set___auto__1___closed__13, &l_Vector_set___auto__1___closed__13_once, _init_l_Vector_set___auto__1___closed__13);
v___x_652_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_653_ = lean_array_push(v___x_652_, v___x_651_);
return v___x_653_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__15(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = lean_obj_once(&l_Vector_set___auto__1___closed__14, &l_Vector_set___auto__1___closed__14_once, _init_l_Vector_set___auto__1___closed__14);
v___x_655_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_656_ = lean_box(2);
v___x_657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
lean_ctor_set(v___x_657_, 2, v___x_654_);
return v___x_657_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__16(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_658_ = lean_obj_once(&l_Vector_set___auto__1___closed__15, &l_Vector_set___auto__1___closed__15_once, _init_l_Vector_set___auto__1___closed__15);
v___x_659_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_660_ = lean_array_push(v___x_659_, v___x_658_);
return v___x_660_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__17(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_661_ = lean_obj_once(&l_Vector_set___auto__1___closed__16, &l_Vector_set___auto__1___closed__16_once, _init_l_Vector_set___auto__1___closed__16);
v___x_662_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_663_ = lean_box(2);
v___x_664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___x_662_);
lean_ctor_set(v___x_664_, 2, v___x_661_);
return v___x_664_;
}
}
static lean_object* _init_l_Vector_set___auto__1(void){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg(lean_object* v_xs_666_, lean_object* v_i_667_, lean_object* v_x_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = lean_array_fset(v_xs_666_, v_i_667_, v_x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg___boxed(lean_object* v_xs_670_, lean_object* v_i_671_, lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Vector_set___redArg(v_xs_670_, v_i_671_, v_x_672_);
lean_dec(v_i_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Vector_set(lean_object* v_00_u03b1_674_, lean_object* v_n_675_, lean_object* v_xs_676_, lean_object* v_i_677_, lean_object* v_x_678_, lean_object* v_h_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = lean_array_fset(v_xs_676_, v_i_677_, v_x_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___boxed(lean_object* v_00_u03b1_681_, lean_object* v_n_682_, lean_object* v_xs_683_, lean_object* v_i_684_, lean_object* v_x_685_, lean_object* v_h_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Vector_set(v_00_u03b1_681_, v_n_682_, v_xs_683_, v_i_684_, v_x_685_, v_h_686_);
lean_dec(v_i_684_);
lean_dec(v_n_682_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg(lean_object* v_xs_688_, lean_object* v_i_689_, lean_object* v_x_690_){
_start:
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_array_get_size(v_xs_688_);
v___x_692_ = lean_nat_dec_lt(v_i_689_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec(v_x_690_);
return v_xs_688_;
}
else
{
lean_object* v___x_693_; 
v___x_693_ = lean_array_fset(v_xs_688_, v_i_689_, v_x_690_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg___boxed(lean_object* v_xs_694_, lean_object* v_i_695_, lean_object* v_x_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Vector_setIfInBounds___redArg(v_xs_694_, v_i_695_, v_x_696_);
lean_dec(v_i_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds(lean_object* v_00_u03b1_698_, lean_object* v_n_699_, lean_object* v_xs_700_, lean_object* v_i_701_, lean_object* v_x_702_){
_start:
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_array_get_size(v_xs_700_);
v___x_704_ = lean_nat_dec_lt(v_i_701_, v___x_703_);
if (v___x_704_ == 0)
{
lean_dec(v_x_702_);
return v_xs_700_;
}
else
{
lean_object* v___x_705_; 
v___x_705_ = lean_array_fset(v_xs_700_, v_i_701_, v_x_702_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___boxed(lean_object* v_00_u03b1_706_, lean_object* v_n_707_, lean_object* v_xs_708_, lean_object* v_i_709_, lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Vector_setIfInBounds(v_00_u03b1_706_, v_n_707_, v_xs_708_, v_i_709_, v_x_710_);
lean_dec(v_i_709_);
lean_dec(v_n_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg(lean_object* v_xs_712_, lean_object* v_i_713_, lean_object* v_x_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = lean_array_set(v_xs_712_, v_i_713_, v_x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg___boxed(lean_object* v_xs_716_, lean_object* v_i_717_, lean_object* v_x_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Vector_set_x21___redArg(v_xs_716_, v_i_717_, v_x_718_);
lean_dec(v_i_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21(lean_object* v_00_u03b1_720_, lean_object* v_n_721_, lean_object* v_xs_722_, lean_object* v_i_723_, lean_object* v_x_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = lean_array_set(v_xs_722_, v_i_723_, v_x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___boxed(lean_object* v_00_u03b1_726_, lean_object* v_n_727_, lean_object* v_xs_728_, lean_object* v_i_729_, lean_object* v_x_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Vector_set_x21(v_00_u03b1_726_, v_n_727_, v_xs_728_, v_i_729_, v_x_730_);
lean_dec(v_i_729_);
lean_dec(v_n_727_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___redArg(lean_object* v_inst_732_, lean_object* v_f_733_, lean_object* v_b_734_, lean_object* v_xs_735_){
_start:
{
lean_object* v_toApplicative_736_; lean_object* v_toPure_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_toApplicative_736_ = lean_ctor_get(v_inst_732_, 0);
v_toPure_737_ = lean_ctor_get(v_toApplicative_736_, 1);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_array_get_size(v_xs_735_);
v___x_740_ = lean_nat_dec_lt(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_inc(v_toPure_737_);
lean_dec_ref(v_xs_735_);
lean_dec(v_f_733_);
lean_dec_ref(v_inst_732_);
v___x_741_ = lean_apply_2(v_toPure_737_, lean_box(0), v_b_734_);
return v___x_741_;
}
else
{
uint8_t v___x_742_; 
v___x_742_ = lean_nat_dec_le(v___x_739_, v___x_739_);
if (v___x_742_ == 0)
{
if (v___x_740_ == 0)
{
lean_object* v___x_743_; 
lean_inc(v_toPure_737_);
lean_dec_ref(v_xs_735_);
lean_dec(v_f_733_);
lean_dec_ref(v_inst_732_);
v___x_743_ = lean_apply_2(v_toPure_737_, lean_box(0), v_b_734_);
return v___x_743_;
}
else
{
size_t v___x_744_; size_t v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((size_t)0ULL);
v___x_745_ = lean_usize_of_nat(v___x_739_);
v___x_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_732_, v_f_733_, v_xs_735_, v___x_744_, v___x_745_, v_b_734_);
return v___x_746_;
}
}
else
{
size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = ((size_t)0ULL);
v___x_748_ = lean_usize_of_nat(v___x_739_);
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_732_, v_f_733_, v_xs_735_, v___x_747_, v___x_748_, v_b_734_);
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM(lean_object* v_m_750_, lean_object* v_00_u03b2_751_, lean_object* v_00_u03b1_752_, lean_object* v_n_753_, lean_object* v_inst_754_, lean_object* v_f_755_, lean_object* v_b_756_, lean_object* v_xs_757_){
_start:
{
lean_object* v_toApplicative_758_; lean_object* v_toPure_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_toApplicative_758_ = lean_ctor_get(v_inst_754_, 0);
v_toPure_759_ = lean_ctor_get(v_toApplicative_758_, 1);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_array_get_size(v_xs_757_);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
lean_inc(v_toPure_759_);
lean_dec_ref(v_xs_757_);
lean_dec(v_f_755_);
lean_dec_ref(v_inst_754_);
v___x_763_ = lean_apply_2(v_toPure_759_, lean_box(0), v_b_756_);
return v___x_763_;
}
else
{
uint8_t v___x_764_; 
v___x_764_ = lean_nat_dec_le(v___x_761_, v___x_761_);
if (v___x_764_ == 0)
{
if (v___x_762_ == 0)
{
lean_object* v___x_765_; 
lean_inc(v_toPure_759_);
lean_dec_ref(v_xs_757_);
lean_dec(v_f_755_);
lean_dec_ref(v_inst_754_);
v___x_765_ = lean_apply_2(v_toPure_759_, lean_box(0), v_b_756_);
return v___x_765_;
}
else
{
size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___x_766_ = ((size_t)0ULL);
v___x_767_ = lean_usize_of_nat(v___x_761_);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_754_, v_f_755_, v_xs_757_, v___x_766_, v___x_767_, v_b_756_);
return v___x_768_;
}
}
else
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((size_t)0ULL);
v___x_770_ = lean_usize_of_nat(v___x_761_);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_754_, v_f_755_, v_xs_757_, v___x_769_, v___x_770_, v_b_756_);
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___boxed(lean_object* v_m_772_, lean_object* v_00_u03b2_773_, lean_object* v_00_u03b1_774_, lean_object* v_n_775_, lean_object* v_inst_776_, lean_object* v_f_777_, lean_object* v_b_778_, lean_object* v_xs_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Vector_foldlM(v_m_772_, v_00_u03b2_773_, v_00_u03b1_774_, v_n_775_, v_inst_776_, v_f_777_, v_b_778_, v_xs_779_);
lean_dec(v_n_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___redArg(lean_object* v_inst_781_, lean_object* v_f_782_, lean_object* v_b_783_, lean_object* v_xs_784_){
_start:
{
lean_object* v_toApplicative_785_; lean_object* v_toPure_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_toApplicative_785_ = lean_ctor_get(v_inst_781_, 0);
v_toPure_786_ = lean_ctor_get(v_toApplicative_785_, 1);
v___x_787_ = lean_array_get_size(v_xs_784_);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = lean_nat_dec_lt(v___x_788_, v___x_787_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
lean_inc(v_toPure_786_);
lean_dec_ref(v_xs_784_);
lean_dec(v_f_782_);
lean_dec_ref(v_inst_781_);
v___x_790_ = lean_apply_2(v_toPure_786_, lean_box(0), v_b_783_);
return v___x_790_;
}
else
{
size_t v___x_791_; size_t v___x_792_; lean_object* v___x_793_; 
v___x_791_ = lean_usize_of_nat(v___x_787_);
v___x_792_ = ((size_t)0ULL);
v___x_793_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_781_, v_f_782_, v_xs_784_, v___x_791_, v___x_792_, v_b_783_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM(lean_object* v_m_794_, lean_object* v_00_u03b1_795_, lean_object* v_00_u03b2_796_, lean_object* v_n_797_, lean_object* v_inst_798_, lean_object* v_f_799_, lean_object* v_b_800_, lean_object* v_xs_801_){
_start:
{
lean_object* v_toApplicative_802_; lean_object* v_toPure_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_toApplicative_802_ = lean_ctor_get(v_inst_798_, 0);
v_toPure_803_ = lean_ctor_get(v_toApplicative_802_, 1);
v___x_804_ = lean_array_get_size(v_xs_801_);
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = lean_nat_dec_lt(v___x_805_, v___x_804_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_inc(v_toPure_803_);
lean_dec_ref(v_xs_801_);
lean_dec(v_f_799_);
lean_dec_ref(v_inst_798_);
v___x_807_ = lean_apply_2(v_toPure_803_, lean_box(0), v_b_800_);
return v___x_807_;
}
else
{
size_t v___x_808_; size_t v___x_809_; lean_object* v___x_810_; 
v___x_808_ = lean_usize_of_nat(v___x_804_);
v___x_809_ = ((size_t)0ULL);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_798_, v_f_799_, v_xs_801_, v___x_808_, v___x_809_, v_b_800_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___boxed(lean_object* v_m_811_, lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_n_814_, lean_object* v_inst_815_, lean_object* v_f_816_, lean_object* v_b_817_, lean_object* v_xs_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Vector_foldrM(v_m_811_, v_00_u03b1_812_, v_00_u03b2_813_, v_n_814_, v_inst_815_, v_f_816_, v_b_817_, v_xs_818_);
lean_dec(v_n_814_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg___lam__0(lean_object* v_f_820_, lean_object* v_x1_821_, lean_object* v_x2_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = lean_apply_2(v_f_820_, v_x1_821_, v_x2_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg(lean_object* v_f_843_, lean_object* v_b_844_, lean_object* v_xs_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_array_get_size(v_xs_845_);
v___x_848_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_849_ = lean_nat_dec_lt(v___x_846_, v___x_847_);
if (v___x_849_ == 0)
{
lean_dec_ref(v_xs_845_);
lean_dec(v_f_843_);
return v_b_844_;
}
else
{
lean_object* v___f_850_; uint8_t v___x_851_; 
v___f_850_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_850_, 0, v_f_843_);
v___x_851_ = lean_nat_dec_le(v___x_847_, v___x_847_);
if (v___x_851_ == 0)
{
if (v___x_849_ == 0)
{
lean_dec_ref(v___f_850_);
lean_dec_ref(v_xs_845_);
return v_b_844_;
}
else
{
size_t v___x_852_; size_t v___x_853_; lean_object* v___x_854_; 
v___x_852_ = ((size_t)0ULL);
v___x_853_ = lean_usize_of_nat(v___x_847_);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_848_, v___f_850_, v_xs_845_, v___x_852_, v___x_853_, v_b_844_);
return v___x_854_;
}
}
else
{
size_t v___x_855_; size_t v___x_856_; lean_object* v___x_857_; 
v___x_855_ = ((size_t)0ULL);
v___x_856_ = lean_usize_of_nat(v___x_847_);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_848_, v___f_850_, v_xs_845_, v___x_855_, v___x_856_, v_b_844_);
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl(lean_object* v_00_u03b2_858_, lean_object* v_00_u03b1_859_, lean_object* v_n_860_, lean_object* v_f_861_, lean_object* v_b_862_, lean_object* v_xs_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = lean_array_get_size(v_xs_863_);
v___x_866_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_867_ = lean_nat_dec_lt(v___x_864_, v___x_865_);
if (v___x_867_ == 0)
{
lean_dec_ref(v_xs_863_);
lean_dec(v_f_861_);
return v_b_862_;
}
else
{
lean_object* v___f_868_; uint8_t v___x_869_; 
v___f_868_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_868_, 0, v_f_861_);
v___x_869_ = lean_nat_dec_le(v___x_865_, v___x_865_);
if (v___x_869_ == 0)
{
if (v___x_867_ == 0)
{
lean_dec_ref(v___f_868_);
lean_dec_ref(v_xs_863_);
return v_b_862_;
}
else
{
size_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; 
v___x_870_ = ((size_t)0ULL);
v___x_871_ = lean_usize_of_nat(v___x_865_);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_866_, v___f_868_, v_xs_863_, v___x_870_, v___x_871_, v_b_862_);
return v___x_872_;
}
}
else
{
size_t v___x_873_; size_t v___x_874_; lean_object* v___x_875_; 
v___x_873_ = ((size_t)0ULL);
v___x_874_ = lean_usize_of_nat(v___x_865_);
v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_866_, v___f_868_, v_xs_863_, v___x_873_, v___x_874_, v_b_862_);
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___boxed(lean_object* v_00_u03b2_876_, lean_object* v_00_u03b1_877_, lean_object* v_n_878_, lean_object* v_f_879_, lean_object* v_b_880_, lean_object* v_xs_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Vector_foldl(v_00_u03b2_876_, v_00_u03b1_877_, v_n_878_, v_f_879_, v_b_880_, v_xs_881_);
lean_dec(v_n_878_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___redArg(lean_object* v_f_883_, lean_object* v_b_884_, lean_object* v_xs_885_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_886_ = lean_array_get_size(v_xs_885_);
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_889_ = lean_nat_dec_lt(v___x_887_, v___x_886_);
if (v___x_889_ == 0)
{
lean_dec_ref(v_xs_885_);
lean_dec(v_f_883_);
return v_b_884_;
}
else
{
lean_object* v___f_890_; size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; 
v___f_890_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_890_, 0, v_f_883_);
v___x_891_ = lean_usize_of_nat(v___x_886_);
v___x_892_ = ((size_t)0ULL);
v___x_893_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_888_, v___f_890_, v_xs_885_, v___x_891_, v___x_892_, v_b_884_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr(lean_object* v_00_u03b1_894_, lean_object* v_00_u03b2_895_, lean_object* v_n_896_, lean_object* v_f_897_, lean_object* v_b_898_, lean_object* v_xs_899_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_900_ = lean_array_get_size(v_xs_899_);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_903_ = lean_nat_dec_lt(v___x_901_, v___x_900_);
if (v___x_903_ == 0)
{
lean_dec_ref(v_xs_899_);
lean_dec(v_f_897_);
return v_b_898_;
}
else
{
lean_object* v___f_904_; size_t v___x_905_; size_t v___x_906_; lean_object* v___x_907_; 
v___f_904_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_904_, 0, v_f_897_);
v___x_905_ = lean_usize_of_nat(v___x_900_);
v___x_906_ = ((size_t)0ULL);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_902_, v___f_904_, v_xs_899_, v___x_905_, v___x_906_, v_b_898_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___boxed(lean_object* v_00_u03b1_908_, lean_object* v_00_u03b2_909_, lean_object* v_n_910_, lean_object* v_f_911_, lean_object* v_b_912_, lean_object* v_xs_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Vector_foldr(v_00_u03b1_908_, v_00_u03b2_909_, v_n_910_, v_f_911_, v_b_912_, v_xs_913_);
lean_dec(v_n_910_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg(lean_object* v_xs_915_, lean_object* v_ys_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Array_append___redArg(v_xs_915_, v_ys_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg___boxed(lean_object* v_xs_918_, lean_object* v_ys_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Vector_append___redArg(v_xs_918_, v_ys_919_);
lean_dec_ref(v_ys_919_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Vector_append(lean_object* v_00_u03b1_921_, lean_object* v_n_922_, lean_object* v_m_923_, lean_object* v_xs_924_, lean_object* v_ys_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Array_append___redArg(v_xs_924_, v_ys_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___boxed(lean_object* v_00_u03b1_927_, lean_object* v_n_928_, lean_object* v_m_929_, lean_object* v_xs_930_, lean_object* v_ys_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Vector_append(v_00_u03b1_927_, v_n_928_, v_m_929_, v_xs_930_, v_ys_931_);
lean_dec_ref(v_ys_931_);
lean_dec(v_m_929_);
lean_dec(v_n_928_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat___redArg(lean_object* v_n_933_, lean_object* v_m_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_935_, 0, lean_box(0));
lean_closure_set(v___x_935_, 1, v_n_933_);
lean_closure_set(v___x_935_, 2, v_m_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat(lean_object* v_00_u03b1_936_, lean_object* v_n_937_, lean_object* v_m_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_939_, 0, lean_box(0));
lean_closure_set(v___x_939_, 1, v_n_937_);
lean_closure_set(v___x_939_, 2, v_m_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg(lean_object* v_xs_940_){
_start:
{
lean_inc_ref(v_xs_940_);
return v_xs_940_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg___boxed(lean_object* v_xs_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Vector_cast___redArg(v_xs_941_);
lean_dec_ref(v_xs_941_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast(lean_object* v_n_943_, lean_object* v_m_944_, lean_object* v_00_u03b1_945_, lean_object* v_h_946_, lean_object* v_xs_947_){
_start:
{
lean_inc_ref(v_xs_947_);
return v_xs_947_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___boxed(lean_object* v_n_948_, lean_object* v_m_949_, lean_object* v_00_u03b1_950_, lean_object* v_h_951_, lean_object* v_xs_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Vector_cast(v_n_948_, v_m_949_, v_00_u03b1_950_, v_h_951_, v_xs_952_);
lean_dec_ref(v_xs_952_);
lean_dec(v_m_949_);
lean_dec(v_n_948_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg(lean_object* v_xs_954_, lean_object* v_start_955_, lean_object* v_stop_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Array_extract___redArg(v_xs_954_, v_start_955_, v_stop_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg___boxed(lean_object* v_xs_958_, lean_object* v_start_959_, lean_object* v_stop_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Vector_extract___redArg(v_xs_958_, v_start_959_, v_stop_960_);
lean_dec_ref(v_xs_958_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract(lean_object* v_00_u03b1_962_, lean_object* v_n_963_, lean_object* v_xs_964_, lean_object* v_start_965_, lean_object* v_stop_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Array_extract___redArg(v_xs_964_, v_start_965_, v_stop_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___boxed(lean_object* v_00_u03b1_968_, lean_object* v_n_969_, lean_object* v_xs_970_, lean_object* v_start_971_, lean_object* v_stop_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Vector_extract(v_00_u03b1_968_, v_n_969_, v_xs_970_, v_start_971_, v_stop_972_);
lean_dec_ref(v_xs_970_);
lean_dec(v_n_969_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg(lean_object* v_n_974_, lean_object* v_xs_975_, lean_object* v_i_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = l_Array_extract___redArg(v_xs_975_, v___x_977_, v_i_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg___boxed(lean_object* v_n_979_, lean_object* v_xs_980_, lean_object* v_i_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Vector_take___redArg(v_n_979_, v_xs_980_, v_i_981_);
lean_dec_ref(v_xs_980_);
lean_dec(v_n_979_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Vector_take(lean_object* v_00_u03b1_983_, lean_object* v_n_984_, lean_object* v_xs_985_, lean_object* v_i_986_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = l_Array_extract___redArg(v_xs_985_, v___x_987_, v_i_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___boxed(lean_object* v_00_u03b1_989_, lean_object* v_n_990_, lean_object* v_xs_991_, lean_object* v_i_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Vector_take(v_00_u03b1_989_, v_n_990_, v_xs_991_, v_i_992_);
lean_dec_ref(v_xs_991_);
lean_dec(v_n_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg(lean_object* v_xs_994_, lean_object* v_i_995_){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_array_get_size(v_xs_994_);
v___x_997_ = l_Array_extract___redArg(v_xs_994_, v_i_995_, v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg___boxed(lean_object* v_xs_998_, lean_object* v_i_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Vector_drop___redArg(v_xs_998_, v_i_999_);
lean_dec_ref(v_xs_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop(lean_object* v_00_u03b1_1001_, lean_object* v_n_1002_, lean_object* v_xs_1003_, lean_object* v_i_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_array_get_size(v_xs_1003_);
v___x_1006_ = l_Array_extract___redArg(v_xs_1003_, v_i_1004_, v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___boxed(lean_object* v_00_u03b1_1007_, lean_object* v_n_1008_, lean_object* v_xs_1009_, lean_object* v_i_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Vector_drop(v_00_u03b1_1007_, v_n_1008_, v_xs_1009_, v_i_1010_);
lean_dec_ref(v_xs_1009_);
lean_dec(v_n_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg(lean_object* v_xs_1012_, lean_object* v_i_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Array_shrink___redArg(v_xs_1012_, v_i_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg___boxed(lean_object* v_xs_1015_, lean_object* v_i_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Vector_shrink___redArg(v_xs_1015_, v_i_1016_);
lean_dec(v_i_1016_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink(lean_object* v_00_u03b1_1018_, lean_object* v_n_1019_, lean_object* v_xs_1020_, lean_object* v_i_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Array_shrink___redArg(v_xs_1020_, v_i_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___boxed(lean_object* v_00_u03b1_1023_, lean_object* v_n_1024_, lean_object* v_xs_1025_, lean_object* v_i_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Vector_shrink(v_00_u03b1_1023_, v_n_1024_, v_xs_1025_, v_i_1026_);
lean_dec(v_i_1026_);
lean_dec(v_n_1024_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg___lam__0(lean_object* v_f_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_apply_1(v_f_1028_, v_x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg(lean_object* v_f_1031_, lean_object* v_xs_1032_){
_start:
{
lean_object* v___f_1033_; lean_object* v___x_1034_; size_t v_sz_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
v___f_1033_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1033_, 0, v_f_1031_);
v___x_1034_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1035_ = lean_array_size(v_xs_1032_);
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1034_, v___f_1033_, v_sz_1035_, v___x_1036_, v_xs_1032_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Vector_map(lean_object* v_00_u03b1_1038_, lean_object* v_00_u03b2_1039_, lean_object* v_n_1040_, lean_object* v_f_1041_, lean_object* v_xs_1042_){
_start:
{
lean_object* v___f_1043_; lean_object* v___x_1044_; size_t v_sz_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v___f_1043_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1043_, 0, v_f_1041_);
v___x_1044_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1045_ = lean_array_size(v_xs_1042_);
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1044_, v___f_1043_, v_sz_1045_, v___x_1046_, v_xs_1042_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___boxed(lean_object* v_00_u03b1_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_n_1050_, lean_object* v_f_1051_, lean_object* v_xs_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Vector_map(v_00_u03b1_1048_, v_00_u03b2_1049_, v_n_1050_, v_f_1051_, v_xs_1052_);
lean_dec(v_n_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg___lam__0(lean_object* v_f_1054_, lean_object* v_i_1055_, lean_object* v_a_1056_, lean_object* v_x_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_apply_2(v_f_1054_, v_i_1055_, v_a_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg(lean_object* v_f_1059_, lean_object* v_xs_1060_){
_start:
{
lean_object* v___f_1061_; lean_object* v___x_1062_; size_t v_sz_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
v___f_1061_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1061_, 0, v_f_1059_);
v___x_1062_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1063_ = lean_array_size(v_xs_1060_);
v___x_1064_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1060_);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1062_, v_xs_1060_, v___f_1061_, v_sz_1063_, v___x_1064_, v_xs_1060_);
lean_dec_ref(v_xs_1060_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx(lean_object* v_00_u03b1_1066_, lean_object* v_00_u03b2_1067_, lean_object* v_n_1068_, lean_object* v_f_1069_, lean_object* v_xs_1070_){
_start:
{
lean_object* v___f_1071_; lean_object* v___x_1072_; size_t v_sz_1073_; size_t v___x_1074_; lean_object* v___x_1075_; 
v___f_1071_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1071_, 0, v_f_1069_);
v___x_1072_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1073_ = lean_array_size(v_xs_1070_);
v___x_1074_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1070_);
v___x_1075_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1072_, v_xs_1070_, v___f_1071_, v_sz_1073_, v___x_1074_, v_xs_1070_);
lean_dec_ref(v_xs_1070_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___boxed(lean_object* v_00_u03b1_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_n_1078_, lean_object* v_f_1079_, lean_object* v_xs_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Vector_mapIdx(v_00_u03b1_1076_, v_00_u03b2_1077_, v_n_1078_, v_f_1079_, v_xs_1080_);
lean_dec(v_n_1078_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg___lam__0(lean_object* v_f_1082_, lean_object* v_x1_1083_, lean_object* v_x2_1084_, lean_object* v_x3_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_apply_3(v_f_1082_, v_x1_1083_, v_x2_1084_, lean_box(0));
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg(lean_object* v_xs_1087_, lean_object* v_f_1088_){
_start:
{
lean_object* v___f_1089_; lean_object* v___x_1090_; size_t v_sz_1091_; size_t v___x_1092_; lean_object* v___x_1093_; 
v___f_1089_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1089_, 0, v_f_1088_);
v___x_1090_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1091_ = lean_array_size(v_xs_1087_);
v___x_1092_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1087_);
v___x_1093_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1090_, v_xs_1087_, v___f_1089_, v_sz_1091_, v___x_1092_, v_xs_1087_);
lean_dec_ref(v_xs_1087_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx(lean_object* v_00_u03b1_1094_, lean_object* v_n_1095_, lean_object* v_00_u03b2_1096_, lean_object* v_xs_1097_, lean_object* v_f_1098_){
_start:
{
lean_object* v___f_1099_; lean_object* v___x_1100_; size_t v_sz_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v___f_1099_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1099_, 0, v_f_1098_);
v___x_1100_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1101_ = lean_array_size(v_xs_1097_);
v___x_1102_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1097_);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1100_, v_xs_1097_, v___f_1099_, v_sz_1101_, v___x_1102_, v_xs_1097_);
lean_dec_ref(v_xs_1097_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___boxed(lean_object* v_00_u03b1_1104_, lean_object* v_n_1105_, lean_object* v_00_u03b2_1106_, lean_object* v_xs_1107_, lean_object* v_f_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Vector_mapFinIdx(v_00_u03b1_1104_, v_n_1105_, v_00_u03b2_1106_, v_xs_1107_, v_f_1108_);
lean_dec(v_n_1105_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(lean_object* v_k_1110_, lean_object* v_acc_1111_, lean_object* v_n_1112_, lean_object* v_inst_1113_, lean_object* v_f_1114_, lean_object* v_xs_1115_, lean_object* v_____do__lift_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(v_k_1110_, v_acc_1111_, v_n_1112_, v_inst_1113_, v_f_1114_, v_xs_1115_, v_____do__lift_1116_);
lean_dec(v_k_1110_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(lean_object* v_n_1118_, lean_object* v_inst_1119_, lean_object* v_f_1120_, lean_object* v_xs_1121_, lean_object* v_k_1122_, lean_object* v_acc_1123_){
_start:
{
lean_object* v_toApplicative_1124_; lean_object* v_toBind_1125_; lean_object* v_toPure_1126_; uint8_t v___x_1127_; 
v_toApplicative_1124_ = lean_ctor_get(v_inst_1119_, 0);
v_toBind_1125_ = lean_ctor_get(v_inst_1119_, 1);
lean_inc(v_toBind_1125_);
v_toPure_1126_ = lean_ctor_get(v_toApplicative_1124_, 1);
v___x_1127_ = lean_nat_dec_lt(v_k_1122_, v_n_1118_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_inc(v_toPure_1126_);
lean_dec(v_toBind_1125_);
lean_dec(v_k_1122_);
lean_dec_ref(v_xs_1121_);
lean_dec(v_f_1120_);
lean_dec_ref(v_inst_1119_);
lean_dec(v_n_1118_);
v___x_1128_ = lean_apply_2(v_toPure_1126_, lean_box(0), v_acc_1123_);
return v___x_1128_;
}
else
{
lean_object* v___f_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_inc_ref(v_xs_1121_);
lean_inc(v_f_1120_);
lean_inc(v_k_1122_);
v___f_1129_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1129_, 0, v_k_1122_);
lean_closure_set(v___f_1129_, 1, v_acc_1123_);
lean_closure_set(v___f_1129_, 2, v_n_1118_);
lean_closure_set(v___f_1129_, 3, v_inst_1119_);
lean_closure_set(v___f_1129_, 4, v_f_1120_);
lean_closure_set(v___f_1129_, 5, v_xs_1121_);
v___x_1130_ = lean_array_fget(v_xs_1121_, v_k_1122_);
lean_dec(v_k_1122_);
lean_dec_ref(v_xs_1121_);
v___x_1131_ = lean_apply_1(v_f_1120_, v___x_1130_);
v___x_1132_ = lean_apply_4(v_toBind_1125_, lean_box(0), lean_box(0), v___x_1131_, v___f_1129_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(lean_object* v_k_1133_, lean_object* v_acc_1134_, lean_object* v_n_1135_, lean_object* v_inst_1136_, lean_object* v_f_1137_, lean_object* v_xs_1138_, lean_object* v_____do__lift_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1140_ = lean_unsigned_to_nat(1u);
v___x_1141_ = lean_nat_add(v_k_1133_, v___x_1140_);
v___x_1142_ = lean_array_push(v_acc_1134_, v_____do__lift_1139_);
v___x_1143_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1135_, v_inst_1136_, v_f_1137_, v_xs_1138_, v___x_1141_, v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(lean_object* v_m_1144_, lean_object* v_00_u03b1_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_n_1147_, lean_object* v_inst_1148_, lean_object* v_f_1149_, lean_object* v_xs_1150_, lean_object* v_k_1151_, lean_object* v_h_1152_, lean_object* v_acc_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1147_, v_inst_1148_, v_f_1149_, v_xs_1150_, v_k_1151_, v_acc_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM___redArg(lean_object* v_n_1157_, lean_object* v_inst_1158_, lean_object* v_f_1159_, lean_object* v_xs_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1163_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1157_, v_inst_1158_, v_f_1159_, v_xs_1160_, v___x_1161_, v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM(lean_object* v_m_1164_, lean_object* v_00_u03b1_1165_, lean_object* v_00_u03b2_1166_, lean_object* v_n_1167_, lean_object* v_inst_1168_, lean_object* v_f_1169_, lean_object* v_xs_1170_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1173_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1167_, v_inst_1168_, v_f_1169_, v_xs_1170_, v___x_1171_, v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg___lam__0(lean_object* v_f_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_apply_1(v_f_1174_, v___y_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg(lean_object* v_inst_1178_, lean_object* v_xs_1179_, lean_object* v_f_1180_){
_start:
{
lean_object* v_toApplicative_1181_; lean_object* v_toPure_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v_toApplicative_1181_ = lean_ctor_get(v_inst_1178_, 0);
v_toPure_1182_ = lean_ctor_get(v_toApplicative_1181_, 1);
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = lean_array_get_size(v_xs_1179_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_nat_dec_lt(v___x_1183_, v___x_1184_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; 
lean_inc(v_toPure_1182_);
lean_dec(v_f_1180_);
lean_dec_ref(v_xs_1179_);
lean_dec_ref(v_inst_1178_);
v___x_1187_ = lean_apply_2(v_toPure_1182_, lean_box(0), v___x_1185_);
return v___x_1187_;
}
else
{
lean_object* v___f_1188_; uint8_t v___x_1189_; 
v___f_1188_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1188_, 0, v_f_1180_);
v___x_1189_ = lean_nat_dec_le(v___x_1184_, v___x_1184_);
if (v___x_1189_ == 0)
{
if (v___x_1186_ == 0)
{
lean_object* v___x_1190_; 
lean_inc(v_toPure_1182_);
lean_dec_ref(v___f_1188_);
lean_dec_ref(v_xs_1179_);
lean_dec_ref(v_inst_1178_);
v___x_1190_ = lean_apply_2(v_toPure_1182_, lean_box(0), v___x_1185_);
return v___x_1190_;
}
else
{
size_t v___x_1191_; size_t v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = ((size_t)0ULL);
v___x_1192_ = lean_usize_of_nat(v___x_1184_);
v___x_1193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1178_, v___f_1188_, v_xs_1179_, v___x_1191_, v___x_1192_, v___x_1185_);
return v___x_1193_;
}
}
else
{
size_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = ((size_t)0ULL);
v___x_1195_ = lean_usize_of_nat(v___x_1184_);
v___x_1196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1178_, v___f_1188_, v_xs_1179_, v___x_1194_, v___x_1195_, v___x_1185_);
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM(lean_object* v_m_1197_, lean_object* v_00_u03b1_1198_, lean_object* v_n_1199_, lean_object* v_inst_1200_, lean_object* v_xs_1201_, lean_object* v_f_1202_){
_start:
{
lean_object* v_toApplicative_1203_; lean_object* v_toPure_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_toApplicative_1203_ = lean_ctor_get(v_inst_1200_, 0);
v_toPure_1204_ = lean_ctor_get(v_toApplicative_1203_, 1);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_array_get_size(v_xs_1201_);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_nat_dec_lt(v___x_1205_, v___x_1206_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
lean_inc(v_toPure_1204_);
lean_dec(v_f_1202_);
lean_dec_ref(v_xs_1201_);
lean_dec_ref(v_inst_1200_);
v___x_1209_ = lean_apply_2(v_toPure_1204_, lean_box(0), v___x_1207_);
return v___x_1209_;
}
else
{
lean_object* v___f_1210_; uint8_t v___x_1211_; 
v___f_1210_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1210_, 0, v_f_1202_);
v___x_1211_ = lean_nat_dec_le(v___x_1206_, v___x_1206_);
if (v___x_1211_ == 0)
{
if (v___x_1208_ == 0)
{
lean_object* v___x_1212_; 
lean_inc(v_toPure_1204_);
lean_dec_ref(v___f_1210_);
lean_dec_ref(v_xs_1201_);
lean_dec_ref(v_inst_1200_);
v___x_1212_ = lean_apply_2(v_toPure_1204_, lean_box(0), v___x_1207_);
return v___x_1212_;
}
else
{
size_t v___x_1213_; size_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = ((size_t)0ULL);
v___x_1214_ = lean_usize_of_nat(v___x_1206_);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1200_, v___f_1210_, v_xs_1201_, v___x_1213_, v___x_1214_, v___x_1207_);
return v___x_1215_;
}
}
else
{
size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = ((size_t)0ULL);
v___x_1217_ = lean_usize_of_nat(v___x_1206_);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1200_, v___f_1210_, v_xs_1201_, v___x_1216_, v___x_1217_, v___x_1207_);
return v___x_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM___boxed(lean_object* v_m_1219_, lean_object* v_00_u03b1_1220_, lean_object* v_n_1221_, lean_object* v_inst_1222_, lean_object* v_xs_1223_, lean_object* v_f_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Vector_forM(v_m_1219_, v_00_u03b1_1220_, v_n_1221_, v_inst_1222_, v_xs_1223_, v_f_1224_);
lean_dec(v_n_1221_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(lean_object* v_i_1226_, lean_object* v_acc_1227_, lean_object* v_n_1228_, lean_object* v_inst_1229_, lean_object* v_xs_1230_, lean_object* v_f_1231_, lean_object* v_____do__lift_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(v_i_1226_, v_acc_1227_, v_n_1228_, v_inst_1229_, v_xs_1230_, v_f_1231_, v_____do__lift_1232_);
lean_dec_ref(v_____do__lift_1232_);
lean_dec(v_i_1226_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(lean_object* v_n_1234_, lean_object* v_inst_1235_, lean_object* v_xs_1236_, lean_object* v_f_1237_, lean_object* v_i_1238_, lean_object* v_acc_1239_){
_start:
{
lean_object* v_toApplicative_1240_; lean_object* v_toBind_1241_; lean_object* v_toPure_1242_; uint8_t v___x_1243_; 
v_toApplicative_1240_ = lean_ctor_get(v_inst_1235_, 0);
v_toBind_1241_ = lean_ctor_get(v_inst_1235_, 1);
lean_inc(v_toBind_1241_);
v_toPure_1242_ = lean_ctor_get(v_toApplicative_1240_, 1);
v___x_1243_ = lean_nat_dec_lt(v_i_1238_, v_n_1234_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_inc(v_toPure_1242_);
lean_dec(v_toBind_1241_);
lean_dec(v_i_1238_);
lean_dec(v_f_1237_);
lean_dec_ref(v_xs_1236_);
lean_dec_ref(v_inst_1235_);
lean_dec(v_n_1234_);
v___x_1244_ = lean_apply_2(v_toPure_1242_, lean_box(0), v_acc_1239_);
return v___x_1244_;
}
else
{
lean_object* v___f_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_inc(v_f_1237_);
lean_inc_ref(v_xs_1236_);
lean_inc(v_i_1238_);
v___f_1245_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1245_, 0, v_i_1238_);
lean_closure_set(v___f_1245_, 1, v_acc_1239_);
lean_closure_set(v___f_1245_, 2, v_n_1234_);
lean_closure_set(v___f_1245_, 3, v_inst_1235_);
lean_closure_set(v___f_1245_, 4, v_xs_1236_);
lean_closure_set(v___f_1245_, 5, v_f_1237_);
v___x_1246_ = lean_array_fget(v_xs_1236_, v_i_1238_);
lean_dec(v_i_1238_);
lean_dec_ref(v_xs_1236_);
v___x_1247_ = lean_apply_1(v_f_1237_, v___x_1246_);
v___x_1248_ = lean_apply_4(v_toBind_1241_, lean_box(0), lean_box(0), v___x_1247_, v___f_1245_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(lean_object* v_i_1249_, lean_object* v_acc_1250_, lean_object* v_n_1251_, lean_object* v_inst_1252_, lean_object* v_xs_1253_, lean_object* v_f_1254_, lean_object* v_____do__lift_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_add(v_i_1249_, v___x_1256_);
v___x_1258_ = l_Array_append___redArg(v_acc_1250_, v_____do__lift_1255_);
v___x_1259_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1251_, v_inst_1252_, v_xs_1253_, v_f_1254_, v___x_1257_, v___x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(lean_object* v_m_1260_, lean_object* v_00_u03b1_1261_, lean_object* v_n_1262_, lean_object* v_00_u03b2_1263_, lean_object* v_k_1264_, lean_object* v_inst_1265_, lean_object* v_xs_1266_, lean_object* v_f_1267_, lean_object* v_i_1268_, lean_object* v_h_1269_, lean_object* v_acc_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1262_, v_inst_1265_, v_xs_1266_, v_f_1267_, v_i_1268_, v_acc_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(lean_object* v_m_1272_, lean_object* v_00_u03b1_1273_, lean_object* v_n_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_k_1276_, lean_object* v_inst_1277_, lean_object* v_xs_1278_, lean_object* v_f_1279_, lean_object* v_i_1280_, lean_object* v_h_1281_, lean_object* v_acc_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(v_m_1272_, v_00_u03b1_1273_, v_n_1274_, v_00_u03b2_1275_, v_k_1276_, v_inst_1277_, v_xs_1278_, v_f_1279_, v_i_1280_, v_h_1281_, v_acc_1282_);
lean_dec(v_k_1276_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___redArg(lean_object* v_n_1284_, lean_object* v_inst_1285_, lean_object* v_xs_1286_, lean_object* v_f_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1290_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1284_, v_inst_1285_, v_xs_1286_, v_f_1287_, v___x_1288_, v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM(lean_object* v_m_1291_, lean_object* v_00_u03b1_1292_, lean_object* v_n_1293_, lean_object* v_00_u03b2_1294_, lean_object* v_k_1295_, lean_object* v_inst_1296_, lean_object* v_xs_1297_, lean_object* v_f_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1301_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1293_, v_inst_1296_, v_xs_1297_, v_f_1298_, v___x_1299_, v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___boxed(lean_object* v_m_1302_, lean_object* v_00_u03b1_1303_, lean_object* v_n_1304_, lean_object* v_00_u03b2_1305_, lean_object* v_k_1306_, lean_object* v_inst_1307_, lean_object* v_xs_1308_, lean_object* v_f_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Vector_flatMapM(v_m_1302_, v_00_u03b1_1303_, v_n_1304_, v_00_u03b2_1305_, v_k_1306_, v_inst_1307_, v_xs_1308_, v_f_1309_);
lean_dec(v_k_1306_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1311_, lean_object* v_ys_1312_, lean_object* v_inst_1313_, lean_object* v_xs_1314_, lean_object* v_f_1315_, lean_object* v_n_1316_, lean_object* v_____do__lift_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Vector_mapFinIdxM_map___redArg___lam__0(v_j_1311_, v_ys_1312_, v_inst_1313_, v_xs_1314_, v_f_1315_, v_n_1316_, v_____do__lift_1317_);
lean_dec(v_n_1316_);
lean_dec(v_j_1311_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg(lean_object* v_inst_1319_, lean_object* v_xs_1320_, lean_object* v_f_1321_, lean_object* v_i_1322_, lean_object* v_j_1323_, lean_object* v_ys_1324_){
_start:
{
lean_object* v_toApplicative_1325_; lean_object* v_toBind_1326_; lean_object* v_toPure_1327_; lean_object* v_zero_1328_; uint8_t v_isZero_1329_; 
v_toApplicative_1325_ = lean_ctor_get(v_inst_1319_, 0);
v_toBind_1326_ = lean_ctor_get(v_inst_1319_, 1);
lean_inc(v_toBind_1326_);
v_toPure_1327_ = lean_ctor_get(v_toApplicative_1325_, 1);
v_zero_1328_ = lean_unsigned_to_nat(0u);
v_isZero_1329_ = lean_nat_dec_eq(v_i_1322_, v_zero_1328_);
if (v_isZero_1329_ == 1)
{
lean_object* v___x_1330_; 
lean_inc(v_toPure_1327_);
lean_dec(v_toBind_1326_);
lean_dec(v_j_1323_);
lean_dec(v_f_1321_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v_inst_1319_);
v___x_1330_ = lean_apply_2(v_toPure_1327_, lean_box(0), v_ys_1324_);
return v___x_1330_;
}
else
{
lean_object* v_one_1331_; lean_object* v_n_1332_; lean_object* v___f_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_one_1331_ = lean_unsigned_to_nat(1u);
v_n_1332_ = lean_nat_sub(v_i_1322_, v_one_1331_);
lean_inc(v_f_1321_);
lean_inc_ref(v_xs_1320_);
lean_inc(v_j_1323_);
v___f_1333_ = lean_alloc_closure((void*)(l_Vector_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1333_, 0, v_j_1323_);
lean_closure_set(v___f_1333_, 1, v_ys_1324_);
lean_closure_set(v___f_1333_, 2, v_inst_1319_);
lean_closure_set(v___f_1333_, 3, v_xs_1320_);
lean_closure_set(v___f_1333_, 4, v_f_1321_);
lean_closure_set(v___f_1333_, 5, v_n_1332_);
v___x_1334_ = lean_array_fget(v_xs_1320_, v_j_1323_);
lean_dec_ref(v_xs_1320_);
v___x_1335_ = lean_apply_3(v_f_1321_, v_j_1323_, v___x_1334_, lean_box(0));
v___x_1336_ = lean_apply_4(v_toBind_1326_, lean_box(0), lean_box(0), v___x_1335_, v___f_1333_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1337_, lean_object* v_ys_1338_, lean_object* v_inst_1339_, lean_object* v_xs_1340_, lean_object* v_f_1341_, lean_object* v_n_1342_, lean_object* v_____do__lift_1343_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = lean_nat_add(v_j_1337_, v___x_1344_);
v___x_1346_ = lean_array_push(v_ys_1338_, v_____do__lift_1343_);
v___x_1347_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1339_, v_xs_1340_, v_f_1341_, v_n_1342_, v___x_1345_, v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1348_, lean_object* v_xs_1349_, lean_object* v_f_1350_, lean_object* v_i_1351_, lean_object* v_j_1352_, lean_object* v_ys_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1348_, v_xs_1349_, v_f_1350_, v_i_1351_, v_j_1352_, v_ys_1353_);
lean_dec(v_i_1351_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map(lean_object* v_n_1355_, lean_object* v_00_u03b1_1356_, lean_object* v_00_u03b2_1357_, lean_object* v_m_1358_, lean_object* v_inst_1359_, lean_object* v_xs_1360_, lean_object* v_f_1361_, lean_object* v_i_1362_, lean_object* v_j_1363_, lean_object* v_inv_1364_, lean_object* v_ys_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1359_, v_xs_1360_, v_f_1361_, v_i_1362_, v_j_1363_, v_ys_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___boxed(lean_object* v_n_1367_, lean_object* v_00_u03b1_1368_, lean_object* v_00_u03b2_1369_, lean_object* v_m_1370_, lean_object* v_inst_1371_, lean_object* v_xs_1372_, lean_object* v_f_1373_, lean_object* v_i_1374_, lean_object* v_j_1375_, lean_object* v_inv_1376_, lean_object* v_ys_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Vector_mapFinIdxM_map(v_n_1367_, v_00_u03b1_1368_, v_00_u03b2_1369_, v_m_1370_, v_inst_1371_, v_xs_1372_, v_f_1373_, v_i_1374_, v_j_1375_, v_inv_1376_, v_ys_1377_);
lean_dec(v_i_1374_);
lean_dec(v_n_1367_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg(lean_object* v_n_1379_, lean_object* v_inst_1380_, lean_object* v_xs_1381_, lean_object* v_f_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1385_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1380_, v_xs_1381_, v_f_1382_, v_n_1379_, v___x_1383_, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg___boxed(lean_object* v_n_1386_, lean_object* v_inst_1387_, lean_object* v_xs_1388_, lean_object* v_f_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Vector_mapFinIdxM___redArg(v_n_1386_, v_inst_1387_, v_xs_1388_, v_f_1389_);
lean_dec(v_n_1386_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM(lean_object* v_n_1391_, lean_object* v_00_u03b1_1392_, lean_object* v_00_u03b2_1393_, lean_object* v_m_1394_, lean_object* v_inst_1395_, lean_object* v_xs_1396_, lean_object* v_f_1397_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1400_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1395_, v_xs_1396_, v_f_1397_, v_n_1391_, v___x_1398_, v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___boxed(lean_object* v_n_1401_, lean_object* v_00_u03b1_1402_, lean_object* v_00_u03b2_1403_, lean_object* v_m_1404_, lean_object* v_inst_1405_, lean_object* v_xs_1406_, lean_object* v_f_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Vector_mapFinIdxM(v_n_1401_, v_00_u03b1_1402_, v_00_u03b2_1403_, v_m_1404_, v_inst_1405_, v_xs_1406_, v_f_1407_);
lean_dec(v_n_1401_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg(lean_object* v_n_1409_, lean_object* v_inst_1410_, lean_object* v_f_1411_, lean_object* v_xs_1412_){
_start:
{
lean_object* v___f_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___f_1413_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1413_, 0, v_f_1411_);
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1416_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1410_, v_xs_1412_, v___f_1413_, v_n_1409_, v___x_1414_, v___x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg___boxed(lean_object* v_n_1417_, lean_object* v_inst_1418_, lean_object* v_f_1419_, lean_object* v_xs_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Vector_mapIdxM___redArg(v_n_1417_, v_inst_1418_, v_f_1419_, v_xs_1420_);
lean_dec(v_n_1417_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM(lean_object* v_n_1422_, lean_object* v_00_u03b1_1423_, lean_object* v_00_u03b2_1424_, lean_object* v_m_1425_, lean_object* v_inst_1426_, lean_object* v_f_1427_, lean_object* v_xs_1428_){
_start:
{
lean_object* v___f_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___f_1429_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1429_, 0, v_f_1427_);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1432_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1426_, v_xs_1428_, v___f_1429_, v_n_1422_, v___x_1430_, v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___boxed(lean_object* v_n_1433_, lean_object* v_00_u03b1_1434_, lean_object* v_00_u03b2_1435_, lean_object* v_m_1436_, lean_object* v_inst_1437_, lean_object* v_f_1438_, lean_object* v_xs_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Vector_mapIdxM(v_n_1433_, v_00_u03b1_1434_, v_00_u03b2_1435_, v_m_1436_, v_inst_1437_, v_f_1438_, v_xs_1439_);
lean_dec(v_n_1433_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___redArg(lean_object* v_inst_1441_, lean_object* v_f_1442_, lean_object* v_xs_1443_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1441_, v_f_1442_, v_xs_1443_, v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM(lean_object* v_00_u03b2_1446_, lean_object* v_n_1447_, lean_object* v_00_u03b1_1448_, lean_object* v_m_1449_, lean_object* v_inst_1450_, lean_object* v_f_1451_, lean_object* v_xs_1452_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1450_, v_f_1451_, v_xs_1452_, v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___boxed(lean_object* v_00_u03b2_1455_, lean_object* v_n_1456_, lean_object* v_00_u03b1_1457_, lean_object* v_m_1458_, lean_object* v_inst_1459_, lean_object* v_f_1460_, lean_object* v_xs_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Vector_firstM(v_00_u03b2_1455_, v_n_1456_, v_00_u03b1_1457_, v_m_1458_, v_inst_1459_, v_f_1460_, v_xs_1461_);
lean_dec(v_n_1456_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0(lean_object* v_x_1463_){
_start:
{
lean_inc_ref(v_x_1463_);
return v_x_1463_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0___boxed(lean_object* v_x_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Vector_flatten___redArg___lam__0(v_x_1464_);
lean_dec_ref(v_x_1464_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg(lean_object* v_xs_1470_){
_start:
{
lean_object* v___f_1471_; lean_object* v___x_1472_; size_t v_sz_1473_; size_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___f_1471_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1472_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1473_ = lean_array_size(v_xs_1470_);
v___x_1474_ = ((size_t)0ULL);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1472_, v___f_1471_, v_sz_1473_, v___x_1474_, v_xs_1470_);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1478_ = lean_array_get_size(v___x_1475_);
v___x_1479_ = lean_nat_dec_lt(v___x_1476_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_dec(v___x_1475_);
return v___x_1477_;
}
else
{
lean_object* v___f_1480_; size_t v___x_1481_; lean_object* v___x_1482_; 
v___f_1480_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1481_ = lean_usize_of_nat(v___x_1478_);
v___x_1482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1472_, v___f_1480_, v___x_1475_, v___x_1474_, v___x_1481_, v___x_1477_);
return v___x_1482_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten(lean_object* v_00_u03b1_1483_, lean_object* v_n_1484_, lean_object* v_m_1485_, lean_object* v_xs_1486_){
_start:
{
lean_object* v___f_1487_; lean_object* v___x_1488_; size_t v_sz_1489_; size_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___f_1487_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1488_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1489_ = lean_array_size(v_xs_1486_);
v___x_1490_ = ((size_t)0ULL);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1488_, v___f_1487_, v_sz_1489_, v___x_1490_, v_xs_1486_);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1494_ = lean_array_get_size(v___x_1491_);
v___x_1495_ = lean_nat_dec_lt(v___x_1492_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_dec(v___x_1491_);
return v___x_1493_;
}
else
{
lean_object* v___f_1496_; size_t v___x_1497_; lean_object* v___x_1498_; 
v___f_1496_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1497_ = lean_usize_of_nat(v___x_1494_);
v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1488_, v___f_1496_, v___x_1491_, v___x_1490_, v___x_1497_, v___x_1493_);
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___boxed(lean_object* v_00_u03b1_1499_, lean_object* v_n_1500_, lean_object* v_m_1501_, lean_object* v_xs_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Vector_flatten(v_00_u03b1_1499_, v_n_1500_, v_m_1501_, v_xs_1502_);
lean_dec(v_m_1501_);
lean_dec(v_n_1500_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg___lam__0(lean_object* v_f_1504_, lean_object* v_x1_1505_, lean_object* v_x2_1506_){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_apply_1(v_f_1504_, v_x2_1506_);
v___x_1508_ = l_Array_append___redArg(v_x1_1505_, v___x_1507_);
lean_dec_ref(v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg(lean_object* v_xs_1509_, lean_object* v_f_1510_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1511_ = lean_unsigned_to_nat(0u);
v___x_1512_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1513_ = lean_array_get_size(v_xs_1509_);
v___x_1514_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1515_ = lean_nat_dec_lt(v___x_1511_, v___x_1513_);
if (v___x_1515_ == 0)
{
lean_dec_ref(v_f_1510_);
lean_dec_ref(v_xs_1509_);
return v___x_1512_;
}
else
{
lean_object* v___f_1516_; size_t v___x_1517_; size_t v___x_1518_; lean_object* v___x_1519_; 
v___f_1516_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1516_, 0, v_f_1510_);
v___x_1517_ = ((size_t)0ULL);
v___x_1518_ = lean_usize_of_nat(v___x_1513_);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1514_, v___f_1516_, v_xs_1509_, v___x_1517_, v___x_1518_, v___x_1512_);
return v___x_1519_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap(lean_object* v_00_u03b1_1520_, lean_object* v_n_1521_, lean_object* v_00_u03b2_1522_, lean_object* v_m_1523_, lean_object* v_xs_1524_, lean_object* v_f_1525_){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1528_ = lean_array_get_size(v_xs_1524_);
v___x_1529_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1530_ = lean_nat_dec_lt(v___x_1526_, v___x_1528_);
if (v___x_1530_ == 0)
{
lean_dec_ref(v_f_1525_);
lean_dec_ref(v_xs_1524_);
return v___x_1527_;
}
else
{
lean_object* v___f_1531_; size_t v___x_1532_; size_t v___x_1533_; lean_object* v___x_1534_; 
v___f_1531_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1531_, 0, v_f_1525_);
v___x_1532_ = ((size_t)0ULL);
v___x_1533_ = lean_usize_of_nat(v___x_1528_);
v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1529_, v___f_1531_, v_xs_1524_, v___x_1532_, v___x_1533_, v___x_1527_);
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___boxed(lean_object* v_00_u03b1_1535_, lean_object* v_n_1536_, lean_object* v_00_u03b2_1537_, lean_object* v_m_1538_, lean_object* v_xs_1539_, lean_object* v_f_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Vector_flatMap(v_00_u03b1_1535_, v_n_1536_, v_00_u03b2_1537_, v_m_1538_, v_xs_1539_, v_f_1540_);
lean_dec(v_m_1538_);
lean_dec(v_n_1536_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg(lean_object* v_xs_1542_, lean_object* v_k_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Array_zipIdx___redArg(v_xs_1542_, v_k_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg___boxed(lean_object* v_xs_1545_, lean_object* v_k_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Vector_zipIdx___redArg(v_xs_1545_, v_k_1546_);
lean_dec(v_k_1546_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx(lean_object* v_00_u03b1_1548_, lean_object* v_n_1549_, lean_object* v_xs_1550_, lean_object* v_k_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Array_zipIdx___redArg(v_xs_1550_, v_k_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___boxed(lean_object* v_00_u03b1_1553_, lean_object* v_n_1554_, lean_object* v_xs_1555_, lean_object* v_k_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Vector_zipIdx(v_00_u03b1_1553_, v_n_1554_, v_xs_1555_, v_k_1556_);
lean_dec(v_k_1556_);
lean_dec(v_n_1554_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg(lean_object* v_as_1558_, lean_object* v_bs_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Array_zip___redArg(v_as_1558_, v_bs_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg___boxed(lean_object* v_as_1561_, lean_object* v_bs_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Vector_zip___redArg(v_as_1561_, v_bs_1562_);
lean_dec_ref(v_bs_1562_);
lean_dec_ref(v_as_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip(lean_object* v_00_u03b1_1564_, lean_object* v_n_1565_, lean_object* v_00_u03b2_1566_, lean_object* v_as_1567_, lean_object* v_bs_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Array_zip___redArg(v_as_1567_, v_bs_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___boxed(lean_object* v_00_u03b1_1570_, lean_object* v_n_1571_, lean_object* v_00_u03b2_1572_, lean_object* v_as_1573_, lean_object* v_bs_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Vector_zip(v_00_u03b1_1570_, v_n_1571_, v_00_u03b2_1572_, v_as_1573_, v_bs_1574_);
lean_dec_ref(v_bs_1574_);
lean_dec_ref(v_as_1573_);
lean_dec(v_n_1571_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___redArg(lean_object* v_f_1576_, lean_object* v_as_1577_, lean_object* v_bs_1578_){
_start:
{
lean_object* v___f_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___f_1579_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1579_, 0, v_f_1576_);
v___x_1580_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1581_ = lean_unsigned_to_nat(0u);
v___x_1582_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1583_ = l_Array_zipWithMAux___redArg(v___x_1580_, v_as_1577_, v_bs_1578_, v___f_1579_, v___x_1581_, v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith(lean_object* v_00_u03b1_1584_, lean_object* v_00_u03b2_1585_, lean_object* v_00_u03c6_1586_, lean_object* v_n_1587_, lean_object* v_f_1588_, lean_object* v_as_1589_, lean_object* v_bs_1590_){
_start:
{
lean_object* v___f_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___f_1591_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1591_, 0, v_f_1588_);
v___x_1592_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1595_ = l_Array_zipWithMAux___redArg(v___x_1592_, v_as_1589_, v_bs_1590_, v___f_1591_, v___x_1593_, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___boxed(lean_object* v_00_u03b1_1596_, lean_object* v_00_u03b2_1597_, lean_object* v_00_u03c6_1598_, lean_object* v_n_1599_, lean_object* v_f_1600_, lean_object* v_as_1601_, lean_object* v_bs_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Vector_zipWith(v_00_u03b1_1596_, v_00_u03b2_1597_, v_00_u03c6_1598_, v_n_1599_, v_f_1600_, v_as_1601_, v_bs_1602_);
lean_dec(v_n_1599_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg(lean_object* v_xs_1604_){
_start:
{
lean_object* v___x_1605_; lean_object* v_fst_1606_; lean_object* v_snd_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v___x_1605_ = l_Array_unzip___redArg(v_xs_1604_);
v_fst_1606_ = lean_ctor_get(v___x_1605_, 0);
v_snd_1607_ = lean_ctor_get(v___x_1605_, 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1605_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_snd_1607_);
lean_inc(v_fst_1606_);
lean_dec(v___x_1605_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_fst_1606_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_snd_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg___boxed(lean_object* v_xs_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Vector_unzip___redArg(v_xs_1615_);
lean_dec_ref(v_xs_1615_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip(lean_object* v_00_u03b1_1617_, lean_object* v_00_u03b2_1618_, lean_object* v_n_1619_, lean_object* v_xs_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
v___x_1621_ = l_Array_unzip___redArg(v_xs_1620_);
v_fst_1622_ = lean_ctor_get(v___x_1621_, 0);
v_snd_1623_ = lean_ctor_get(v___x_1621_, 1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1621_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_snd_1623_);
lean_inc(v_fst_1622_);
lean_dec(v___x_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_fst_1622_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_snd_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___boxed(lean_object* v_00_u03b1_1631_, lean_object* v_00_u03b2_1632_, lean_object* v_n_1633_, lean_object* v_xs_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Vector_unzip(v_00_u03b1_1631_, v_00_u03b2_1632_, v_n_1633_, v_xs_1634_);
lean_dec_ref(v_xs_1634_);
lean_dec(v_n_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn___redArg(lean_object* v_n_1636_, lean_object* v_f_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Array_ofFn___redArg(v_n_1636_, v_f_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn(lean_object* v_n_1639_, lean_object* v_00_u03b1_1640_, lean_object* v_f_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Array_ofFn___redArg(v_n_1639_, v_f_1641_);
return v___x_1642_;
}
}
static lean_object* _init_l_Vector_swap___auto__1(void){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1643_;
}
}
static lean_object* _init_l_Vector_swap___auto__3(void){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg(lean_object* v_xs_1645_, lean_object* v_i_1646_, lean_object* v_j_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_array_fswap(v_xs_1645_, v_i_1646_, v_j_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg___boxed(lean_object* v_xs_1649_, lean_object* v_i_1650_, lean_object* v_j_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Vector_swap___redArg(v_xs_1649_, v_i_1650_, v_j_1651_);
lean_dec(v_j_1651_);
lean_dec(v_i_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap(lean_object* v_00_u03b1_1653_, lean_object* v_n_1654_, lean_object* v_xs_1655_, lean_object* v_i_1656_, lean_object* v_j_1657_, lean_object* v_hi_1658_, lean_object* v_hj_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_array_fswap(v_xs_1655_, v_i_1656_, v_j_1657_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___boxed(lean_object* v_00_u03b1_1661_, lean_object* v_n_1662_, lean_object* v_xs_1663_, lean_object* v_i_1664_, lean_object* v_j_1665_, lean_object* v_hi_1666_, lean_object* v_hj_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Vector_swap(v_00_u03b1_1661_, v_n_1662_, v_xs_1663_, v_i_1664_, v_j_1665_, v_hi_1666_, v_hj_1667_);
lean_dec(v_j_1665_);
lean_dec(v_i_1664_);
lean_dec(v_n_1662_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg(lean_object* v_xs_1669_, lean_object* v_i_1670_, lean_object* v_j_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_array_swap(v_xs_1669_, v_i_1670_, v_j_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg___boxed(lean_object* v_xs_1673_, lean_object* v_i_1674_, lean_object* v_j_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Vector_swapIfInBounds___redArg(v_xs_1673_, v_i_1674_, v_j_1675_);
lean_dec(v_j_1675_);
lean_dec(v_i_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds(lean_object* v_00_u03b1_1677_, lean_object* v_n_1678_, lean_object* v_xs_1679_, lean_object* v_i_1680_, lean_object* v_j_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_array_swap(v_xs_1679_, v_i_1680_, v_j_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___boxed(lean_object* v_00_u03b1_1683_, lean_object* v_n_1684_, lean_object* v_xs_1685_, lean_object* v_i_1686_, lean_object* v_j_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Vector_swapIfInBounds(v_00_u03b1_1683_, v_n_1684_, v_xs_1685_, v_i_1686_, v_j_1687_);
lean_dec(v_j_1687_);
lean_dec(v_i_1686_);
lean_dec(v_n_1684_);
return v_res_1688_;
}
}
static lean_object* _init_l_Vector_swapAt___auto__1(void){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg(lean_object* v_xs_1690_, lean_object* v_i_1691_, lean_object* v_x_1692_){
_start:
{
lean_object* v_e_1693_; lean_object* v_xs_x27_1694_; lean_object* v___x_1695_; 
v_e_1693_ = lean_array_fget(v_xs_1690_, v_i_1691_);
v_xs_x27_1694_ = lean_array_fset(v_xs_1690_, v_i_1691_, v_x_1692_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_e_1693_);
lean_ctor_set(v___x_1695_, 1, v_xs_x27_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg___boxed(lean_object* v_xs_1696_, lean_object* v_i_1697_, lean_object* v_x_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Vector_swapAt___redArg(v_xs_1696_, v_i_1697_, v_x_1698_);
lean_dec(v_i_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt(lean_object* v_00_u03b1_1700_, lean_object* v_n_1701_, lean_object* v_xs_1702_, lean_object* v_i_1703_, lean_object* v_x_1704_, lean_object* v_hi_1705_){
_start:
{
lean_object* v_e_1706_; lean_object* v_xs_x27_1707_; lean_object* v___x_1708_; 
v_e_1706_ = lean_array_fget(v_xs_1702_, v_i_1703_);
v_xs_x27_1707_ = lean_array_fset(v_xs_1702_, v_i_1703_, v_x_1704_);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v_e_1706_);
lean_ctor_set(v___x_1708_, 1, v_xs_x27_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___boxed(lean_object* v_00_u03b1_1709_, lean_object* v_n_1710_, lean_object* v_xs_1711_, lean_object* v_i_1712_, lean_object* v_x_1713_, lean_object* v_hi_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Vector_swapAt(v_00_u03b1_1709_, v_n_1710_, v_xs_1711_, v_i_1712_, v_x_1713_, v_hi_1714_);
lean_dec(v_i_1712_);
lean_dec(v_n_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___redArg(lean_object* v_xs_1720_, lean_object* v_i_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = lean_array_get_size(v_xs_1720_);
v___x_1724_ = lean_nat_dec_lt(v_i_1721_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_object* v_this_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v_fst_1737_; lean_object* v_snd_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
v_this_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1725_, 0, v_x_1722_);
lean_ctor_set(v_this_1725_, 1, v_xs_1720_);
v___x_1726_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1727_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1728_ = lean_unsigned_to_nat(438u);
v___x_1729_ = lean_unsigned_to_nat(4u);
v___x_1730_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1731_ = l_Nat_reprFast(v_i_1721_);
v___x_1732_ = lean_string_append(v___x_1730_, v___x_1731_);
lean_dec_ref(v___x_1731_);
v___x_1733_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1734_ = lean_string_append(v___x_1732_, v___x_1733_);
v___x_1735_ = l_mkPanicMessageWithDecl(v___x_1726_, v___x_1727_, v___x_1728_, v___x_1729_, v___x_1734_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = l_panic___redArg(v_this_1725_, v___x_1735_);
lean_dec_ref_known(v_this_1725_, 2);
v_fst_1737_ = lean_ctor_get(v___x_1736_, 0);
v_snd_1738_ = lean_ctor_get(v___x_1736_, 1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1736_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_snd_1738_);
lean_inc(v_fst_1737_);
lean_dec(v___x_1736_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_fst_1737_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_snd_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
else
{
lean_object* v_e_1746_; lean_object* v_xs_x27_1747_; lean_object* v___x_1748_; 
v_e_1746_ = lean_array_fget(v_xs_1720_, v_i_1721_);
v_xs_x27_1747_ = lean_array_fset(v_xs_1720_, v_i_1721_, v_x_1722_);
lean_dec(v_i_1721_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_e_1746_);
lean_ctor_set(v___x_1748_, 1, v_xs_x27_1747_);
return v___x_1748_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21(lean_object* v_00_u03b1_1749_, lean_object* v_n_1750_, lean_object* v_xs_1751_, lean_object* v_i_1752_, lean_object* v_x_1753_){
_start:
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = lean_array_get_size(v_xs_1751_);
v___x_1755_ = lean_nat_dec_lt(v_i_1752_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v_this_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v_fst_1768_; lean_object* v_snd_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
v_this_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1756_, 0, v_x_1753_);
lean_ctor_set(v_this_1756_, 1, v_xs_1751_);
v___x_1757_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1758_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1759_ = lean_unsigned_to_nat(438u);
v___x_1760_ = lean_unsigned_to_nat(4u);
v___x_1761_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1762_ = l_Nat_reprFast(v_i_1752_);
v___x_1763_ = lean_string_append(v___x_1761_, v___x_1762_);
lean_dec_ref(v___x_1762_);
v___x_1764_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1765_ = lean_string_append(v___x_1763_, v___x_1764_);
v___x_1766_ = l_mkPanicMessageWithDecl(v___x_1757_, v___x_1758_, v___x_1759_, v___x_1760_, v___x_1765_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = l_panic___redArg(v_this_1756_, v___x_1766_);
lean_dec_ref_known(v_this_1756_, 2);
v_fst_1768_ = lean_ctor_get(v___x_1767_, 0);
v_snd_1769_ = lean_ctor_get(v___x_1767_, 1);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1767_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_snd_1769_);
lean_inc(v_fst_1768_);
lean_dec(v___x_1767_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_fst_1768_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_snd_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
else
{
lean_object* v_e_1777_; lean_object* v_xs_x27_1778_; lean_object* v___x_1779_; 
v_e_1777_ = lean_array_fget(v_xs_1751_, v_i_1752_);
v_xs_x27_1778_ = lean_array_fset(v_xs_1751_, v_i_1752_, v_x_1753_);
lean_dec(v_i_1752_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_e_1777_);
lean_ctor_set(v___x_1779_, 1, v_xs_x27_1778_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___boxed(lean_object* v_00_u03b1_1780_, lean_object* v_n_1781_, lean_object* v_xs_1782_, lean_object* v_i_1783_, lean_object* v_x_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Vector_swapAt_x21(v_00_u03b1_1780_, v_n_1781_, v_xs_1782_, v_i_1783_, v_x_1784_);
lean_dec(v_n_1781_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Vector_range(lean_object* v_n_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Array_range(v_n_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Vector_range_x27(lean_object* v_start_1788_, lean_object* v_size_1789_, lean_object* v_step_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Array_range_x27(v_start_1788_, v_size_1789_, v_step_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv___redArg(lean_object* v_n_1792_, lean_object* v_xs_1793_, lean_object* v_ys_1794_, lean_object* v_r_1795_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = l_Array_isEqvAux___redArg(v_xs_1793_, v_ys_1794_, v_r_1795_, v_n_1792_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___redArg___boxed(lean_object* v_n_1797_, lean_object* v_xs_1798_, lean_object* v_ys_1799_, lean_object* v_r_1800_){
_start:
{
uint8_t v_res_1801_; lean_object* v_r_1802_; 
v_res_1801_ = l_Vector_isEqv___redArg(v_n_1797_, v_xs_1798_, v_ys_1799_, v_r_1800_);
lean_dec_ref(v_ys_1799_);
lean_dec_ref(v_xs_1798_);
v_r_1802_ = lean_box(v_res_1801_);
return v_r_1802_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv(lean_object* v_00_u03b1_1803_, lean_object* v_n_1804_, lean_object* v_xs_1805_, lean_object* v_ys_1806_, lean_object* v_r_1807_){
_start:
{
uint8_t v___x_1808_; 
v___x_1808_ = l_Array_isEqvAux___redArg(v_xs_1805_, v_ys_1806_, v_r_1807_, v_n_1804_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___boxed(lean_object* v_00_u03b1_1809_, lean_object* v_n_1810_, lean_object* v_xs_1811_, lean_object* v_ys_1812_, lean_object* v_r_1813_){
_start:
{
uint8_t v_res_1814_; lean_object* v_r_1815_; 
v_res_1814_ = l_Vector_isEqv(v_00_u03b1_1809_, v_n_1810_, v_xs_1811_, v_ys_1812_, v_r_1813_);
lean_dec_ref(v_ys_1812_);
lean_dec_ref(v_xs_1811_);
v_r_1815_ = lean_box(v_res_1814_);
return v_r_1815_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__0(lean_object* v_inst_1816_, lean_object* v_x1_1817_, lean_object* v_x2_1818_){
_start:
{
lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1819_ = lean_apply_2(v_inst_1816_, v_x1_1817_, v_x2_1818_);
v___x_1820_ = lean_unbox(v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__0___boxed(lean_object* v_inst_1821_, lean_object* v_x1_1822_, lean_object* v_x2_1823_){
_start:
{
uint8_t v_res_1824_; lean_object* v_r_1825_; 
v_res_1824_ = l_Vector_instBEq___redArg___lam__0(v_inst_1821_, v_x1_1822_, v_x2_1823_);
v_r_1825_ = lean_box(v_res_1824_);
return v_r_1825_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__1(lean_object* v___f_1826_, lean_object* v_n_1827_, lean_object* v_xs_1828_, lean_object* v_ys_1829_){
_start:
{
uint8_t v___x_1830_; 
v___x_1830_ = l_Array_isEqvAux___redArg(v_xs_1828_, v_ys_1829_, v___f_1826_, v_n_1827_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__1___boxed(lean_object* v___f_1831_, lean_object* v_n_1832_, lean_object* v_xs_1833_, lean_object* v_ys_1834_){
_start:
{
uint8_t v_res_1835_; lean_object* v_r_1836_; 
v_res_1835_ = l_Vector_instBEq___redArg___lam__1(v___f_1831_, v_n_1832_, v_xs_1833_, v_ys_1834_);
lean_dec_ref(v_ys_1834_);
lean_dec_ref(v_xs_1833_);
v_r_1836_ = lean_box(v_res_1835_);
return v_r_1836_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg(lean_object* v_n_1837_, lean_object* v_inst_1838_){
_start:
{
lean_object* v___f_1839_; lean_object* v___f_1840_; 
v___f_1839_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1839_, 0, v_inst_1838_);
v___f_1840_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1840_, 0, v___f_1839_);
lean_closure_set(v___f_1840_, 1, v_n_1837_);
return v___f_1840_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq(lean_object* v_00_u03b1_1841_, lean_object* v_n_1842_, lean_object* v_inst_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Vector_instBEq___redArg(v_n_1842_, v_inst_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___redArg(lean_object* v_xs_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Array_reverse___redArg(v_xs_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse(lean_object* v_00_u03b1_1847_, lean_object* v_n_1848_, lean_object* v_xs_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Array_reverse___redArg(v_xs_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___boxed(lean_object* v_00_u03b1_1851_, lean_object* v_n_1852_, lean_object* v_xs_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Vector_reverse(v_00_u03b1_1851_, v_n_1852_, v_xs_1853_);
lean_dec(v_n_1852_);
return v_res_1854_;
}
}
static lean_object* _init_l_Vector_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___redArg(lean_object* v_xs_1856_, lean_object* v_i_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Array_eraseIdx___redArg(v_xs_1856_, v_i_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx(lean_object* v_00_u03b1_1859_, lean_object* v_n_1860_, lean_object* v_xs_1861_, lean_object* v_i_1862_, lean_object* v_h_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Array_eraseIdx___redArg(v_xs_1861_, v_i_1862_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___boxed(lean_object* v_00_u03b1_1865_, lean_object* v_n_1866_, lean_object* v_xs_1867_, lean_object* v_i_1868_, lean_object* v_h_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Vector_eraseIdx(v_00_u03b1_1865_, v_n_1866_, v_xs_1867_, v_i_1868_, v_h_1869_);
lean_dec(v_n_1866_);
return v_res_1870_;
}
}
static lean_object* _init_l_Vector_eraseIdx_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1874_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1875_ = lean_unsigned_to_nat(4u);
v___x_1876_ = lean_unsigned_to_nat(407u);
v___x_1877_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__1));
v___x_1878_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1879_ = l_mkPanicMessageWithDecl(v___x_1878_, v___x_1877_, v___x_1876_, v___x_1875_, v___x_1874_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg(lean_object* v_n_1880_, lean_object* v_xs_1881_, lean_object* v_i_1882_){
_start:
{
uint8_t v___x_1883_; 
v___x_1883_ = lean_nat_dec_lt(v_i_1882_, v_n_1880_);
if (v___x_1883_ == 0)
{
lean_object* v_this_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec(v_i_1882_);
v_this_1884_ = lean_array_pop(v_xs_1881_);
v___x_1885_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1886_ = l_panic___redArg(v_this_1884_, v___x_1885_);
lean_dec_ref(v_this_1884_);
return v___x_1886_;
}
else
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Array_eraseIdx___redArg(v_xs_1881_, v_i_1882_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg___boxed(lean_object* v_n_1888_, lean_object* v_xs_1889_, lean_object* v_i_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Vector_eraseIdx_x21___redArg(v_n_1888_, v_xs_1889_, v_i_1890_);
lean_dec(v_n_1888_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21(lean_object* v_00_u03b1_1892_, lean_object* v_n_1893_, lean_object* v_xs_1894_, lean_object* v_i_1895_){
_start:
{
uint8_t v___x_1896_; 
v___x_1896_ = lean_nat_dec_lt(v_i_1895_, v_n_1893_);
if (v___x_1896_ == 0)
{
lean_object* v_this_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_dec(v_i_1895_);
v_this_1897_ = lean_array_pop(v_xs_1894_);
v___x_1898_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1899_ = l_panic___redArg(v_this_1897_, v___x_1898_);
lean_dec_ref(v_this_1897_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Array_eraseIdx___redArg(v_xs_1894_, v_i_1895_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___boxed(lean_object* v_00_u03b1_1901_, lean_object* v_n_1902_, lean_object* v_xs_1903_, lean_object* v_i_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Vector_eraseIdx_x21(v_00_u03b1_1901_, v_n_1902_, v_xs_1903_, v_i_1904_);
lean_dec(v_n_1902_);
return v_res_1905_;
}
}
static lean_object* _init_l_Vector_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg(lean_object* v_xs_1907_, lean_object* v_i_1908_, lean_object* v_x_1909_){
_start:
{
lean_object* v_j_1910_; lean_object* v_as_1911_; lean_object* v___x_1912_; 
v_j_1910_ = lean_array_get_size(v_xs_1907_);
v_as_1911_ = lean_array_push(v_xs_1907_, v_x_1909_);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1908_, v_as_1911_, v_j_1910_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg___boxed(lean_object* v_xs_1913_, lean_object* v_i_1914_, lean_object* v_x_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Vector_insertIdx___redArg(v_xs_1913_, v_i_1914_, v_x_1915_);
lean_dec(v_i_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx(lean_object* v_00_u03b1_1917_, lean_object* v_n_1918_, lean_object* v_xs_1919_, lean_object* v_i_1920_, lean_object* v_x_1921_, lean_object* v_h_1922_){
_start:
{
lean_object* v_j_1923_; lean_object* v_as_1924_; lean_object* v___x_1925_; 
v_j_1923_ = lean_array_get_size(v_xs_1919_);
v_as_1924_ = lean_array_push(v_xs_1919_, v_x_1921_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1920_, v_as_1924_, v_j_1923_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___boxed(lean_object* v_00_u03b1_1926_, lean_object* v_n_1927_, lean_object* v_xs_1928_, lean_object* v_i_1929_, lean_object* v_x_1930_, lean_object* v_h_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Vector_insertIdx(v_00_u03b1_1926_, v_n_1927_, v_xs_1928_, v_i_1929_, v_x_1930_, v_h_1931_);
lean_dec(v_i_1929_);
lean_dec(v_n_1927_);
return v_res_1932_;
}
}
static lean_object* _init_l_Vector_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1934_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1935_ = lean_unsigned_to_nat(4u);
v___x_1936_ = lean_unsigned_to_nat(420u);
v___x_1937_ = ((lean_object*)(l_Vector_insertIdx_x21___redArg___closed__0));
v___x_1938_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1939_ = l_mkPanicMessageWithDecl(v___x_1938_, v___x_1937_, v___x_1936_, v___x_1935_, v___x_1934_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg(lean_object* v_n_1940_, lean_object* v_xs_1941_, lean_object* v_i_1942_, lean_object* v_x_1943_){
_start:
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_nat_dec_le(v_i_1942_, v_n_1940_);
if (v___x_1944_ == 0)
{
lean_object* v_this_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_this_1945_ = lean_array_push(v_xs_1941_, v_x_1943_);
v___x_1946_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1947_ = l_panic___redArg(v_this_1945_, v___x_1946_);
lean_dec_ref(v_this_1945_);
return v___x_1947_;
}
else
{
lean_object* v_j_1948_; lean_object* v_as_1949_; lean_object* v___x_1950_; 
v_j_1948_ = lean_array_get_size(v_xs_1941_);
v_as_1949_ = lean_array_push(v_xs_1941_, v_x_1943_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1942_, v_as_1949_, v_j_1948_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg___boxed(lean_object* v_n_1951_, lean_object* v_xs_1952_, lean_object* v_i_1953_, lean_object* v_x_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Vector_insertIdx_x21___redArg(v_n_1951_, v_xs_1952_, v_i_1953_, v_x_1954_);
lean_dec(v_i_1953_);
lean_dec(v_n_1951_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21(lean_object* v_00_u03b1_1956_, lean_object* v_n_1957_, lean_object* v_xs_1958_, lean_object* v_i_1959_, lean_object* v_x_1960_){
_start:
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_nat_dec_le(v_i_1959_, v_n_1957_);
if (v___x_1961_ == 0)
{
lean_object* v_this_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v_this_1962_ = lean_array_push(v_xs_1958_, v_x_1960_);
v___x_1963_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1964_ = l_panic___redArg(v_this_1962_, v___x_1963_);
lean_dec_ref(v_this_1962_);
return v___x_1964_;
}
else
{
lean_object* v_j_1965_; lean_object* v_as_1966_; lean_object* v___x_1967_; 
v_j_1965_ = lean_array_get_size(v_xs_1958_);
v_as_1966_ = lean_array_push(v_xs_1958_, v_x_1960_);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1959_, v_as_1966_, v_j_1965_);
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___boxed(lean_object* v_00_u03b1_1968_, lean_object* v_n_1969_, lean_object* v_xs_1970_, lean_object* v_i_1971_, lean_object* v_x_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Vector_insertIdx_x21(v_00_u03b1_1968_, v_n_1969_, v_xs_1970_, v_i_1971_, v_x_1972_);
lean_dec(v_i_1971_);
lean_dec(v_n_1969_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg(lean_object* v_n_1974_, lean_object* v_xs_1975_){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_unsigned_to_nat(1u);
v___x_1977_ = l_Array_extract___redArg(v_xs_1975_, v___x_1976_, v_n_1974_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg___boxed(lean_object* v_n_1978_, lean_object* v_xs_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Vector_tail___redArg(v_n_1978_, v_xs_1979_);
lean_dec_ref(v_xs_1979_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail(lean_object* v_00_u03b1_1981_, lean_object* v_n_1982_, lean_object* v_xs_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_unsigned_to_nat(1u);
v___x_1985_ = l_Array_extract___redArg(v_xs_1983_, v___x_1984_, v_n_1982_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___boxed(lean_object* v_00_u03b1_1986_, lean_object* v_n_1987_, lean_object* v_xs_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Vector_tail(v_00_u03b1_1986_, v_n_1987_, v_xs_1988_);
lean_dec_ref(v_xs_1988_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg(lean_object* v_inst_1990_, lean_object* v_xs_1991_, lean_object* v_x_1992_){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Array_finIdxOf_x3f___redArg(v_inst_1990_, v_xs_1991_, v_x_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
return v___x_1993_;
}
else
{
lean_object* v_val_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_val_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_val_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_val_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_2002_, lean_object* v_xs_2003_, lean_object* v_x_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Vector_finIdxOf_x3f___redArg(v_inst_2002_, v_xs_2003_, v_x_2004_);
lean_dec_ref(v_xs_2003_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f(lean_object* v_00_u03b1_2006_, lean_object* v_n_2007_, lean_object* v_inst_2008_, lean_object* v_xs_2009_, lean_object* v_x_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Array_finIdxOf_x3f___redArg(v_inst_2008_, v_xs_2009_, v_x_2010_);
if (lean_obj_tag(v___x_2011_) == 0)
{
return v___x_2011_;
}
else
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v_val_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_val_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_n_2021_, lean_object* v_inst_2022_, lean_object* v_xs_2023_, lean_object* v_x_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Vector_finIdxOf_x3f(v_00_u03b1_2020_, v_n_2021_, v_inst_2022_, v_xs_2023_, v_x_2024_);
lean_dec_ref(v_xs_2023_);
lean_dec(v_n_2021_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg(lean_object* v_p_2026_, lean_object* v_xs_2027_){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2026_, v_xs_2027_, v___x_2028_);
if (lean_obj_tag(v___x_2029_) == 0)
{
return v___x_2029_;
}
else
{
lean_object* v_val_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
v_val_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_val_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_val_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2038_, lean_object* v_xs_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Vector_findFinIdx_x3f___redArg(v_p_2038_, v_xs_2039_);
lean_dec_ref(v_xs_2039_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f(lean_object* v_00_u03b1_2041_, lean_object* v_n_2042_, lean_object* v_p_2043_, lean_object* v_xs_2044_){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2043_, v_xs_2044_, v___x_2045_);
if (lean_obj_tag(v___x_2046_) == 0)
{
return v___x_2046_;
}
else
{
lean_object* v_val_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
v_val_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_val_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_val_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2055_, lean_object* v_n_2056_, lean_object* v_p_2057_, lean_object* v_xs_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Vector_findFinIdx_x3f(v_00_u03b1_2055_, v_n_2056_, v_p_2057_, v_xs_2058_);
lean_dec_ref(v_xs_2058_);
lean_dec(v_n_2056_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__0(lean_object* v_toPure_2060_, lean_object* v_____s_2061_){
_start:
{
lean_object* v_fst_2062_; 
v_fst_2062_ = lean_ctor_get(v_____s_2061_, 0);
lean_inc(v_fst_2062_);
lean_dec_ref(v_____s_2061_);
if (lean_obj_tag(v_fst_2062_) == 0)
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_apply_2(v_toPure_2060_, lean_box(0), v___x_2063_);
return v___x_2064_;
}
else
{
lean_object* v_val_2065_; lean_object* v___x_2066_; 
v_val_2065_ = lean_ctor_get(v_fst_2062_, 0);
lean_inc(v_val_2065_);
lean_dec_ref_known(v_fst_2062_, 1);
v___x_2066_ = lean_apply_2(v_toPure_2060_, lean_box(0), v_val_2065_);
return v___x_2066_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1(lean_object* v___x_2067_, lean_object* v_toPure_2068_, lean_object* v_a_2069_, lean_object* v___x_2070_, uint8_t v_____do__lift_2071_){
_start:
{
if (v_____do__lift_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec(v_a_2069_);
v___x_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2067_);
v___x_2073_ = lean_apply_2(v_toPure_2068_, lean_box(0), v___x_2072_);
return v___x_2073_;
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec_ref(v___x_2067_);
v___x_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2074_, 0, v_a_2069_);
v___x_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___x_2070_);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
v___x_2078_ = lean_apply_2(v_toPure_2068_, lean_box(0), v___x_2077_);
return v___x_2078_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_2079_, lean_object* v_toPure_2080_, lean_object* v_a_2081_, lean_object* v___x_2082_, lean_object* v_____do__lift_2083_){
_start:
{
uint8_t v_____do__lift_124__boxed_2084_; lean_object* v_res_2085_; 
v_____do__lift_124__boxed_2084_ = lean_unbox(v_____do__lift_2083_);
v_res_2085_ = l_Vector_findM_x3f___redArg___lam__1(v___x_2079_, v_toPure_2080_, v_a_2081_, v___x_2082_, v_____do__lift_124__boxed_2084_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2(lean_object* v___x_2086_, lean_object* v_toPure_2087_, lean_object* v___x_2088_, lean_object* v_f_2089_, lean_object* v_toBind_2090_, lean_object* v_a_2091_, lean_object* v_x_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___f_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_inc(v_a_2091_);
v___f_2094_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2094_, 0, v___x_2086_);
lean_closure_set(v___f_2094_, 1, v_toPure_2087_);
lean_closure_set(v___f_2094_, 2, v_a_2091_);
lean_closure_set(v___f_2094_, 3, v___x_2088_);
v___x_2095_ = lean_apply_1(v_f_2089_, v_a_2091_);
v___x_2096_ = lean_apply_4(v_toBind_2090_, lean_box(0), lean_box(0), v___x_2095_, v___f_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2___boxed(lean_object* v___x_2097_, lean_object* v_toPure_2098_, lean_object* v___x_2099_, lean_object* v_f_2100_, lean_object* v_toBind_2101_, lean_object* v_a_2102_, lean_object* v_x_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Vector_findM_x3f___redArg___lam__2(v___x_2097_, v_toPure_2098_, v___x_2099_, v_f_2100_, v_toBind_2101_, v_a_2102_, v_x_2103_, v___y_2104_);
lean_dec_ref(v___y_2104_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg(lean_object* v_inst_2109_, lean_object* v_f_2110_, lean_object* v_as_2111_){
_start:
{
lean_object* v_toApplicative_2112_; lean_object* v_toBind_2113_; lean_object* v_toPure_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___f_2117_; lean_object* v___f_2118_; size_t v_sz_2119_; size_t v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_toApplicative_2112_ = lean_ctor_get(v_inst_2109_, 0);
v_toBind_2113_ = lean_ctor_get(v_inst_2109_, 1);
lean_inc_n(v_toBind_2113_, 2);
v_toPure_2114_ = lean_ctor_get(v_toApplicative_2112_, 1);
v___x_2115_ = lean_box(0);
v___x_2116_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2114_, 2);
v___f_2117_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2117_, 0, v_toPure_2114_);
v___f_2118_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2118_, 0, v___x_2116_);
lean_closure_set(v___f_2118_, 1, v_toPure_2114_);
lean_closure_set(v___f_2118_, 2, v___x_2115_);
lean_closure_set(v___f_2118_, 3, v_f_2110_);
lean_closure_set(v___f_2118_, 4, v_toBind_2113_);
v_sz_2119_ = lean_array_size(v_as_2111_);
v___x_2120_ = ((size_t)0ULL);
v___x_2121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2109_, v_as_2111_, v___f_2118_, v_sz_2119_, v___x_2120_, v___x_2116_);
v___x_2122_ = lean_apply_4(v_toBind_2113_, lean_box(0), lean_box(0), v___x_2121_, v___f_2117_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f(lean_object* v_n_2123_, lean_object* v_00_u03b1_2124_, lean_object* v_m_2125_, lean_object* v_inst_2126_, lean_object* v_f_2127_, lean_object* v_as_2128_){
_start:
{
lean_object* v_toApplicative_2129_; lean_object* v_toBind_2130_; lean_object* v_toPure_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; lean_object* v___f_2135_; size_t v_sz_2136_; size_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_toApplicative_2129_ = lean_ctor_get(v_inst_2126_, 0);
v_toBind_2130_ = lean_ctor_get(v_inst_2126_, 1);
lean_inc_n(v_toBind_2130_, 2);
v_toPure_2131_ = lean_ctor_get(v_toApplicative_2129_, 1);
v___x_2132_ = lean_box(0);
v___x_2133_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2131_, 2);
v___f_2134_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2134_, 0, v_toPure_2131_);
v___f_2135_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2135_, 0, v___x_2133_);
lean_closure_set(v___f_2135_, 1, v_toPure_2131_);
lean_closure_set(v___f_2135_, 2, v___x_2132_);
lean_closure_set(v___f_2135_, 3, v_f_2127_);
lean_closure_set(v___f_2135_, 4, v_toBind_2130_);
v_sz_2136_ = lean_array_size(v_as_2128_);
v___x_2137_ = ((size_t)0ULL);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2126_, v_as_2128_, v___f_2135_, v_sz_2136_, v___x_2137_, v___x_2133_);
v___x_2139_ = lean_apply_4(v_toBind_2130_, lean_box(0), lean_box(0), v___x_2138_, v___f_2134_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___boxed(lean_object* v_n_2140_, lean_object* v_00_u03b1_2141_, lean_object* v_m_2142_, lean_object* v_inst_2143_, lean_object* v_f_2144_, lean_object* v_as_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Vector_findM_x3f(v_n_2140_, v_00_u03b1_2141_, v_m_2142_, v_inst_2143_, v_f_2144_, v_as_2145_);
lean_dec(v_n_2140_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__1(lean_object* v___x_2147_, lean_object* v_toPure_2148_, lean_object* v___x_2149_, lean_object* v_____do__lift_2150_){
_start:
{
if (lean_obj_tag(v_____do__lift_2150_) == 1)
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec_ref(v___x_2149_);
v___x_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2151_, 0, v_____do__lift_2150_);
v___x_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v___x_2147_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
v___x_2154_ = lean_apply_2(v_toPure_2148_, lean_box(0), v___x_2153_);
return v___x_2154_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_dec(v_____do__lift_2150_);
v___x_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2149_);
v___x_2156_ = lean_apply_2(v_toPure_2148_, lean_box(0), v___x_2155_);
return v___x_2156_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0(lean_object* v_f_2157_, lean_object* v_toBind_2158_, lean_object* v___f_2159_, lean_object* v_a_2160_, lean_object* v_x_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = lean_apply_1(v_f_2157_, v_a_2160_);
v___x_2164_ = lean_apply_4(v_toBind_2158_, lean_box(0), lean_box(0), v___x_2163_, v___f_2159_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0___boxed(lean_object* v_f_2165_, lean_object* v_toBind_2166_, lean_object* v___f_2167_, lean_object* v_a_2168_, lean_object* v_x_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Vector_findSomeM_x3f___redArg___lam__0(v_f_2165_, v_toBind_2166_, v___f_2167_, v_a_2168_, v_x_2169_, v___y_2170_);
lean_dec_ref(v___y_2170_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg(lean_object* v_inst_2172_, lean_object* v_f_2173_, lean_object* v_as_2174_){
_start:
{
lean_object* v_toApplicative_2175_; lean_object* v_toBind_2176_; lean_object* v_toPure_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___f_2180_; lean_object* v___f_2181_; lean_object* v___f_2182_; size_t v_sz_2183_; size_t v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_toApplicative_2175_ = lean_ctor_get(v_inst_2172_, 0);
v_toBind_2176_ = lean_ctor_get(v_inst_2172_, 1);
lean_inc_n(v_toBind_2176_, 2);
v_toPure_2177_ = lean_ctor_get(v_toApplicative_2175_, 1);
v___x_2178_ = lean_box(0);
v___x_2179_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2177_, 2);
v___f_2180_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2180_, 0, v_toPure_2177_);
v___f_2181_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2181_, 0, v___x_2178_);
lean_closure_set(v___f_2181_, 1, v_toPure_2177_);
lean_closure_set(v___f_2181_, 2, v___x_2179_);
v___f_2182_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2182_, 0, v_f_2173_);
lean_closure_set(v___f_2182_, 1, v_toBind_2176_);
lean_closure_set(v___f_2182_, 2, v___f_2181_);
v_sz_2183_ = lean_array_size(v_as_2174_);
v___x_2184_ = ((size_t)0ULL);
v___x_2185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2172_, v_as_2174_, v___f_2182_, v_sz_2183_, v___x_2184_, v___x_2179_);
v___x_2186_ = lean_apply_4(v_toBind_2176_, lean_box(0), lean_box(0), v___x_2185_, v___f_2180_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f(lean_object* v_m_2187_, lean_object* v_00_u03b1_2188_, lean_object* v_00_u03b2_2189_, lean_object* v_n_2190_, lean_object* v_inst_2191_, lean_object* v_f_2192_, lean_object* v_as_2193_){
_start:
{
lean_object* v_toApplicative_2194_; lean_object* v_toBind_2195_; lean_object* v_toPure_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___f_2199_; lean_object* v___f_2200_; lean_object* v___f_2201_; size_t v_sz_2202_; size_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_toApplicative_2194_ = lean_ctor_get(v_inst_2191_, 0);
v_toBind_2195_ = lean_ctor_get(v_inst_2191_, 1);
lean_inc_n(v_toBind_2195_, 2);
v_toPure_2196_ = lean_ctor_get(v_toApplicative_2194_, 1);
v___x_2197_ = lean_box(0);
v___x_2198_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2196_, 2);
v___f_2199_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2199_, 0, v_toPure_2196_);
v___f_2200_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2200_, 0, v___x_2197_);
lean_closure_set(v___f_2200_, 1, v_toPure_2196_);
lean_closure_set(v___f_2200_, 2, v___x_2198_);
v___f_2201_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2201_, 0, v_f_2192_);
lean_closure_set(v___f_2201_, 1, v_toBind_2195_);
lean_closure_set(v___f_2201_, 2, v___f_2200_);
v_sz_2202_ = lean_array_size(v_as_2193_);
v___x_2203_ = ((size_t)0ULL);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2191_, v_as_2193_, v___f_2201_, v_sz_2202_, v___x_2203_, v___x_2198_);
v___x_2205_ = lean_apply_4(v_toBind_2195_, lean_box(0), lean_box(0), v___x_2204_, v___f_2199_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___boxed(lean_object* v_m_2206_, lean_object* v_00_u03b1_2207_, lean_object* v_00_u03b2_2208_, lean_object* v_n_2209_, lean_object* v_inst_2210_, lean_object* v_f_2211_, lean_object* v_as_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Vector_findSomeM_x3f(v_m_2206_, v_00_u03b1_2207_, v_00_u03b2_2208_, v_n_2209_, v_inst_2210_, v_f_2211_, v_as_2212_);
lean_dec(v_n_2209_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2214_, lean_object* v_a_2215_, uint8_t v_____do__lift_2216_){
_start:
{
if (v_____do__lift_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec(v_a_2215_);
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_apply_2(v_toPure_2214_, lean_box(0), v___x_2217_);
return v___x_2218_;
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_a_2215_);
v___x_2220_ = lean_apply_2(v_toPure_2214_, lean_box(0), v___x_2219_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2221_, lean_object* v_a_2222_, lean_object* v_____do__lift_2223_){
_start:
{
uint8_t v_____do__lift_50__boxed_2224_; lean_object* v_res_2225_; 
v_____do__lift_50__boxed_2224_ = lean_unbox(v_____do__lift_2223_);
v_res_2225_ = l_Vector_findRevM_x3f___redArg___lam__0(v_toPure_2221_, v_a_2222_, v_____do__lift_50__boxed_2224_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2226_, lean_object* v_f_2227_, lean_object* v_toBind_2228_, lean_object* v_a_2229_){
_start:
{
lean_object* v___f_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_inc(v_a_2229_);
v___f_2230_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2230_, 0, v_toPure_2226_);
lean_closure_set(v___f_2230_, 1, v_a_2229_);
v___x_2231_ = lean_apply_1(v_f_2227_, v_a_2229_);
v___x_2232_ = lean_apply_4(v_toBind_2228_, lean_box(0), lean_box(0), v___x_2231_, v___f_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg(lean_object* v_inst_2233_, lean_object* v_f_2234_, lean_object* v_as_2235_){
_start:
{
lean_object* v_toApplicative_2236_; lean_object* v_toBind_2237_; lean_object* v_toPure_2238_; lean_object* v___f_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_toApplicative_2236_ = lean_ctor_get(v_inst_2233_, 0);
v_toBind_2237_ = lean_ctor_get(v_inst_2233_, 1);
v_toPure_2238_ = lean_ctor_get(v_toApplicative_2236_, 1);
lean_inc(v_toBind_2237_);
lean_inc(v_toPure_2238_);
v___f_2239_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2239_, 0, v_toPure_2238_);
lean_closure_set(v___f_2239_, 1, v_f_2234_);
lean_closure_set(v___f_2239_, 2, v_toBind_2237_);
v___x_2240_ = lean_array_get_size(v_as_2235_);
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2233_, v___f_2239_, v_as_2235_, v___x_2240_, lean_box(0));
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f(lean_object* v_n_2242_, lean_object* v_00_u03b1_2243_, lean_object* v_m_2244_, lean_object* v_inst_2245_, lean_object* v_f_2246_, lean_object* v_as_2247_){
_start:
{
lean_object* v_toApplicative_2248_; lean_object* v_toBind_2249_; lean_object* v_toPure_2250_; lean_object* v___f_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_toApplicative_2248_ = lean_ctor_get(v_inst_2245_, 0);
v_toBind_2249_ = lean_ctor_get(v_inst_2245_, 1);
v_toPure_2250_ = lean_ctor_get(v_toApplicative_2248_, 1);
lean_inc(v_toBind_2249_);
lean_inc(v_toPure_2250_);
v___f_2251_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2251_, 0, v_toPure_2250_);
lean_closure_set(v___f_2251_, 1, v_f_2246_);
lean_closure_set(v___f_2251_, 2, v_toBind_2249_);
v___x_2252_ = lean_array_get_size(v_as_2247_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2245_, v___f_2251_, v_as_2247_, v___x_2252_, lean_box(0));
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___boxed(lean_object* v_n_2254_, lean_object* v_00_u03b1_2255_, lean_object* v_m_2256_, lean_object* v_inst_2257_, lean_object* v_f_2258_, lean_object* v_as_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Vector_findRevM_x3f(v_n_2254_, v_00_u03b1_2255_, v_m_2256_, v_inst_2257_, v_f_2258_, v_as_2259_);
lean_dec(v_n_2254_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___redArg(lean_object* v_inst_2261_, lean_object* v_f_2262_, lean_object* v_as_2263_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_array_get_size(v_as_2263_);
v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2261_, v_f_2262_, v_as_2263_, v___x_2264_, lean_box(0));
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f(lean_object* v_m_2266_, lean_object* v_00_u03b1_2267_, lean_object* v_00_u03b2_2268_, lean_object* v_n_2269_, lean_object* v_inst_2270_, lean_object* v_f_2271_, lean_object* v_as_2272_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_array_get_size(v_as_2272_);
v___x_2274_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2270_, v_f_2271_, v_as_2272_, v___x_2273_, lean_box(0));
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___boxed(lean_object* v_m_2275_, lean_object* v_00_u03b1_2276_, lean_object* v_00_u03b2_2277_, lean_object* v_n_2278_, lean_object* v_inst_2279_, lean_object* v_f_2280_, lean_object* v_as_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Vector_findSomeRevM_x3f(v_m_2275_, v_00_u03b1_2276_, v_00_u03b2_2277_, v_n_2278_, v_inst_2279_, v_f_2280_, v_as_2281_);
lean_dec(v_n_2278_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0(lean_object* v_f_2283_, lean_object* v___x_2284_, lean_object* v___x_2285_, lean_object* v_a_2286_, lean_object* v_x_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___x_2289_; uint8_t v___x_2290_; 
lean_inc(v_a_2286_);
v___x_2289_ = lean_apply_1(v_f_2283_, v_a_2286_);
v___x_2290_ = lean_unbox(v___x_2289_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; 
lean_dec(v_a_2286_);
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2284_);
return v___x_2291_;
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec_ref(v___x_2284_);
v___x_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2292_, 0, v_a_2286_);
v___x_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v___x_2285_);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
return v___x_2295_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0___boxed(lean_object* v_f_2296_, lean_object* v___x_2297_, lean_object* v___x_2298_, lean_object* v_a_2299_, lean_object* v_x_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Vector_find_x3f___redArg___lam__0(v_f_2296_, v___x_2297_, v___x_2298_, v_a_2299_, v_x_2300_, v___y_2301_);
lean_dec_ref(v___y_2301_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg(lean_object* v_f_2303_, lean_object* v_as_2304_){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___f_2309_; size_t v_sz_2310_; size_t v___x_2311_; lean_object* v___x_2312_; lean_object* v_fst_2313_; 
v___x_2305_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2306_ = lean_box(0);
v___x_2307_ = lean_box(0);
v___x_2308_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2309_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2309_, 0, v_f_2303_);
lean_closure_set(v___f_2309_, 1, v___x_2308_);
lean_closure_set(v___f_2309_, 2, v___x_2307_);
v_sz_2310_ = lean_array_size(v_as_2304_);
v___x_2311_ = ((size_t)0ULL);
v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2305_, v_as_2304_, v___f_2309_, v_sz_2310_, v___x_2311_, v___x_2308_);
v_fst_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_fst_2313_);
lean_dec(v___x_2312_);
if (lean_obj_tag(v_fst_2313_) == 0)
{
return v___x_2306_;
}
else
{
lean_object* v_val_2314_; 
v_val_2314_ = lean_ctor_get(v_fst_2313_, 0);
lean_inc(v_val_2314_);
lean_dec_ref_known(v_fst_2313_, 1);
return v_val_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f(lean_object* v_n_2315_, lean_object* v_00_u03b1_2316_, lean_object* v_f_2317_, lean_object* v_as_2318_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___f_2323_; size_t v_sz_2324_; size_t v___x_2325_; lean_object* v___x_2326_; lean_object* v_fst_2327_; 
v___x_2319_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_box(0);
v___x_2322_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2323_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2323_, 0, v_f_2317_);
lean_closure_set(v___f_2323_, 1, v___x_2322_);
lean_closure_set(v___f_2323_, 2, v___x_2321_);
v_sz_2324_ = lean_array_size(v_as_2318_);
v___x_2325_ = ((size_t)0ULL);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2319_, v_as_2318_, v___f_2323_, v_sz_2324_, v___x_2325_, v___x_2322_);
v_fst_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_fst_2327_);
lean_dec(v___x_2326_);
if (lean_obj_tag(v_fst_2327_) == 0)
{
return v___x_2320_;
}
else
{
lean_object* v_val_2328_; 
v_val_2328_ = lean_ctor_get(v_fst_2327_, 0);
lean_inc(v_val_2328_);
lean_dec_ref_known(v_fst_2327_, 1);
return v_val_2328_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___boxed(lean_object* v_n_2329_, lean_object* v_00_u03b1_2330_, lean_object* v_f_2331_, lean_object* v_as_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Vector_find_x3f(v_n_2329_, v_00_u03b1_2330_, v_f_2331_, v_as_2332_);
lean_dec(v_n_2329_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg___lam__0(lean_object* v_f_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
lean_inc(v_a_2335_);
v___x_2336_ = lean_apply_1(v_f_2334_, v_a_2335_);
v___x_2337_ = lean_unbox(v___x_2336_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; 
lean_dec(v_a_2335_);
v___x_2338_ = lean_box(0);
return v___x_2338_;
}
else
{
lean_object* v___x_2339_; 
v___x_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2339_, 0, v_a_2335_);
return v___x_2339_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg(lean_object* v_f_2340_, lean_object* v_as_2341_){
_start:
{
lean_object* v___f_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___f_2342_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2342_, 0, v_f_2340_);
v___x_2343_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2344_ = lean_array_get_size(v_as_2341_);
v___x_2345_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2343_, v___f_2342_, v_as_2341_, v___x_2344_, lean_box(0));
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f(lean_object* v_n_2346_, lean_object* v_00_u03b1_2347_, lean_object* v_f_2348_, lean_object* v_as_2349_){
_start:
{
lean_object* v___f_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___f_2350_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2350_, 0, v_f_2348_);
v___x_2351_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2352_ = lean_array_get_size(v_as_2349_);
v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2351_, v___f_2350_, v_as_2349_, v___x_2352_, lean_box(0));
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___boxed(lean_object* v_n_2354_, lean_object* v_00_u03b1_2355_, lean_object* v_f_2356_, lean_object* v_as_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Vector_findRev_x3f(v_n_2354_, v_00_u03b1_2355_, v_f_2356_, v_as_2357_);
lean_dec(v_n_2354_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0(lean_object* v_f_2359_, lean_object* v___x_2360_, lean_object* v___x_2361_, lean_object* v_a_2362_, lean_object* v_x_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_apply_1(v_f_2359_, v_a_2362_);
if (lean_obj_tag(v___x_2365_) == 1)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_dec_ref(v___x_2361_);
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
lean_ctor_set(v___x_2367_, 1, v___x_2360_);
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
else
{
lean_object* v___x_2369_; 
lean_dec(v___x_2365_);
v___x_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2361_);
return v___x_2369_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2370_, lean_object* v___x_2371_, lean_object* v___x_2372_, lean_object* v_a_2373_, lean_object* v_x_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Vector_findSome_x3f___redArg___lam__0(v_f_2370_, v___x_2371_, v___x_2372_, v_a_2373_, v_x_2374_, v___y_2375_);
lean_dec_ref(v___y_2375_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg(lean_object* v_f_2377_, lean_object* v_as_2378_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___f_2383_; size_t v_sz_2384_; size_t v___x_2385_; lean_object* v___x_2386_; lean_object* v_fst_2387_; 
v___x_2379_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2380_ = lean_box(0);
v___x_2381_ = lean_box(0);
v___x_2382_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2383_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2383_, 0, v_f_2377_);
lean_closure_set(v___f_2383_, 1, v___x_2381_);
lean_closure_set(v___f_2383_, 2, v___x_2382_);
v_sz_2384_ = lean_array_size(v_as_2378_);
v___x_2385_ = ((size_t)0ULL);
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2379_, v_as_2378_, v___f_2383_, v_sz_2384_, v___x_2385_, v___x_2382_);
v_fst_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_fst_2387_);
lean_dec(v___x_2386_);
if (lean_obj_tag(v_fst_2387_) == 0)
{
return v___x_2380_;
}
else
{
lean_object* v_val_2388_; 
v_val_2388_ = lean_ctor_get(v_fst_2387_, 0);
lean_inc(v_val_2388_);
lean_dec_ref_known(v_fst_2387_, 1);
return v_val_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f(lean_object* v_00_u03b1_2389_, lean_object* v_00_u03b2_2390_, lean_object* v_n_2391_, lean_object* v_f_2392_, lean_object* v_as_2393_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___f_2398_; size_t v_sz_2399_; size_t v___x_2400_; lean_object* v___x_2401_; lean_object* v_fst_2402_; 
v___x_2394_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2395_ = lean_box(0);
v___x_2396_ = lean_box(0);
v___x_2397_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2398_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2398_, 0, v_f_2392_);
lean_closure_set(v___f_2398_, 1, v___x_2396_);
lean_closure_set(v___f_2398_, 2, v___x_2397_);
v_sz_2399_ = lean_array_size(v_as_2393_);
v___x_2400_ = ((size_t)0ULL);
v___x_2401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2394_, v_as_2393_, v___f_2398_, v_sz_2399_, v___x_2400_, v___x_2397_);
v_fst_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_fst_2402_);
lean_dec(v___x_2401_);
if (lean_obj_tag(v_fst_2402_) == 0)
{
return v___x_2395_;
}
else
{
lean_object* v_val_2403_; 
v_val_2403_ = lean_ctor_get(v_fst_2402_, 0);
lean_inc(v_val_2403_);
lean_dec_ref_known(v_fst_2402_, 1);
return v_val_2403_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___boxed(lean_object* v_00_u03b1_2404_, lean_object* v_00_u03b2_2405_, lean_object* v_n_2406_, lean_object* v_f_2407_, lean_object* v_as_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Vector_findSome_x3f(v_00_u03b1_2404_, v_00_u03b2_2405_, v_n_2406_, v_f_2407_, v_as_2408_);
lean_dec(v_n_2406_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2410_, lean_object* v_x_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_apply_1(v_f_2410_, v_x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg(lean_object* v_f_2413_, lean_object* v_as_2414_){
_start:
{
lean_object* v___f_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___f_2415_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2415_, 0, v_f_2413_);
v___x_2416_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2417_ = lean_array_get_size(v_as_2414_);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2416_, v___f_2415_, v_as_2414_, v___x_2417_, lean_box(0));
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f(lean_object* v_00_u03b1_2419_, lean_object* v_00_u03b2_2420_, lean_object* v_n_2421_, lean_object* v_f_2422_, lean_object* v_as_2423_){
_start:
{
lean_object* v___f_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___f_2424_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2424_, 0, v_f_2422_);
v___x_2425_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2426_ = lean_array_get_size(v_as_2423_);
v___x_2427_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2425_, v___f_2424_, v_as_2423_, v___x_2426_, lean_box(0));
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___boxed(lean_object* v_00_u03b1_2428_, lean_object* v_00_u03b2_2429_, lean_object* v_n_2430_, lean_object* v_f_2431_, lean_object* v_as_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Vector_findSomeRev_x3f(v_00_u03b1_2428_, v_00_u03b2_2429_, v_n_2430_, v_f_2431_, v_as_2432_);
lean_dec(v_n_2430_);
return v_res_2433_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf___redArg(lean_object* v_inst_2434_, lean_object* v_xs_2435_, lean_object* v_ys_2436_){
_start:
{
uint8_t v___x_2437_; 
v___x_2437_ = l_Array_isPrefixOf___redArg(v_inst_2434_, v_xs_2435_, v_ys_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___redArg___boxed(lean_object* v_inst_2438_, lean_object* v_xs_2439_, lean_object* v_ys_2440_){
_start:
{
uint8_t v_res_2441_; lean_object* v_r_2442_; 
v_res_2441_ = l_Vector_isPrefixOf___redArg(v_inst_2438_, v_xs_2439_, v_ys_2440_);
lean_dec_ref(v_ys_2440_);
lean_dec_ref(v_xs_2439_);
v_r_2442_ = lean_box(v_res_2441_);
return v_r_2442_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf(lean_object* v_00_u03b1_2443_, lean_object* v_m_2444_, lean_object* v_n_2445_, lean_object* v_inst_2446_, lean_object* v_xs_2447_, lean_object* v_ys_2448_){
_start:
{
uint8_t v___x_2449_; 
v___x_2449_ = l_Array_isPrefixOf___redArg(v_inst_2446_, v_xs_2447_, v_ys_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___boxed(lean_object* v_00_u03b1_2450_, lean_object* v_m_2451_, lean_object* v_n_2452_, lean_object* v_inst_2453_, lean_object* v_xs_2454_, lean_object* v_ys_2455_){
_start:
{
uint8_t v_res_2456_; lean_object* v_r_2457_; 
v_res_2456_ = l_Vector_isPrefixOf(v_00_u03b1_2450_, v_m_2451_, v_n_2452_, v_inst_2453_, v_xs_2454_, v_ys_2455_);
lean_dec_ref(v_ys_2455_);
lean_dec_ref(v_xs_2454_);
lean_dec(v_n_2452_);
lean_dec(v_m_2451_);
v_r_2457_ = lean_box(v_res_2456_);
return v_r_2457_;
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___redArg(lean_object* v_inst_2458_, lean_object* v_p_2459_, lean_object* v_xs_2460_){
_start:
{
lean_object* v_toApplicative_2461_; lean_object* v_toPure_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; 
v_toApplicative_2461_ = lean_ctor_get(v_inst_2458_, 0);
v_toPure_2462_ = lean_ctor_get(v_toApplicative_2461_, 1);
v___x_2463_ = lean_unsigned_to_nat(0u);
v___x_2464_ = lean_array_get_size(v_xs_2460_);
v___x_2465_ = lean_nat_dec_lt(v___x_2463_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_inc(v_toPure_2462_);
lean_dec_ref(v_xs_2460_);
lean_dec(v_p_2459_);
lean_dec_ref(v_inst_2458_);
v___x_2466_ = lean_box(v___x_2465_);
v___x_2467_ = lean_apply_2(v_toPure_2462_, lean_box(0), v___x_2466_);
return v___x_2467_;
}
else
{
if (v___x_2465_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_inc(v_toPure_2462_);
lean_dec_ref(v_xs_2460_);
lean_dec(v_p_2459_);
lean_dec_ref(v_inst_2458_);
v___x_2468_ = lean_box(v___x_2465_);
v___x_2469_ = lean_apply_2(v_toPure_2462_, lean_box(0), v___x_2468_);
return v___x_2469_;
}
else
{
size_t v___x_2470_; size_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = ((size_t)0ULL);
v___x_2471_ = lean_usize_of_nat(v___x_2464_);
v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2458_, v_p_2459_, v_xs_2460_, v___x_2470_, v___x_2471_);
return v___x_2472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM(lean_object* v_m_2473_, lean_object* v_00_u03b1_2474_, lean_object* v_n_2475_, lean_object* v_inst_2476_, lean_object* v_p_2477_, lean_object* v_xs_2478_){
_start:
{
lean_object* v_toApplicative_2479_; lean_object* v_toPure_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_toApplicative_2479_ = lean_ctor_get(v_inst_2476_, 0);
v_toPure_2480_ = lean_ctor_get(v_toApplicative_2479_, 1);
v___x_2481_ = lean_unsigned_to_nat(0u);
v___x_2482_ = lean_array_get_size(v_xs_2478_);
v___x_2483_ = lean_nat_dec_lt(v___x_2481_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_inc(v_toPure_2480_);
lean_dec_ref(v_xs_2478_);
lean_dec(v_p_2477_);
lean_dec_ref(v_inst_2476_);
v___x_2484_ = lean_box(v___x_2483_);
v___x_2485_ = lean_apply_2(v_toPure_2480_, lean_box(0), v___x_2484_);
return v___x_2485_;
}
else
{
if (v___x_2483_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_inc(v_toPure_2480_);
lean_dec_ref(v_xs_2478_);
lean_dec(v_p_2477_);
lean_dec_ref(v_inst_2476_);
v___x_2486_ = lean_box(v___x_2483_);
v___x_2487_ = lean_apply_2(v_toPure_2480_, lean_box(0), v___x_2486_);
return v___x_2487_;
}
else
{
size_t v___x_2488_; size_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = ((size_t)0ULL);
v___x_2489_ = lean_usize_of_nat(v___x_2482_);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2476_, v_p_2477_, v_xs_2478_, v___x_2488_, v___x_2489_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___boxed(lean_object* v_m_2491_, lean_object* v_00_u03b1_2492_, lean_object* v_n_2493_, lean_object* v_inst_2494_, lean_object* v_p_2495_, lean_object* v_xs_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Vector_anyM(v_m_2491_, v_00_u03b1_2492_, v_n_2493_, v_inst_2494_, v_p_2495_, v_xs_2496_);
lean_dec(v_n_2493_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0(lean_object* v_toPure_2498_, uint8_t v_____do__lift_2499_){
_start:
{
if (v_____do__lift_2499_ == 0)
{
uint8_t v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = 1;
v___x_2501_ = lean_box(v___x_2500_);
v___x_2502_ = lean_apply_2(v_toPure_2498_, lean_box(0), v___x_2501_);
return v___x_2502_;
}
else
{
uint8_t v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = 0;
v___x_2504_ = lean_box(v___x_2503_);
v___x_2505_ = lean_apply_2(v_toPure_2498_, lean_box(0), v___x_2504_);
return v___x_2505_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0___boxed(lean_object* v_toPure_2506_, lean_object* v_____do__lift_2507_){
_start:
{
uint8_t v_____do__lift_112__boxed_2508_; lean_object* v_res_2509_; 
v_____do__lift_112__boxed_2508_ = lean_unbox(v_____do__lift_2507_);
v_res_2509_ = l_Vector_allM___redArg___lam__0(v_toPure_2506_, v_____do__lift_112__boxed_2508_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1(lean_object* v_toPure_2510_, uint8_t v___x_2511_, uint8_t v_____do__lift_2512_){
_start:
{
if (v_____do__lift_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_box(v___x_2511_);
v___x_2514_ = lean_apply_2(v_toPure_2510_, lean_box(0), v___x_2513_);
return v___x_2514_;
}
else
{
uint8_t v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = 0;
v___x_2516_ = lean_box(v___x_2515_);
v___x_2517_ = lean_apply_2(v_toPure_2510_, lean_box(0), v___x_2516_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1___boxed(lean_object* v_toPure_2518_, lean_object* v___x_2519_, lean_object* v_____do__lift_2520_){
_start:
{
uint8_t v___x_127__boxed_2521_; uint8_t v_____do__lift_128__boxed_2522_; lean_object* v_res_2523_; 
v___x_127__boxed_2521_ = lean_unbox(v___x_2519_);
v_____do__lift_128__boxed_2522_ = lean_unbox(v_____do__lift_2520_);
v_res_2523_ = l_Vector_allM___redArg___lam__1(v_toPure_2518_, v___x_127__boxed_2521_, v_____do__lift_128__boxed_2522_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__2(lean_object* v_p_2524_, lean_object* v_toBind_2525_, lean_object* v___f_2526_, lean_object* v_v_2527_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_apply_1(v_p_2524_, v_v_2527_);
v___x_2529_ = lean_apply_4(v_toBind_2525_, lean_box(0), lean_box(0), v___x_2528_, v___f_2526_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg(lean_object* v_inst_2530_, lean_object* v_p_2531_, lean_object* v_xs_2532_){
_start:
{
lean_object* v_toApplicative_2533_; lean_object* v_toBind_2534_; lean_object* v_toPure_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___f_2538_; uint8_t v___x_2539_; 
v_toApplicative_2533_ = lean_ctor_get(v_inst_2530_, 0);
v_toBind_2534_ = lean_ctor_get(v_inst_2530_, 1);
lean_inc(v_toBind_2534_);
v_toPure_2535_ = lean_ctor_get(v_toApplicative_2533_, 1);
v___x_2536_ = lean_unsigned_to_nat(0u);
v___x_2537_ = lean_array_get_size(v_xs_2532_);
lean_inc(v_toPure_2535_);
v___f_2538_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2538_, 0, v_toPure_2535_);
v___x_2539_ = lean_nat_dec_lt(v___x_2536_, v___x_2537_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_inc(v_toPure_2535_);
lean_dec_ref(v_xs_2532_);
lean_dec(v_p_2531_);
lean_dec_ref(v_inst_2530_);
v___x_2540_ = lean_box(v___x_2539_);
v___x_2541_ = lean_apply_2(v_toPure_2535_, lean_box(0), v___x_2540_);
v___x_2542_ = lean_apply_4(v_toBind_2534_, lean_box(0), lean_box(0), v___x_2541_, v___f_2538_);
return v___x_2542_;
}
else
{
if (v___x_2539_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_inc(v_toPure_2535_);
lean_dec_ref(v_xs_2532_);
lean_dec(v_p_2531_);
lean_dec_ref(v_inst_2530_);
v___x_2543_ = lean_box(v___x_2539_);
v___x_2544_ = lean_apply_2(v_toPure_2535_, lean_box(0), v___x_2543_);
v___x_2545_ = lean_apply_4(v_toBind_2534_, lean_box(0), lean_box(0), v___x_2544_, v___f_2538_);
return v___x_2545_;
}
else
{
lean_object* v___x_2546_; lean_object* v___f_2547_; lean_object* v___f_2548_; size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2546_ = lean_box(v___x_2539_);
lean_inc(v_toPure_2535_);
v___f_2547_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2547_, 0, v_toPure_2535_);
lean_closure_set(v___f_2547_, 1, v___x_2546_);
lean_inc(v_toBind_2534_);
v___f_2548_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2548_, 0, v_p_2531_);
lean_closure_set(v___f_2548_, 1, v_toBind_2534_);
lean_closure_set(v___f_2548_, 2, v___f_2547_);
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = lean_usize_of_nat(v___x_2537_);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2530_, v___f_2548_, v_xs_2532_, v___x_2549_, v___x_2550_);
v___x_2552_ = lean_apply_4(v_toBind_2534_, lean_box(0), lean_box(0), v___x_2551_, v___f_2538_);
return v___x_2552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM(lean_object* v_m_2553_, lean_object* v_00_u03b1_2554_, lean_object* v_n_2555_, lean_object* v_inst_2556_, lean_object* v_p_2557_, lean_object* v_xs_2558_){
_start:
{
lean_object* v_toApplicative_2559_; lean_object* v_toBind_2560_; lean_object* v_toPure_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___f_2564_; uint8_t v___x_2565_; 
v_toApplicative_2559_ = lean_ctor_get(v_inst_2556_, 0);
v_toBind_2560_ = lean_ctor_get(v_inst_2556_, 1);
lean_inc(v_toBind_2560_);
v_toPure_2561_ = lean_ctor_get(v_toApplicative_2559_, 1);
v___x_2562_ = lean_unsigned_to_nat(0u);
v___x_2563_ = lean_array_get_size(v_xs_2558_);
lean_inc(v_toPure_2561_);
v___f_2564_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2564_, 0, v_toPure_2561_);
v___x_2565_ = lean_nat_dec_lt(v___x_2562_, v___x_2563_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_inc(v_toPure_2561_);
lean_dec_ref(v_xs_2558_);
lean_dec(v_p_2557_);
lean_dec_ref(v_inst_2556_);
v___x_2566_ = lean_box(v___x_2565_);
v___x_2567_ = lean_apply_2(v_toPure_2561_, lean_box(0), v___x_2566_);
v___x_2568_ = lean_apply_4(v_toBind_2560_, lean_box(0), lean_box(0), v___x_2567_, v___f_2564_);
return v___x_2568_;
}
else
{
if (v___x_2565_ == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_inc(v_toPure_2561_);
lean_dec_ref(v_xs_2558_);
lean_dec(v_p_2557_);
lean_dec_ref(v_inst_2556_);
v___x_2569_ = lean_box(v___x_2565_);
v___x_2570_ = lean_apply_2(v_toPure_2561_, lean_box(0), v___x_2569_);
v___x_2571_ = lean_apply_4(v_toBind_2560_, lean_box(0), lean_box(0), v___x_2570_, v___f_2564_);
return v___x_2571_;
}
else
{
lean_object* v___x_2572_; lean_object* v___f_2573_; lean_object* v___f_2574_; size_t v___x_2575_; size_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2572_ = lean_box(v___x_2565_);
lean_inc(v_toPure_2561_);
v___f_2573_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2573_, 0, v_toPure_2561_);
lean_closure_set(v___f_2573_, 1, v___x_2572_);
lean_inc(v_toBind_2560_);
v___f_2574_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2574_, 0, v_p_2557_);
lean_closure_set(v___f_2574_, 1, v_toBind_2560_);
lean_closure_set(v___f_2574_, 2, v___f_2573_);
v___x_2575_ = ((size_t)0ULL);
v___x_2576_ = lean_usize_of_nat(v___x_2563_);
v___x_2577_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2556_, v___f_2574_, v_xs_2558_, v___x_2575_, v___x_2576_);
v___x_2578_ = lean_apply_4(v_toBind_2560_, lean_box(0), lean_box(0), v___x_2577_, v___f_2564_);
return v___x_2578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___boxed(lean_object* v_m_2579_, lean_object* v_00_u03b1_2580_, lean_object* v_n_2581_, lean_object* v_inst_2582_, lean_object* v_p_2583_, lean_object* v_xs_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Vector_allM(v_m_2579_, v_00_u03b1_2580_, v_n_2581_, v_inst_2582_, v_p_2583_, v_xs_2584_);
lean_dec(v_n_2581_);
return v_res_2585_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg___lam__0(lean_object* v_p_2586_, lean_object* v_x_2587_){
_start:
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = lean_apply_1(v_p_2586_, v_x_2587_);
v___x_2589_ = lean_unbox(v___x_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___lam__0___boxed(lean_object* v_p_2590_, lean_object* v_x_2591_){
_start:
{
uint8_t v_res_2592_; lean_object* v_r_2593_; 
v_res_2592_ = l_Vector_any___redArg___lam__0(v_p_2590_, v_x_2591_);
v_r_2593_ = lean_box(v_res_2592_);
return v_r_2593_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg(lean_object* v_xs_2594_, lean_object* v_p_2595_){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2596_ = lean_unsigned_to_nat(0u);
v___x_2597_ = lean_array_get_size(v_xs_2594_);
v___x_2598_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2599_ = lean_nat_dec_lt(v___x_2596_, v___x_2597_);
if (v___x_2599_ == 0)
{
lean_dec_ref(v_p_2595_);
lean_dec_ref(v_xs_2594_);
return v___x_2599_;
}
else
{
if (v___x_2599_ == 0)
{
lean_dec_ref(v_p_2595_);
lean_dec_ref(v_xs_2594_);
return v___x_2599_;
}
else
{
lean_object* v___f_2600_; size_t v___x_2601_; size_t v___x_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___f_2600_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2600_, 0, v_p_2595_);
v___x_2601_ = ((size_t)0ULL);
v___x_2602_ = lean_usize_of_nat(v___x_2597_);
v___x_2603_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2598_, v___f_2600_, v_xs_2594_, v___x_2601_, v___x_2602_);
v___x_2604_ = lean_unbox(v___x_2603_);
lean_dec(v___x_2603_);
return v___x_2604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___boxed(lean_object* v_xs_2605_, lean_object* v_p_2606_){
_start:
{
uint8_t v_res_2607_; lean_object* v_r_2608_; 
v_res_2607_ = l_Vector_any___redArg(v_xs_2605_, v_p_2606_);
v_r_2608_ = lean_box(v_res_2607_);
return v_r_2608_;
}
}
LEAN_EXPORT uint8_t l_Vector_any(lean_object* v_00_u03b1_2609_, lean_object* v_n_2610_, lean_object* v_xs_2611_, lean_object* v_p_2612_){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2613_ = lean_unsigned_to_nat(0u);
v___x_2614_ = lean_array_get_size(v_xs_2611_);
v___x_2615_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2616_ = lean_nat_dec_lt(v___x_2613_, v___x_2614_);
if (v___x_2616_ == 0)
{
lean_dec_ref(v_p_2612_);
lean_dec_ref(v_xs_2611_);
return v___x_2616_;
}
else
{
if (v___x_2616_ == 0)
{
lean_dec_ref(v_p_2612_);
lean_dec_ref(v_xs_2611_);
return v___x_2616_;
}
else
{
lean_object* v___f_2617_; size_t v___x_2618_; size_t v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___f_2617_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2617_, 0, v_p_2612_);
v___x_2618_ = ((size_t)0ULL);
v___x_2619_ = lean_usize_of_nat(v___x_2614_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2615_, v___f_2617_, v_xs_2611_, v___x_2618_, v___x_2619_);
v___x_2621_ = lean_unbox(v___x_2620_);
lean_dec(v___x_2620_);
return v___x_2621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___boxed(lean_object* v_00_u03b1_2622_, lean_object* v_n_2623_, lean_object* v_xs_2624_, lean_object* v_p_2625_){
_start:
{
uint8_t v_res_2626_; lean_object* v_r_2627_; 
v_res_2626_ = l_Vector_any(v_00_u03b1_2622_, v_n_2623_, v_xs_2624_, v_p_2625_);
lean_dec(v_n_2623_);
v_r_2627_ = lean_box(v_res_2626_);
return v_r_2627_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg___lam__0(lean_object* v_p_2628_, uint8_t v___x_2629_, lean_object* v_v_2630_){
_start:
{
lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = lean_apply_1(v_p_2628_, v_v_2630_);
v___x_2632_ = lean_unbox(v___x_2631_);
if (v___x_2632_ == 0)
{
return v___x_2629_;
}
else
{
uint8_t v___x_2633_; 
v___x_2633_ = 0;
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___lam__0___boxed(lean_object* v_p_2634_, lean_object* v___x_2635_, lean_object* v_v_2636_){
_start:
{
uint8_t v___x_75__boxed_2637_; uint8_t v_res_2638_; lean_object* v_r_2639_; 
v___x_75__boxed_2637_ = lean_unbox(v___x_2635_);
v_res_2638_ = l_Vector_all___redArg___lam__0(v_p_2634_, v___x_75__boxed_2637_, v_v_2636_);
v_r_2639_ = lean_box(v_res_2638_);
return v_r_2639_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg(lean_object* v_xs_2640_, lean_object* v_p_2641_){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2642_ = lean_unsigned_to_nat(0u);
v___x_2643_ = lean_array_get_size(v_xs_2640_);
v___x_2644_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2645_ = lean_nat_dec_lt(v___x_2642_, v___x_2643_);
if (v___x_2645_ == 0)
{
uint8_t v___x_2646_; 
lean_dec_ref(v_p_2641_);
lean_dec_ref(v_xs_2640_);
v___x_2646_ = 1;
return v___x_2646_;
}
else
{
if (v___x_2645_ == 0)
{
lean_dec_ref(v_p_2641_);
lean_dec_ref(v_xs_2640_);
return v___x_2645_;
}
else
{
lean_object* v___x_2647_; lean_object* v___f_2648_; size_t v___x_2649_; size_t v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2647_ = lean_box(v___x_2645_);
v___f_2648_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2648_, 0, v_p_2641_);
lean_closure_set(v___f_2648_, 1, v___x_2647_);
v___x_2649_ = ((size_t)0ULL);
v___x_2650_ = lean_usize_of_nat(v___x_2643_);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2644_, v___f_2648_, v_xs_2640_, v___x_2649_, v___x_2650_);
v___x_2652_ = lean_unbox(v___x_2651_);
lean_dec(v___x_2651_);
if (v___x_2652_ == 0)
{
return v___x_2645_;
}
else
{
uint8_t v___x_2653_; 
v___x_2653_ = 0;
return v___x_2653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___boxed(lean_object* v_xs_2654_, lean_object* v_p_2655_){
_start:
{
uint8_t v_res_2656_; lean_object* v_r_2657_; 
v_res_2656_ = l_Vector_all___redArg(v_xs_2654_, v_p_2655_);
v_r_2657_ = lean_box(v_res_2656_);
return v_r_2657_;
}
}
LEAN_EXPORT uint8_t l_Vector_all(lean_object* v_00_u03b1_2658_, lean_object* v_n_2659_, lean_object* v_xs_2660_, lean_object* v_p_2661_){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_array_get_size(v_xs_2660_);
v___x_2664_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2665_ = lean_nat_dec_lt(v___x_2662_, v___x_2663_);
if (v___x_2665_ == 0)
{
uint8_t v___x_2666_; 
lean_dec_ref(v_p_2661_);
lean_dec_ref(v_xs_2660_);
v___x_2666_ = 1;
return v___x_2666_;
}
else
{
if (v___x_2665_ == 0)
{
lean_dec_ref(v_p_2661_);
lean_dec_ref(v_xs_2660_);
return v___x_2665_;
}
else
{
lean_object* v___x_2667_; lean_object* v___f_2668_; size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
v___x_2667_ = lean_box(v___x_2665_);
v___f_2668_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2668_, 0, v_p_2661_);
lean_closure_set(v___f_2668_, 1, v___x_2667_);
v___x_2669_ = ((size_t)0ULL);
v___x_2670_ = lean_usize_of_nat(v___x_2663_);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2664_, v___f_2668_, v_xs_2660_, v___x_2669_, v___x_2670_);
v___x_2672_ = lean_unbox(v___x_2671_);
lean_dec(v___x_2671_);
if (v___x_2672_ == 0)
{
return v___x_2665_;
}
else
{
uint8_t v___x_2673_; 
v___x_2673_ = 0;
return v___x_2673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___boxed(lean_object* v_00_u03b1_2674_, lean_object* v_n_2675_, lean_object* v_xs_2676_, lean_object* v_p_2677_){
_start:
{
uint8_t v_res_2678_; lean_object* v_r_2679_; 
v_res_2678_ = l_Vector_all(v_00_u03b1_2674_, v_n_2675_, v_xs_2676_, v_p_2677_);
lean_dec(v_n_2675_);
v_r_2679_ = lean_box(v_res_2678_);
return v_r_2679_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0(lean_object* v_p_2680_, lean_object* v_x1_2681_, lean_object* v_x2_2682_){
_start:
{
lean_object* v___x_2683_; uint8_t v___x_2684_; 
v___x_2683_ = lean_apply_1(v_p_2680_, v_x1_2681_);
v___x_2684_ = lean_unbox(v___x_2683_);
if (v___x_2684_ == 0)
{
lean_inc(v_x2_2682_);
return v_x2_2682_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = lean_unsigned_to_nat(1u);
v___x_2686_ = lean_nat_add(v_x2_2682_, v___x_2685_);
return v___x_2686_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0___boxed(lean_object* v_p_2687_, lean_object* v_x1_2688_, lean_object* v_x2_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Vector_countP___redArg___lam__0(v_p_2687_, v_x1_2688_, v_x2_2689_);
lean_dec(v_x2_2689_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg(lean_object* v_p_2691_, lean_object* v_xs_2692_){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2693_ = lean_unsigned_to_nat(0u);
v___x_2694_ = lean_array_get_size(v_xs_2692_);
v___x_2695_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2696_ = lean_nat_dec_lt(v___x_2693_, v___x_2694_);
if (v___x_2696_ == 0)
{
lean_dec_ref(v_xs_2692_);
lean_dec_ref(v_p_2691_);
return v___x_2693_;
}
else
{
lean_object* v___f_2697_; size_t v___x_2698_; size_t v___x_2699_; lean_object* v___x_2700_; 
v___f_2697_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2697_, 0, v_p_2691_);
v___x_2698_ = lean_usize_of_nat(v___x_2694_);
v___x_2699_ = ((size_t)0ULL);
v___x_2700_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2695_, v___f_2697_, v_xs_2692_, v___x_2698_, v___x_2699_, v___x_2693_);
return v___x_2700_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP(lean_object* v_00_u03b1_2701_, lean_object* v_n_2702_, lean_object* v_p_2703_, lean_object* v_xs_2704_){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = lean_array_get_size(v_xs_2704_);
v___x_2707_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2708_ = lean_nat_dec_lt(v___x_2705_, v___x_2706_);
if (v___x_2708_ == 0)
{
lean_dec_ref(v_xs_2704_);
lean_dec_ref(v_p_2703_);
return v___x_2705_;
}
else
{
lean_object* v___f_2709_; size_t v___x_2710_; size_t v___x_2711_; lean_object* v___x_2712_; 
v___f_2709_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2709_, 0, v_p_2703_);
v___x_2710_ = lean_usize_of_nat(v___x_2706_);
v___x_2711_ = ((size_t)0ULL);
v___x_2712_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2707_, v___f_2709_, v_xs_2704_, v___x_2710_, v___x_2711_, v___x_2705_);
return v___x_2712_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___boxed(lean_object* v_00_u03b1_2713_, lean_object* v_n_2714_, lean_object* v_p_2715_, lean_object* v_xs_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Vector_countP(v_00_u03b1_2713_, v_n_2714_, v_p_2715_, v_xs_2716_);
lean_dec(v_n_2714_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0(lean_object* v_inst_2718_, lean_object* v_a_2719_, lean_object* v_x1_2720_, lean_object* v_x2_2721_){
_start:
{
lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2722_ = lean_apply_2(v_inst_2718_, v_x1_2720_, v_a_2719_);
v___x_2723_ = lean_unbox(v___x_2722_);
if (v___x_2723_ == 0)
{
lean_inc(v_x2_2721_);
return v_x2_2721_;
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_unsigned_to_nat(1u);
v___x_2725_ = lean_nat_add(v_x2_2721_, v___x_2724_);
return v___x_2725_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0___boxed(lean_object* v_inst_2726_, lean_object* v_a_2727_, lean_object* v_x1_2728_, lean_object* v_x2_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Vector_count___redArg___lam__0(v_inst_2726_, v_a_2727_, v_x1_2728_, v_x2_2729_);
lean_dec(v_x2_2729_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg(lean_object* v_inst_2731_, lean_object* v_a_2732_, lean_object* v_xs_2733_){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2734_ = lean_unsigned_to_nat(0u);
v___x_2735_ = lean_array_get_size(v_xs_2733_);
v___x_2736_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2737_ = lean_nat_dec_lt(v___x_2734_, v___x_2735_);
if (v___x_2737_ == 0)
{
lean_dec_ref(v_xs_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_inst_2731_);
return v___x_2734_;
}
else
{
lean_object* v___f_2738_; size_t v___x_2739_; size_t v___x_2740_; lean_object* v___x_2741_; 
v___f_2738_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2738_, 0, v_inst_2731_);
lean_closure_set(v___f_2738_, 1, v_a_2732_);
v___x_2739_ = lean_usize_of_nat(v___x_2735_);
v___x_2740_ = ((size_t)0ULL);
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2736_, v___f_2738_, v_xs_2733_, v___x_2739_, v___x_2740_, v___x_2734_);
return v___x_2741_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count(lean_object* v_00_u03b1_2742_, lean_object* v_n_2743_, lean_object* v_inst_2744_, lean_object* v_a_2745_, lean_object* v_xs_2746_){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2747_ = lean_unsigned_to_nat(0u);
v___x_2748_ = lean_array_get_size(v_xs_2746_);
v___x_2749_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2750_ = lean_nat_dec_lt(v___x_2747_, v___x_2748_);
if (v___x_2750_ == 0)
{
lean_dec_ref(v_xs_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_inst_2744_);
return v___x_2747_;
}
else
{
lean_object* v___f_2751_; size_t v___x_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
v___f_2751_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2751_, 0, v_inst_2744_);
lean_closure_set(v___f_2751_, 1, v_a_2745_);
v___x_2752_ = lean_usize_of_nat(v___x_2748_);
v___x_2753_ = ((size_t)0ULL);
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2749_, v___f_2751_, v_xs_2746_, v___x_2752_, v___x_2753_, v___x_2747_);
return v___x_2754_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_n_2756_, lean_object* v_inst_2757_, lean_object* v_a_2758_, lean_object* v_xs_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Vector_count(v_00_u03b1_2755_, v_n_2756_, v_inst_2757_, v_a_2758_, v_xs_2759_);
lean_dec(v_n_2756_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___redArg(lean_object* v_inst_2761_, lean_object* v_xs_2762_, lean_object* v_a_2763_, lean_object* v_b_2764_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Array_replace___redArg(v_inst_2761_, v_xs_2762_, v_a_2763_, v_b_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace(lean_object* v_00_u03b1_2766_, lean_object* v_n_2767_, lean_object* v_inst_2768_, lean_object* v_xs_2769_, lean_object* v_a_2770_, lean_object* v_b_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Array_replace___redArg(v_inst_2768_, v_xs_2769_, v_a_2770_, v_b_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___boxed(lean_object* v_00_u03b1_2773_, lean_object* v_n_2774_, lean_object* v_inst_2775_, lean_object* v_xs_2776_, lean_object* v_a_2777_, lean_object* v_b_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Vector_replace(v_00_u03b1_2773_, v_n_2774_, v_inst_2775_, v_xs_2776_, v_a_2777_, v_b_2778_);
lean_dec(v_n_2774_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg___lam__0(lean_object* v_inst_2780_, lean_object* v_x1_2781_, lean_object* v_x2_2782_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_apply_2(v_inst_2780_, v_x1_2781_, v_x2_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg(lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_xs_2786_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2787_ = lean_array_get_size(v_xs_2786_);
v___x_2788_ = lean_unsigned_to_nat(0u);
v___x_2789_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2790_ = lean_nat_dec_lt(v___x_2788_, v___x_2787_);
if (v___x_2790_ == 0)
{
lean_dec_ref(v_xs_2786_);
lean_dec(v_inst_2784_);
return v_inst_2785_;
}
else
{
lean_object* v___f_2791_; size_t v___x_2792_; size_t v___x_2793_; lean_object* v___x_2794_; 
v___f_2791_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2791_, 0, v_inst_2784_);
v___x_2792_ = lean_usize_of_nat(v___x_2787_);
v___x_2793_ = ((size_t)0ULL);
v___x_2794_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2789_, v___f_2791_, v_xs_2786_, v___x_2792_, v___x_2793_, v_inst_2785_);
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum(lean_object* v_00_u03b1_2795_, lean_object* v_n_2796_, lean_object* v_inst_2797_, lean_object* v_inst_2798_, lean_object* v_xs_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2800_ = lean_array_get_size(v_xs_2799_);
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2803_ = lean_nat_dec_lt(v___x_2801_, v___x_2800_);
if (v___x_2803_ == 0)
{
lean_dec_ref(v_xs_2799_);
lean_dec(v_inst_2797_);
return v_inst_2798_;
}
else
{
lean_object* v___f_2804_; size_t v___x_2805_; size_t v___x_2806_; lean_object* v___x_2807_; 
v___f_2804_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2804_, 0, v_inst_2797_);
v___x_2805_ = lean_usize_of_nat(v___x_2800_);
v___x_2806_ = ((size_t)0ULL);
v___x_2807_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2802_, v___f_2804_, v_xs_2799_, v___x_2805_, v___x_2806_, v_inst_2798_);
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum___boxed(lean_object* v_00_u03b1_2808_, lean_object* v_n_2809_, lean_object* v_inst_2810_, lean_object* v_inst_2811_, lean_object* v_xs_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Vector_sum(v_00_u03b1_2808_, v_n_2809_, v_inst_2810_, v_inst_2811_, v_xs_2812_);
lean_dec(v_n_2809_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Vector_prod___redArg(lean_object* v_inst_2814_, lean_object* v_inst_2815_, lean_object* v_xs_2816_){
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
LEAN_EXPORT lean_object* l_Vector_prod(lean_object* v_00_u03b1_2825_, lean_object* v_n_2826_, lean_object* v_inst_2827_, lean_object* v_inst_2828_, lean_object* v_xs_2829_){
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
LEAN_EXPORT lean_object* l_Vector_prod___boxed(lean_object* v_00_u03b1_2838_, lean_object* v_n_2839_, lean_object* v_inst_2840_, lean_object* v_inst_2841_, lean_object* v_xs_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Vector_prod(v_00_u03b1_2838_, v_n_2839_, v_inst_2840_, v_inst_2841_, v_xs_2842_);
lean_dec(v_n_2839_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg(lean_object* v_m_2844_, lean_object* v_n_2845_, lean_object* v_a_2846_, lean_object* v_xs_2847_){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_nat_sub(v_n_2845_, v_m_2844_);
v___x_2849_ = lean_mk_array(v___x_2848_, v_a_2846_);
v___x_2850_ = l_Array_append___redArg(v___x_2849_, v_xs_2847_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg___boxed(lean_object* v_m_2851_, lean_object* v_n_2852_, lean_object* v_a_2853_, lean_object* v_xs_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Vector_leftpad___redArg(v_m_2851_, v_n_2852_, v_a_2853_, v_xs_2854_);
lean_dec_ref(v_xs_2854_);
lean_dec(v_n_2852_);
lean_dec(v_m_2851_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad(lean_object* v_00_u03b1_2856_, lean_object* v_m_2857_, lean_object* v_n_2858_, lean_object* v_a_2859_, lean_object* v_xs_2860_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = lean_nat_sub(v_n_2858_, v_m_2857_);
v___x_2862_ = lean_mk_array(v___x_2861_, v_a_2859_);
v___x_2863_ = l_Array_append___redArg(v___x_2862_, v_xs_2860_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___boxed(lean_object* v_00_u03b1_2864_, lean_object* v_m_2865_, lean_object* v_n_2866_, lean_object* v_a_2867_, lean_object* v_xs_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Vector_leftpad(v_00_u03b1_2864_, v_m_2865_, v_n_2866_, v_a_2867_, v_xs_2868_);
lean_dec_ref(v_xs_2868_);
lean_dec(v_n_2866_);
lean_dec(v_m_2865_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg(lean_object* v_m_2870_, lean_object* v_n_2871_, lean_object* v_a_2872_, lean_object* v_xs_2873_){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_nat_sub(v_n_2871_, v_m_2870_);
v___x_2875_ = lean_mk_array(v___x_2874_, v_a_2872_);
v___x_2876_ = l_Array_append___redArg(v_xs_2873_, v___x_2875_);
lean_dec_ref(v___x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg___boxed(lean_object* v_m_2877_, lean_object* v_n_2878_, lean_object* v_a_2879_, lean_object* v_xs_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Vector_rightpad___redArg(v_m_2877_, v_n_2878_, v_a_2879_, v_xs_2880_);
lean_dec(v_n_2878_);
lean_dec(v_m_2877_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad(lean_object* v_00_u03b1_2882_, lean_object* v_m_2883_, lean_object* v_n_2884_, lean_object* v_a_2885_, lean_object* v_xs_2886_){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2887_ = lean_nat_sub(v_n_2884_, v_m_2883_);
v___x_2888_ = lean_mk_array(v___x_2887_, v_a_2885_);
v___x_2889_ = l_Array_append___redArg(v_xs_2886_, v___x_2888_);
lean_dec_ref(v___x_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___boxed(lean_object* v_00_u03b1_2890_, lean_object* v_m_2891_, lean_object* v_n_2892_, lean_object* v_a_2893_, lean_object* v_xs_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Vector_rightpad(v_00_u03b1_2890_, v_m_2891_, v_n_2892_, v_a_2893_, v_xs_2894_);
lean_dec(v_n_2892_);
lean_dec(v_m_2891_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_f_2896_, lean_object* v_a_2897_, lean_object* v_h_2898_, lean_object* v_b_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_apply_3(v_f_2896_, v_a_2897_, lean_box(0), v_b_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_inst_2901_, lean_object* v_00_u03b2_2902_, lean_object* v_xs_2903_, lean_object* v_b_2904_, lean_object* v_f_2905_){
_start:
{
lean_object* v___f_2906_; size_t v_sz_2907_; size_t v___x_2908_; lean_object* v___x_2909_; 
v___f_2906_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2906_, 0, v_f_2905_);
v_sz_2907_ = lean_array_size(v_xs_2903_);
v___x_2908_ = ((size_t)0ULL);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2901_, v_xs_2903_, v___f_2906_, v_sz_2907_, v___x_2908_, v_b_2904_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_2910_){
_start:
{
lean_object* v___f_2911_; 
v___f_2911_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2911_, 0, v_inst_2910_);
return v___f_2911_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_2912_, lean_object* v_00_u03b1_2913_, lean_object* v_n_2914_, lean_object* v_inst_2915_){
_start:
{
lean_object* v___f_2916_; 
v___f_2916_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2916_, 0, v_inst_2915_);
return v___f_2916_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(lean_object* v_m_2917_, lean_object* v_00_u03b1_2918_, lean_object* v_n_2919_, lean_object* v_inst_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Vector_instForIn_x27InferInstanceMembershipOfMonad(v_m_2917_, v_00_u03b1_2918_, v_n_2919_, v_inst_2920_);
lean_dec(v_n_2919_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad___redArg(lean_object* v_n_2922_, lean_object* v_inst_2923_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2924_, 0, lean_box(0));
lean_closure_set(v___x_2924_, 1, lean_box(0));
lean_closure_set(v___x_2924_, 2, v_n_2922_);
lean_closure_set(v___x_2924_, 3, v_inst_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad(lean_object* v_m_2925_, lean_object* v_00_u03b1_2926_, lean_object* v_n_2927_, lean_object* v_inst_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2929_, 0, lean_box(0));
lean_closure_set(v___x_2929_, 1, lean_box(0));
lean_closure_set(v___x_2929_, 2, v_n_2927_);
lean_closure_set(v___x_2929_, 3, v_inst_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object* v_00_u03b1_2930_, lean_object* v_n_2931_, lean_object* v_inst_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_box(0);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object* v_00_u03b1_2934_, lean_object* v_n_2935_, lean_object* v_inst_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Vector_instLT(v_00_u03b1_2934_, v_n_2935_, v_inst_2936_);
lean_dec(v_n_2935_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE(lean_object* v_00_u03b1_2938_, lean_object* v_n_2939_, lean_object* v_inst_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = lean_box(0);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___boxed(lean_object* v_00_u03b1_2942_, lean_object* v_n_2943_, lean_object* v_inst_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Vector_instLE(v_00_u03b1_2942_, v_n_2943_, v_inst_2944_);
lean_dec(v_n_2943_);
return v_res_2945_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__2(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = ((lean_object*)(l_Vector_lex___auto__1___closed__0));
v___x_2953_ = l_Lean_mkAtom(v___x_2952_);
return v___x_2953_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__3(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = lean_obj_once(&l_Vector_lex___auto__1___closed__2, &l_Vector_lex___auto__1___closed__2_once, _init_l_Vector_lex___auto__1___closed__2);
v___x_2955_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_2956_ = lean_array_push(v___x_2955_, v___x_2954_);
return v___x_2956_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_2970_ = l_Lean_mkAtom(v___x_2969_);
return v___x_2970_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = lean_obj_once(&l_Vector_lex___auto__1___closed__8, &l_Vector_lex___auto__1___closed__8_once, _init_l_Vector_lex___auto__1___closed__8);
v___x_2972_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_2973_ = lean_array_push(v___x_2972_, v___x_2971_);
return v___x_2973_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_2979_ = lean_string_utf8_byte_size(v___x_2978_);
return v___x_2979_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2980_ = lean_obj_once(&l_Vector_lex___auto__1___closed__13, &l_Vector_lex___auto__1___closed__13_once, _init_l_Vector_lex___auto__1___closed__13);
v___x_2981_ = lean_unsigned_to_nat(0u);
v___x_2982_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_2983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
lean_ctor_set(v___x_2983_, 1, v___x_2981_);
lean_ctor_set(v___x_2983_, 2, v___x_2980_);
return v___x_2983_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_box(0);
v___x_2986_ = lean_obj_once(&l_Vector_lex___auto__1___closed__14, &l_Vector_lex___auto__1___closed__14_once, _init_l_Vector_lex___auto__1___closed__14);
v___x_2987_ = lean_box(2);
v___x_2988_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v___x_2986_);
lean_ctor_set(v___x_2988_, 2, v___x_2985_);
lean_ctor_set(v___x_2988_, 3, v___x_2984_);
return v___x_2988_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = lean_obj_once(&l_Vector_lex___auto__1___closed__15, &l_Vector_lex___auto__1___closed__15_once, _init_l_Vector_lex___auto__1___closed__15);
v___x_2990_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_2991_ = lean_array_push(v___x_2990_, v___x_2989_);
return v___x_2991_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2992_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_2993_ = ((lean_object*)(l_Vector_lex___auto__1___closed__11));
v___x_2994_ = lean_box(2);
v___x_2995_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
lean_ctor_set(v___x_2995_, 1, v___x_2993_);
lean_ctor_set(v___x_2995_, 2, v___x_2992_);
return v___x_2995_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_2997_ = lean_obj_once(&l_Vector_lex___auto__1___closed__9, &l_Vector_lex___auto__1___closed__9_once, _init_l_Vector_lex___auto__1___closed__9);
v___x_2998_ = lean_array_push(v___x_2997_, v___x_2996_);
return v___x_2998_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2999_ = lean_obj_once(&l_Vector_lex___auto__1___closed__18, &l_Vector_lex___auto__1___closed__18_once, _init_l_Vector_lex___auto__1___closed__18);
v___x_3000_ = ((lean_object*)(l_Vector_lex___auto__1___closed__7));
v___x_3001_ = lean_box(2);
v___x_3002_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
lean_ctor_set(v___x_3002_, 1, v___x_3000_);
lean_ctor_set(v___x_3002_, 2, v___x_2999_);
return v___x_3002_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3003_ = lean_obj_once(&l_Vector_lex___auto__1___closed__19, &l_Vector_lex___auto__1___closed__19_once, _init_l_Vector_lex___auto__1___closed__19);
v___x_3004_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3005_ = lean_array_push(v___x_3004_, v___x_3003_);
return v___x_3005_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = ((lean_object*)(l_Vector_lex___auto__1___closed__25));
v___x_3017_ = l_Lean_mkAtom(v___x_3016_);
return v___x_3017_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = lean_obj_once(&l_Vector_lex___auto__1___closed__26, &l_Vector_lex___auto__1___closed__26_once, _init_l_Vector_lex___auto__1___closed__26);
v___x_3019_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3020_ = lean_array_push(v___x_3019_, v___x_3018_);
return v___x_3020_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3022_ = lean_obj_once(&l_Vector_lex___auto__1___closed__27, &l_Vector_lex___auto__1___closed__27_once, _init_l_Vector_lex___auto__1___closed__27);
v___x_3023_ = lean_array_push(v___x_3022_, v___x_3021_);
return v___x_3023_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3024_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3025_ = ((lean_object*)(l_Vector_lex___auto__1___closed__24));
v___x_3026_ = lean_box(2);
v___x_3027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set(v___x_3027_, 1, v___x_3025_);
lean_ctor_set(v___x_3027_, 2, v___x_3024_);
return v___x_3027_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3028_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3029_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3030_ = lean_array_push(v___x_3029_, v___x_3028_);
return v___x_3030_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = ((lean_object*)(l_Vector_lex___auto__1___closed__31));
v___x_3033_ = l_Lean_mkAtom(v___x_3032_);
return v___x_3033_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__33(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = lean_obj_once(&l_Vector_lex___auto__1___closed__32, &l_Vector_lex___auto__1___closed__32_once, _init_l_Vector_lex___auto__1___closed__32);
v___x_3035_ = lean_obj_once(&l_Vector_lex___auto__1___closed__30, &l_Vector_lex___auto__1___closed__30_once, _init_l_Vector_lex___auto__1___closed__30);
v___x_3036_ = lean_array_push(v___x_3035_, v___x_3034_);
return v___x_3036_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__34(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3037_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3038_ = lean_obj_once(&l_Vector_lex___auto__1___closed__33, &l_Vector_lex___auto__1___closed__33_once, _init_l_Vector_lex___auto__1___closed__33);
v___x_3039_ = lean_array_push(v___x_3038_, v___x_3037_);
return v___x_3039_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__35(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3040_ = lean_obj_once(&l_Vector_lex___auto__1___closed__34, &l_Vector_lex___auto__1___closed__34_once, _init_l_Vector_lex___auto__1___closed__34);
v___x_3041_ = ((lean_object*)(l_Vector_lex___auto__1___closed__22));
v___x_3042_ = lean_box(2);
v___x_3043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
lean_ctor_set(v___x_3043_, 1, v___x_3041_);
lean_ctor_set(v___x_3043_, 2, v___x_3040_);
return v___x_3043_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__36(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = lean_obj_once(&l_Vector_lex___auto__1___closed__35, &l_Vector_lex___auto__1___closed__35_once, _init_l_Vector_lex___auto__1___closed__35);
v___x_3045_ = lean_obj_once(&l_Vector_lex___auto__1___closed__20, &l_Vector_lex___auto__1___closed__20_once, _init_l_Vector_lex___auto__1___closed__20);
v___x_3046_ = lean_array_push(v___x_3045_, v___x_3044_);
return v___x_3046_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_3048_ = l_Lean_mkAtom(v___x_3047_);
return v___x_3048_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = lean_obj_once(&l_Vector_lex___auto__1___closed__37, &l_Vector_lex___auto__1___closed__37_once, _init_l_Vector_lex___auto__1___closed__37);
v___x_3050_ = lean_obj_once(&l_Vector_lex___auto__1___closed__36, &l_Vector_lex___auto__1___closed__36_once, _init_l_Vector_lex___auto__1___closed__36);
v___x_3051_ = lean_array_push(v___x_3050_, v___x_3049_);
return v___x_3051_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3052_ = lean_obj_once(&l_Vector_lex___auto__1___closed__38, &l_Vector_lex___auto__1___closed__38_once, _init_l_Vector_lex___auto__1___closed__38);
v___x_3053_ = ((lean_object*)(l_Vector_lex___auto__1___closed__5));
v___x_3054_ = lean_box(2);
v___x_3055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___x_3053_);
lean_ctor_set(v___x_3055_, 2, v___x_3052_);
return v___x_3055_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = lean_obj_once(&l_Vector_lex___auto__1___closed__39, &l_Vector_lex___auto__1___closed__39_once, _init_l_Vector_lex___auto__1___closed__39);
v___x_3057_ = lean_obj_once(&l_Vector_lex___auto__1___closed__3, &l_Vector_lex___auto__1___closed__3_once, _init_l_Vector_lex___auto__1___closed__3);
v___x_3058_ = lean_array_push(v___x_3057_, v___x_3056_);
return v___x_3058_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3059_ = lean_obj_once(&l_Vector_lex___auto__1___closed__40, &l_Vector_lex___auto__1___closed__40_once, _init_l_Vector_lex___auto__1___closed__40);
v___x_3060_ = ((lean_object*)(l_Vector_lex___auto__1___closed__1));
v___x_3061_ = lean_box(2);
v___x_3062_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
lean_ctor_set(v___x_3062_, 1, v___x_3060_);
lean_ctor_set(v___x_3062_, 2, v___x_3059_);
return v___x_3062_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = lean_obj_once(&l_Vector_lex___auto__1___closed__41, &l_Vector_lex___auto__1___closed__41_once, _init_l_Vector_lex___auto__1___closed__41);
v___x_3064_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3065_ = lean_array_push(v___x_3064_, v___x_3063_);
return v___x_3065_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3066_ = lean_obj_once(&l_Vector_lex___auto__1___closed__42, &l_Vector_lex___auto__1___closed__42_once, _init_l_Vector_lex___auto__1___closed__42);
v___x_3067_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_3068_ = lean_box(2);
v___x_3069_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
lean_ctor_set(v___x_3069_, 1, v___x_3067_);
lean_ctor_set(v___x_3069_, 2, v___x_3066_);
return v___x_3069_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = lean_obj_once(&l_Vector_lex___auto__1___closed__43, &l_Vector_lex___auto__1___closed__43_once, _init_l_Vector_lex___auto__1___closed__43);
v___x_3071_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3072_ = lean_array_push(v___x_3071_, v___x_3070_);
return v___x_3072_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3073_ = lean_obj_once(&l_Vector_lex___auto__1___closed__44, &l_Vector_lex___auto__1___closed__44_once, _init_l_Vector_lex___auto__1___closed__44);
v___x_3074_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_3075_ = lean_box(2);
v___x_3076_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v___x_3074_);
lean_ctor_set(v___x_3076_, 2, v___x_3073_);
return v___x_3076_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = lean_obj_once(&l_Vector_lex___auto__1___closed__45, &l_Vector_lex___auto__1___closed__45_once, _init_l_Vector_lex___auto__1___closed__45);
v___x_3078_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3079_ = lean_array_push(v___x_3078_, v___x_3077_);
return v___x_3079_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3080_ = lean_obj_once(&l_Vector_lex___auto__1___closed__46, &l_Vector_lex___auto__1___closed__46_once, _init_l_Vector_lex___auto__1___closed__46);
v___x_3081_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_3082_ = lean_box(2);
v___x_3083_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set(v___x_3083_, 1, v___x_3081_);
lean_ctor_set(v___x_3083_, 2, v___x_3080_);
return v___x_3083_;
}
}
static lean_object* _init_l_Vector_lex___auto__1(void){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = lean_obj_once(&l_Vector_lex___auto__1___closed__47, &l_Vector_lex___auto__1___closed__47_once, _init_l_Vector_lex___auto__1___closed__47);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0(lean_object* v_n_3085_, lean_object* v_xs_3086_, lean_object* v_ys_3087_, lean_object* v_lt_3088_, lean_object* v_inst_3089_, lean_object* v___x_3090_, lean_object* v___x_3091_, lean_object* v_next_3092_, lean_object* v_acc_3093_, lean_object* v_h_3094_, lean_object* v_G_3095_){
_start:
{
uint8_t v___x_3096_; 
v___x_3096_ = lean_nat_dec_lt(v_next_3092_, v_n_3085_);
if (v___x_3096_ == 0)
{
lean_dec_ref(v_G_3095_);
lean_dec_ref(v___x_3091_);
lean_dec_ref(v_inst_3089_);
lean_dec_ref(v_lt_3088_);
lean_inc_ref(v_acc_3093_);
return v_acc_3093_;
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3097_ = lean_array_fget_borrowed(v_xs_3086_, v_next_3092_);
v___x_3098_ = lean_array_fget_borrowed(v_ys_3087_, v_next_3092_);
lean_inc(v___x_3098_);
lean_inc(v___x_3097_);
v___x_3099_ = lean_apply_2(v_lt_3088_, v___x_3097_, v___x_3098_);
v___x_3100_ = lean_unbox(v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; uint8_t v___x_3102_; 
lean_inc(v___x_3098_);
lean_inc(v___x_3097_);
v___x_3101_ = lean_apply_2(v_inst_3089_, v___x_3097_, v___x_3098_);
v___x_3102_ = lean_unbox(v___x_3101_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
lean_dec_ref(v_G_3095_);
lean_dec_ref(v___x_3091_);
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3099_);
v___x_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
lean_ctor_set(v___x_3104_, 1, v___x_3090_);
return v___x_3104_;
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = lean_unsigned_to_nat(1u);
v___x_3106_ = lean_nat_add(v_next_3092_, v___x_3105_);
v___x_3107_ = lean_apply_4(v_G_3095_, v___x_3106_, v___x_3091_, lean_box(0), lean_box(0));
return v___x_3107_;
}
}
else
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
lean_dec_ref(v_G_3095_);
lean_dec_ref(v___x_3091_);
lean_dec_ref(v_inst_3089_);
v___x_3108_ = lean_box(v___x_3096_);
v___x_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
v___x_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
lean_ctor_set(v___x_3110_, 1, v___x_3090_);
return v___x_3110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0___boxed(lean_object* v_n_3111_, lean_object* v_xs_3112_, lean_object* v_ys_3113_, lean_object* v_lt_3114_, lean_object* v_inst_3115_, lean_object* v___x_3116_, lean_object* v___x_3117_, lean_object* v_next_3118_, lean_object* v_acc_3119_, lean_object* v_h_3120_, lean_object* v_G_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Vector_lex___redArg___lam__0(v_n_3111_, v_xs_3112_, v_ys_3113_, v_lt_3114_, v_inst_3115_, v___x_3116_, v___x_3117_, v_next_3118_, v_acc_3119_, v_h_3120_, v_G_3121_);
lean_dec_ref(v_acc_3119_);
lean_dec(v_next_3118_);
lean_dec_ref(v_ys_3113_);
lean_dec_ref(v_xs_3112_);
lean_dec(v_n_3111_);
return v_res_3122_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object* v_n_3126_, lean_object* v_inst_3127_, lean_object* v_xs_3128_, lean_object* v_ys_3129_, lean_object* v_lt_3130_){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___f_3134_; lean_object* v___x_3135_; lean_object* v_fst_3136_; 
v___x_3131_ = lean_unsigned_to_nat(0u);
v___x_3132_ = lean_box(0);
v___x_3133_ = ((lean_object*)(l_Vector_lex___redArg___closed__0));
v___f_3134_ = lean_alloc_closure((void*)(l_Vector_lex___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_3134_, 0, v_n_3126_);
lean_closure_set(v___f_3134_, 1, v_xs_3128_);
lean_closure_set(v___f_3134_, 2, v_ys_3129_);
lean_closure_set(v___f_3134_, 3, v_lt_3130_);
lean_closure_set(v___f_3134_, 4, v_inst_3127_);
lean_closure_set(v___f_3134_, 5, v___x_3132_);
lean_closure_set(v___f_3134_, 6, v___x_3133_);
v___x_3135_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3134_, v___x_3131_, v___x_3133_, lean_box(0));
v_fst_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_fst_3136_);
lean_dec(v___x_3135_);
if (lean_obj_tag(v_fst_3136_) == 0)
{
uint8_t v___x_3137_; 
v___x_3137_ = 0;
return v___x_3137_;
}
else
{
lean_object* v_val_3138_; uint8_t v___x_3139_; 
v_val_3138_ = lean_ctor_get(v_fst_3136_, 0);
lean_inc(v_val_3138_);
lean_dec_ref_known(v_fst_3136_, 1);
v___x_3139_ = lean_unbox(v_val_3138_);
lean_dec(v_val_3138_);
return v___x_3139_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object* v_n_3140_, lean_object* v_inst_3141_, lean_object* v_xs_3142_, lean_object* v_ys_3143_, lean_object* v_lt_3144_){
_start:
{
uint8_t v_res_3145_; lean_object* v_r_3146_; 
v_res_3145_ = l_Vector_lex___redArg(v_n_3140_, v_inst_3141_, v_xs_3142_, v_ys_3143_, v_lt_3144_);
v_r_3146_ = lean_box(v_res_3145_);
return v_r_3146_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex(lean_object* v_00_u03b1_3147_, lean_object* v_n_3148_, lean_object* v_inst_3149_, lean_object* v_xs_3150_, lean_object* v_ys_3151_, lean_object* v_lt_3152_){
_start:
{
uint8_t v___x_3153_; 
v___x_3153_ = l_Vector_lex___redArg(v_n_3148_, v_inst_3149_, v_xs_3150_, v_ys_3151_, v_lt_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object* v_00_u03b1_3154_, lean_object* v_n_3155_, lean_object* v_inst_3156_, lean_object* v_xs_3157_, lean_object* v_ys_3158_, lean_object* v_lt_3159_){
_start:
{
uint8_t v_res_3160_; lean_object* v_r_3161_; 
v_res_3160_ = l_Vector_lex(v_00_u03b1_3154_, v_n_3155_, v_inst_3156_, v_xs_3157_, v_ys_3158_, v_lt_3159_);
v_r_3161_ = lean_box(v_res_3160_);
return v_r_3161_;
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
