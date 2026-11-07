// Lean compiler output
// Module: Init.Data.Vector.Basic
// Imports: import Init.Data.Array.Nat public import Init.Data.Array.DecidableEq import Init.Data.Array.InsertIdx import Init.Data.Array.MapIdx import Init.Omega
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_mark_linear(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Vector_modify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_modify___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_modify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Vector_Basic_0__Vector_lex_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_lex_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Vector_modify___redArg(lean_object* v_xs_726_, lean_object* v_i_727_, lean_object* v_f_728_){
_start:
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = lean_array_get_size(v_xs_726_);
v___x_730_ = lean_nat_dec_lt(v_i_727_, v___x_729_);
if (v___x_730_ == 0)
{
lean_dec(v_f_728_);
return v_xs_726_;
}
else
{
lean_object* v_v_731_; lean_object* v___x_732_; lean_object* v_xs_x27_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_v_731_ = lean_array_fget(v_xs_726_, v_i_727_);
v___x_732_ = lean_box(0);
v_xs_x27_733_ = lean_array_fset(v_xs_726_, v_i_727_, v___x_732_);
v___x_734_ = lean_apply_1(v_f_728_, v_v_731_);
v___x_735_ = lean_array_fset(v_xs_x27_733_, v_i_727_, v___x_734_);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_modify___redArg___boxed(lean_object* v_xs_736_, lean_object* v_i_737_, lean_object* v_f_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Vector_modify___redArg(v_xs_736_, v_i_737_, v_f_738_);
lean_dec(v_i_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Vector_modify(lean_object* v_00_u03b1_740_, lean_object* v_n_741_, lean_object* v_xs_742_, lean_object* v_i_743_, lean_object* v_f_744_){
_start:
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_array_get_size(v_xs_742_);
v___x_746_ = lean_nat_dec_lt(v_i_743_, v___x_745_);
if (v___x_746_ == 0)
{
lean_dec(v_f_744_);
return v_xs_742_;
}
else
{
lean_object* v_v_747_; lean_object* v___x_748_; lean_object* v_xs_x27_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_v_747_ = lean_array_fget(v_xs_742_, v_i_743_);
v___x_748_ = lean_box(0);
v_xs_x27_749_ = lean_array_fset(v_xs_742_, v_i_743_, v___x_748_);
v___x_750_ = lean_apply_1(v_f_744_, v_v_747_);
v___x_751_ = lean_array_fset(v_xs_x27_749_, v_i_743_, v___x_750_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_modify___boxed(lean_object* v_00_u03b1_752_, lean_object* v_n_753_, lean_object* v_xs_754_, lean_object* v_i_755_, lean_object* v_f_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Vector_modify(v_00_u03b1_752_, v_n_753_, v_xs_754_, v_i_755_, v_f_756_);
lean_dec(v_i_755_);
lean_dec(v_n_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg(lean_object* v_xs_758_, lean_object* v_i_759_, lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = lean_array_get_size(v_xs_758_);
v___x_762_ = lean_nat_dec_lt(v_i_759_, v___x_761_);
if (v___x_762_ == 0)
{
lean_dec(v_x_760_);
return v_xs_758_;
}
else
{
lean_object* v___x_763_; 
v___x_763_ = lean_array_fset(v_xs_758_, v_i_759_, v_x_760_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg___boxed(lean_object* v_xs_764_, lean_object* v_i_765_, lean_object* v_x_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Vector_setIfInBounds___redArg(v_xs_764_, v_i_765_, v_x_766_);
lean_dec(v_i_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds(lean_object* v_00_u03b1_768_, lean_object* v_n_769_, lean_object* v_xs_770_, lean_object* v_i_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = lean_array_get_size(v_xs_770_);
v___x_774_ = lean_nat_dec_lt(v_i_771_, v___x_773_);
if (v___x_774_ == 0)
{
lean_dec(v_x_772_);
return v_xs_770_;
}
else
{
lean_object* v___x_775_; 
v___x_775_ = lean_array_fset(v_xs_770_, v_i_771_, v_x_772_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___boxed(lean_object* v_00_u03b1_776_, lean_object* v_n_777_, lean_object* v_xs_778_, lean_object* v_i_779_, lean_object* v_x_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Vector_setIfInBounds(v_00_u03b1_776_, v_n_777_, v_xs_778_, v_i_779_, v_x_780_);
lean_dec(v_i_779_);
lean_dec(v_n_777_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg(lean_object* v_xs_782_, lean_object* v_i_783_, lean_object* v_x_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = lean_array_set(v_xs_782_, v_i_783_, v_x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg___boxed(lean_object* v_xs_786_, lean_object* v_i_787_, lean_object* v_x_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Vector_set_x21___redArg(v_xs_786_, v_i_787_, v_x_788_);
lean_dec(v_i_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21(lean_object* v_00_u03b1_790_, lean_object* v_n_791_, lean_object* v_xs_792_, lean_object* v_i_793_, lean_object* v_x_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = lean_array_set(v_xs_792_, v_i_793_, v_x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___boxed(lean_object* v_00_u03b1_796_, lean_object* v_n_797_, lean_object* v_xs_798_, lean_object* v_i_799_, lean_object* v_x_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Vector_set_x21(v_00_u03b1_796_, v_n_797_, v_xs_798_, v_i_799_, v_x_800_);
lean_dec(v_i_799_);
lean_dec(v_n_797_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___redArg(lean_object* v_inst_802_, lean_object* v_f_803_, lean_object* v_b_804_, lean_object* v_xs_805_){
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
size_t v___x_812_; size_t v___x_813_; lean_object* v___x_814_; 
v___x_812_ = ((size_t)0ULL);
v___x_813_ = lean_usize_of_nat(v___x_809_);
v___x_814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_802_, v_f_803_, v_xs_805_, v___x_812_, v___x_813_, v_b_804_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM(lean_object* v_m_815_, lean_object* v_00_u03b2_816_, lean_object* v_00_u03b1_817_, lean_object* v_n_818_, lean_object* v_inst_819_, lean_object* v_f_820_, lean_object* v_b_821_, lean_object* v_xs_822_){
_start:
{
lean_object* v_toApplicative_823_; lean_object* v_toPure_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_toApplicative_823_ = lean_ctor_get(v_inst_819_, 0);
v_toPure_824_ = lean_ctor_get(v_toApplicative_823_, 1);
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_array_get_size(v_xs_822_);
v___x_827_ = lean_nat_dec_lt(v___x_825_, v___x_826_);
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
v___x_829_ = ((size_t)0ULL);
v___x_830_ = lean_usize_of_nat(v___x_826_);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_819_, v_f_820_, v_xs_822_, v___x_829_, v___x_830_, v_b_821_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___boxed(lean_object* v_m_832_, lean_object* v_00_u03b2_833_, lean_object* v_00_u03b1_834_, lean_object* v_n_835_, lean_object* v_inst_836_, lean_object* v_f_837_, lean_object* v_b_838_, lean_object* v_xs_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Vector_foldlM(v_m_832_, v_00_u03b2_833_, v_00_u03b1_834_, v_n_835_, v_inst_836_, v_f_837_, v_b_838_, v_xs_839_);
lean_dec(v_n_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___redArg(lean_object* v_inst_841_, lean_object* v_f_842_, lean_object* v_b_843_, lean_object* v_xs_844_){
_start:
{
lean_object* v_toApplicative_845_; lean_object* v_toPure_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_toApplicative_845_ = lean_ctor_get(v_inst_841_, 0);
v_toPure_846_ = lean_ctor_get(v_toApplicative_845_, 1);
v___x_847_ = lean_array_get_size(v_xs_844_);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_nat_dec_lt(v___x_848_, v___x_847_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_inc(v_toPure_846_);
lean_dec_ref(v_xs_844_);
lean_dec(v_f_842_);
lean_dec_ref(v_inst_841_);
v___x_850_ = lean_apply_2(v_toPure_846_, lean_box(0), v_b_843_);
return v___x_850_;
}
else
{
size_t v___x_851_; size_t v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_usize_of_nat(v___x_847_);
v___x_852_ = ((size_t)0ULL);
v___x_853_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_841_, v_f_842_, v_xs_844_, v___x_851_, v___x_852_, v_b_843_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM(lean_object* v_m_854_, lean_object* v_00_u03b1_855_, lean_object* v_00_u03b2_856_, lean_object* v_n_857_, lean_object* v_inst_858_, lean_object* v_f_859_, lean_object* v_b_860_, lean_object* v_xs_861_){
_start:
{
lean_object* v_toApplicative_862_; lean_object* v_toPure_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_toApplicative_862_ = lean_ctor_get(v_inst_858_, 0);
v_toPure_863_ = lean_ctor_get(v_toApplicative_862_, 1);
v___x_864_ = lean_array_get_size(v_xs_861_);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_nat_dec_lt(v___x_865_, v___x_864_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_inc(v_toPure_863_);
lean_dec_ref(v_xs_861_);
lean_dec(v_f_859_);
lean_dec_ref(v_inst_858_);
v___x_867_ = lean_apply_2(v_toPure_863_, lean_box(0), v_b_860_);
return v___x_867_;
}
else
{
size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; 
v___x_868_ = lean_usize_of_nat(v___x_864_);
v___x_869_ = ((size_t)0ULL);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_858_, v_f_859_, v_xs_861_, v___x_868_, v___x_869_, v_b_860_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___boxed(lean_object* v_m_871_, lean_object* v_00_u03b1_872_, lean_object* v_00_u03b2_873_, lean_object* v_n_874_, lean_object* v_inst_875_, lean_object* v_f_876_, lean_object* v_b_877_, lean_object* v_xs_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Vector_foldrM(v_m_871_, v_00_u03b1_872_, v_00_u03b2_873_, v_n_874_, v_inst_875_, v_f_876_, v_b_877_, v_xs_878_);
lean_dec(v_n_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg___lam__0(lean_object* v_f_880_, lean_object* v_x1_881_, lean_object* v_x2_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lean_apply_2(v_f_880_, v_x1_881_, v_x2_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg(lean_object* v_f_903_, lean_object* v_b_904_, lean_object* v_xs_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_array_get_size(v_xs_905_);
v___x_908_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_909_ = lean_nat_dec_lt(v___x_906_, v___x_907_);
if (v___x_909_ == 0)
{
lean_dec_ref(v_xs_905_);
lean_dec(v_f_903_);
return v_b_904_;
}
else
{
lean_object* v___f_910_; size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v___f_910_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_910_, 0, v_f_903_);
v___x_911_ = ((size_t)0ULL);
v___x_912_ = lean_usize_of_nat(v___x_907_);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_908_, v___f_910_, v_xs_905_, v___x_911_, v___x_912_, v_b_904_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl(lean_object* v_00_u03b2_914_, lean_object* v_00_u03b1_915_, lean_object* v_n_916_, lean_object* v_f_917_, lean_object* v_b_918_, lean_object* v_xs_919_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_array_get_size(v_xs_919_);
v___x_922_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_923_ = lean_nat_dec_lt(v___x_920_, v___x_921_);
if (v___x_923_ == 0)
{
lean_dec_ref(v_xs_919_);
lean_dec(v_f_917_);
return v_b_918_;
}
else
{
lean_object* v___f_924_; size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; 
v___f_924_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_924_, 0, v_f_917_);
v___x_925_ = ((size_t)0ULL);
v___x_926_ = lean_usize_of_nat(v___x_921_);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_922_, v___f_924_, v_xs_919_, v___x_925_, v___x_926_, v_b_918_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___boxed(lean_object* v_00_u03b2_928_, lean_object* v_00_u03b1_929_, lean_object* v_n_930_, lean_object* v_f_931_, lean_object* v_b_932_, lean_object* v_xs_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Vector_foldl(v_00_u03b2_928_, v_00_u03b1_929_, v_n_930_, v_f_931_, v_b_932_, v_xs_933_);
lean_dec(v_n_930_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___redArg(lean_object* v_f_935_, lean_object* v_b_936_, lean_object* v_xs_937_){
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
LEAN_EXPORT lean_object* l_Vector_foldr(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_n_948_, lean_object* v_f_949_, lean_object* v_b_950_, lean_object* v_xs_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_952_ = lean_array_get_size(v_xs_951_);
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_955_ = lean_nat_dec_lt(v___x_953_, v___x_952_);
if (v___x_955_ == 0)
{
lean_dec_ref(v_xs_951_);
lean_dec(v_f_949_);
return v_b_950_;
}
else
{
lean_object* v___f_956_; size_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
v___f_956_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_956_, 0, v_f_949_);
v___x_957_ = lean_usize_of_nat(v___x_952_);
v___x_958_ = ((size_t)0ULL);
v___x_959_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_954_, v___f_956_, v_xs_951_, v___x_957_, v___x_958_, v_b_950_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___boxed(lean_object* v_00_u03b1_960_, lean_object* v_00_u03b2_961_, lean_object* v_n_962_, lean_object* v_f_963_, lean_object* v_b_964_, lean_object* v_xs_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Vector_foldr(v_00_u03b1_960_, v_00_u03b2_961_, v_n_962_, v_f_963_, v_b_964_, v_xs_965_);
lean_dec(v_n_962_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg(lean_object* v_xs_967_, lean_object* v_ys_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Array_append___redArg(v_xs_967_, v_ys_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg___boxed(lean_object* v_xs_970_, lean_object* v_ys_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Vector_append___redArg(v_xs_970_, v_ys_971_);
lean_dec_ref(v_ys_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Vector_append(lean_object* v_00_u03b1_973_, lean_object* v_n_974_, lean_object* v_m_975_, lean_object* v_xs_976_, lean_object* v_ys_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Array_append___redArg(v_xs_976_, v_ys_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___boxed(lean_object* v_00_u03b1_979_, lean_object* v_n_980_, lean_object* v_m_981_, lean_object* v_xs_982_, lean_object* v_ys_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Vector_append(v_00_u03b1_979_, v_n_980_, v_m_981_, v_xs_982_, v_ys_983_);
lean_dec_ref(v_ys_983_);
lean_dec(v_m_981_);
lean_dec(v_n_980_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat___redArg(lean_object* v_n_985_, lean_object* v_m_986_){
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
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat(lean_object* v_00_u03b1_988_, lean_object* v_n_989_, lean_object* v_m_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_991_, 0, lean_box(0));
lean_closure_set(v___x_991_, 1, v_n_989_);
lean_closure_set(v___x_991_, 2, v_m_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg(lean_object* v_xs_992_){
_start:
{
lean_inc_ref(v_xs_992_);
return v_xs_992_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg___boxed(lean_object* v_xs_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Vector_cast___redArg(v_xs_993_);
lean_dec_ref(v_xs_993_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast(lean_object* v_n_995_, lean_object* v_m_996_, lean_object* v_00_u03b1_997_, lean_object* v_h_998_, lean_object* v_xs_999_){
_start:
{
lean_inc_ref(v_xs_999_);
return v_xs_999_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___boxed(lean_object* v_n_1000_, lean_object* v_m_1001_, lean_object* v_00_u03b1_1002_, lean_object* v_h_1003_, lean_object* v_xs_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Vector_cast(v_n_1000_, v_m_1001_, v_00_u03b1_1002_, v_h_1003_, v_xs_1004_);
lean_dec_ref(v_xs_1004_);
lean_dec(v_m_1001_);
lean_dec(v_n_1000_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg(lean_object* v_xs_1006_, lean_object* v_start_1007_, lean_object* v_stop_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Array_extract___redArg(v_xs_1006_, v_start_1007_, v_stop_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg___boxed(lean_object* v_xs_1010_, lean_object* v_start_1011_, lean_object* v_stop_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Vector_extract___redArg(v_xs_1010_, v_start_1011_, v_stop_1012_);
lean_dec_ref(v_xs_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract(lean_object* v_00_u03b1_1014_, lean_object* v_n_1015_, lean_object* v_xs_1016_, lean_object* v_start_1017_, lean_object* v_stop_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Array_extract___redArg(v_xs_1016_, v_start_1017_, v_stop_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___boxed(lean_object* v_00_u03b1_1020_, lean_object* v_n_1021_, lean_object* v_xs_1022_, lean_object* v_start_1023_, lean_object* v_stop_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Vector_extract(v_00_u03b1_1020_, v_n_1021_, v_xs_1022_, v_start_1023_, v_stop_1024_);
lean_dec_ref(v_xs_1022_);
lean_dec(v_n_1021_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg(lean_object* v_n_1026_, lean_object* v_xs_1027_, lean_object* v_i_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = l_Array_extract___redArg(v_xs_1027_, v___x_1029_, v_i_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg___boxed(lean_object* v_n_1031_, lean_object* v_xs_1032_, lean_object* v_i_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Vector_take___redArg(v_n_1031_, v_xs_1032_, v_i_1033_);
lean_dec_ref(v_xs_1032_);
lean_dec(v_n_1031_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Vector_take(lean_object* v_00_u03b1_1035_, lean_object* v_n_1036_, lean_object* v_xs_1037_, lean_object* v_i_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = l_Array_extract___redArg(v_xs_1037_, v___x_1039_, v_i_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_n_1042_, lean_object* v_xs_1043_, lean_object* v_i_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Vector_take(v_00_u03b1_1041_, v_n_1042_, v_xs_1043_, v_i_1044_);
lean_dec_ref(v_xs_1043_);
lean_dec(v_n_1042_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg(lean_object* v_xs_1046_, lean_object* v_i_1047_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_array_get_size(v_xs_1046_);
v___x_1049_ = l_Array_extract___redArg(v_xs_1046_, v_i_1047_, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg___boxed(lean_object* v_xs_1050_, lean_object* v_i_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Vector_drop___redArg(v_xs_1050_, v_i_1051_);
lean_dec_ref(v_xs_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop(lean_object* v_00_u03b1_1053_, lean_object* v_n_1054_, lean_object* v_xs_1055_, lean_object* v_i_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_array_get_size(v_xs_1055_);
v___x_1058_ = l_Array_extract___redArg(v_xs_1055_, v_i_1056_, v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___boxed(lean_object* v_00_u03b1_1059_, lean_object* v_n_1060_, lean_object* v_xs_1061_, lean_object* v_i_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Vector_drop(v_00_u03b1_1059_, v_n_1060_, v_xs_1061_, v_i_1062_);
lean_dec_ref(v_xs_1061_);
lean_dec(v_n_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg(lean_object* v_xs_1064_, lean_object* v_i_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Array_shrink___redArg(v_xs_1064_, v_i_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg___boxed(lean_object* v_xs_1067_, lean_object* v_i_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Vector_shrink___redArg(v_xs_1067_, v_i_1068_);
lean_dec(v_i_1068_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink(lean_object* v_00_u03b1_1070_, lean_object* v_n_1071_, lean_object* v_xs_1072_, lean_object* v_i_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Array_shrink___redArg(v_xs_1072_, v_i_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___boxed(lean_object* v_00_u03b1_1075_, lean_object* v_n_1076_, lean_object* v_xs_1077_, lean_object* v_i_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Vector_shrink(v_00_u03b1_1075_, v_n_1076_, v_xs_1077_, v_i_1078_);
lean_dec(v_i_1078_);
lean_dec(v_n_1076_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg___lam__0(lean_object* v_f_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_apply_1(v_f_1080_, v_x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg(lean_object* v_f_1083_, lean_object* v_xs_1084_){
_start:
{
lean_object* v___f_1085_; lean_object* v___x_1086_; size_t v_sz_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
v___f_1085_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1085_, 0, v_f_1083_);
v___x_1086_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1087_ = lean_array_size(v_xs_1084_);
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1086_, v___f_1085_, v_sz_1087_, v___x_1088_, v_xs_1084_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Vector_map(lean_object* v_00_u03b1_1090_, lean_object* v_00_u03b2_1091_, lean_object* v_n_1092_, lean_object* v_f_1093_, lean_object* v_xs_1094_){
_start:
{
lean_object* v___f_1095_; lean_object* v___x_1096_; size_t v_sz_1097_; size_t v___x_1098_; lean_object* v___x_1099_; 
v___f_1095_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1095_, 0, v_f_1093_);
v___x_1096_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1097_ = lean_array_size(v_xs_1094_);
v___x_1098_ = ((size_t)0ULL);
v___x_1099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1096_, v___f_1095_, v_sz_1097_, v___x_1098_, v_xs_1094_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___boxed(lean_object* v_00_u03b1_1100_, lean_object* v_00_u03b2_1101_, lean_object* v_n_1102_, lean_object* v_f_1103_, lean_object* v_xs_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Vector_map(v_00_u03b1_1100_, v_00_u03b2_1101_, v_n_1102_, v_f_1103_, v_xs_1104_);
lean_dec(v_n_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg___lam__0(lean_object* v_f_1106_, lean_object* v_i_1107_, lean_object* v_a_1108_, lean_object* v_x_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_apply_2(v_f_1106_, v_i_1107_, v_a_1108_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg(lean_object* v_f_1111_, lean_object* v_xs_1112_){
_start:
{
lean_object* v___f_1113_; lean_object* v___x_1114_; size_t v_sz_1115_; size_t v___x_1116_; lean_object* v___x_1117_; 
v___f_1113_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1113_, 0, v_f_1111_);
v___x_1114_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1115_ = lean_array_size(v_xs_1112_);
v___x_1116_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1112_);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1114_, v_xs_1112_, v___f_1113_, v_sz_1115_, v___x_1116_, v_xs_1112_);
lean_dec_ref(v_xs_1112_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx(lean_object* v_00_u03b1_1118_, lean_object* v_00_u03b2_1119_, lean_object* v_n_1120_, lean_object* v_f_1121_, lean_object* v_xs_1122_){
_start:
{
lean_object* v___f_1123_; lean_object* v___x_1124_; size_t v_sz_1125_; size_t v___x_1126_; lean_object* v___x_1127_; 
v___f_1123_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1123_, 0, v_f_1121_);
v___x_1124_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1125_ = lean_array_size(v_xs_1122_);
v___x_1126_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1122_);
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1124_, v_xs_1122_, v___f_1123_, v_sz_1125_, v___x_1126_, v_xs_1122_);
lean_dec_ref(v_xs_1122_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___boxed(lean_object* v_00_u03b1_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_n_1130_, lean_object* v_f_1131_, lean_object* v_xs_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Vector_mapIdx(v_00_u03b1_1128_, v_00_u03b2_1129_, v_n_1130_, v_f_1131_, v_xs_1132_);
lean_dec(v_n_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg___lam__0(lean_object* v_f_1134_, lean_object* v_x1_1135_, lean_object* v_x2_1136_, lean_object* v_x3_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_apply_3(v_f_1134_, v_x1_1135_, v_x2_1136_, lean_box(0));
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg(lean_object* v_xs_1139_, lean_object* v_f_1140_){
_start:
{
lean_object* v___f_1141_; lean_object* v___x_1142_; size_t v_sz_1143_; size_t v___x_1144_; lean_object* v___x_1145_; 
v___f_1141_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1141_, 0, v_f_1140_);
v___x_1142_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1143_ = lean_array_size(v_xs_1139_);
v___x_1144_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1139_);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1142_, v_xs_1139_, v___f_1141_, v_sz_1143_, v___x_1144_, v_xs_1139_);
lean_dec_ref(v_xs_1139_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx(lean_object* v_00_u03b1_1146_, lean_object* v_n_1147_, lean_object* v_00_u03b2_1148_, lean_object* v_xs_1149_, lean_object* v_f_1150_){
_start:
{
lean_object* v___f_1151_; lean_object* v___x_1152_; size_t v_sz_1153_; size_t v___x_1154_; lean_object* v___x_1155_; 
v___f_1151_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1151_, 0, v_f_1150_);
v___x_1152_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1153_ = lean_array_size(v_xs_1149_);
v___x_1154_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1149_);
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1152_, v_xs_1149_, v___f_1151_, v_sz_1153_, v___x_1154_, v_xs_1149_);
lean_dec_ref(v_xs_1149_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___boxed(lean_object* v_00_u03b1_1156_, lean_object* v_n_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_xs_1159_, lean_object* v_f_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Vector_mapFinIdx(v_00_u03b1_1156_, v_n_1157_, v_00_u03b2_1158_, v_xs_1159_, v_f_1160_);
lean_dec(v_n_1157_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(lean_object* v_k_1162_, lean_object* v_acc_1163_, lean_object* v_n_1164_, lean_object* v_inst_1165_, lean_object* v_f_1166_, lean_object* v_xs_1167_, lean_object* v_____do__lift_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(v_k_1162_, v_acc_1163_, v_n_1164_, v_inst_1165_, v_f_1166_, v_xs_1167_, v_____do__lift_1168_);
lean_dec(v_k_1162_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(lean_object* v_n_1170_, lean_object* v_inst_1171_, lean_object* v_f_1172_, lean_object* v_xs_1173_, lean_object* v_k_1174_, lean_object* v_acc_1175_){
_start:
{
lean_object* v_toApplicative_1176_; lean_object* v_toBind_1177_; lean_object* v_toPure_1178_; uint8_t v___x_1179_; 
v_toApplicative_1176_ = lean_ctor_get(v_inst_1171_, 0);
v_toBind_1177_ = lean_ctor_get(v_inst_1171_, 1);
lean_inc(v_toBind_1177_);
v_toPure_1178_ = lean_ctor_get(v_toApplicative_1176_, 1);
v___x_1179_ = lean_nat_dec_lt(v_k_1174_, v_n_1170_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
lean_inc(v_toPure_1178_);
lean_dec(v_toBind_1177_);
lean_dec(v_k_1174_);
lean_dec_ref(v_xs_1173_);
lean_dec(v_f_1172_);
lean_dec_ref(v_inst_1171_);
lean_dec(v_n_1170_);
v___x_1180_ = lean_apply_2(v_toPure_1178_, lean_box(0), v_acc_1175_);
return v___x_1180_;
}
else
{
lean_object* v___f_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_inc_ref(v_xs_1173_);
lean_inc(v_f_1172_);
lean_inc(v_k_1174_);
v___f_1181_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1181_, 0, v_k_1174_);
lean_closure_set(v___f_1181_, 1, v_acc_1175_);
lean_closure_set(v___f_1181_, 2, v_n_1170_);
lean_closure_set(v___f_1181_, 3, v_inst_1171_);
lean_closure_set(v___f_1181_, 4, v_f_1172_);
lean_closure_set(v___f_1181_, 5, v_xs_1173_);
v___x_1182_ = lean_array_fget(v_xs_1173_, v_k_1174_);
lean_dec(v_k_1174_);
lean_dec_ref(v_xs_1173_);
v___x_1183_ = lean_apply_1(v_f_1172_, v___x_1182_);
v___x_1184_ = lean_apply_4(v_toBind_1177_, lean_box(0), lean_box(0), v___x_1183_, v___f_1181_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(lean_object* v_k_1185_, lean_object* v_acc_1186_, lean_object* v_n_1187_, lean_object* v_inst_1188_, lean_object* v_f_1189_, lean_object* v_xs_1190_, lean_object* v_____do__lift_1191_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1192_ = lean_unsigned_to_nat(1u);
v___x_1193_ = lean_nat_add(v_k_1185_, v___x_1192_);
v___x_1194_ = lean_array_push(v_acc_1186_, v_____do__lift_1191_);
v___x_1195_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1187_, v_inst_1188_, v_f_1189_, v_xs_1190_, v___x_1193_, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(lean_object* v_m_1196_, lean_object* v_00_u03b1_1197_, lean_object* v_00_u03b2_1198_, lean_object* v_n_1199_, lean_object* v_inst_1200_, lean_object* v_f_1201_, lean_object* v_xs_1202_, lean_object* v_k_1203_, lean_object* v_h_1204_, lean_object* v_acc_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1199_, v_inst_1200_, v_f_1201_, v_xs_1202_, v_k_1203_, v_acc_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM___redArg(lean_object* v_n_1209_, lean_object* v_inst_1210_, lean_object* v_f_1211_, lean_object* v_xs_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1215_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1209_, v_inst_1210_, v_f_1211_, v_xs_1212_, v___x_1213_, v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM(lean_object* v_m_1216_, lean_object* v_00_u03b1_1217_, lean_object* v_00_u03b2_1218_, lean_object* v_n_1219_, lean_object* v_inst_1220_, lean_object* v_f_1221_, lean_object* v_xs_1222_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_unsigned_to_nat(0u);
v___x_1224_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1225_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1219_, v_inst_1220_, v_f_1221_, v_xs_1222_, v___x_1223_, v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg___lam__0(lean_object* v_f_1226_, lean_object* v_x_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_apply_1(v_f_1226_, v___y_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg(lean_object* v_inst_1230_, lean_object* v_xs_1231_, lean_object* v_f_1232_){
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
lean_object* v___f_1240_; size_t v___x_1241_; size_t v___x_1242_; lean_object* v___x_1243_; 
v___f_1240_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1240_, 0, v_f_1232_);
v___x_1241_ = ((size_t)0ULL);
v___x_1242_ = lean_usize_of_nat(v___x_1236_);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1230_, v___f_1240_, v_xs_1231_, v___x_1241_, v___x_1242_, v___x_1237_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM(lean_object* v_m_1244_, lean_object* v_00_u03b1_1245_, lean_object* v_n_1246_, lean_object* v_inst_1247_, lean_object* v_xs_1248_, lean_object* v_f_1249_){
_start:
{
lean_object* v_toApplicative_1250_; lean_object* v_toPure_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_toApplicative_1250_ = lean_ctor_get(v_inst_1247_, 0);
v_toPure_1251_ = lean_ctor_get(v_toApplicative_1250_, 1);
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = lean_array_get_size(v_xs_1248_);
v___x_1254_ = lean_box(0);
v___x_1255_ = lean_nat_dec_lt(v___x_1252_, v___x_1253_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_inc(v_toPure_1251_);
lean_dec(v_f_1249_);
lean_dec_ref(v_xs_1248_);
lean_dec_ref(v_inst_1247_);
v___x_1256_ = lean_apply_2(v_toPure_1251_, lean_box(0), v___x_1254_);
return v___x_1256_;
}
else
{
lean_object* v___f_1257_; size_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v___f_1257_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1257_, 0, v_f_1249_);
v___x_1258_ = ((size_t)0ULL);
v___x_1259_ = lean_usize_of_nat(v___x_1253_);
v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1247_, v___f_1257_, v_xs_1248_, v___x_1258_, v___x_1259_, v___x_1254_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM___boxed(lean_object* v_m_1261_, lean_object* v_00_u03b1_1262_, lean_object* v_n_1263_, lean_object* v_inst_1264_, lean_object* v_xs_1265_, lean_object* v_f_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Vector_forM(v_m_1261_, v_00_u03b1_1262_, v_n_1263_, v_inst_1264_, v_xs_1265_, v_f_1266_);
lean_dec(v_n_1263_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(lean_object* v_i_1268_, lean_object* v_acc_1269_, lean_object* v_n_1270_, lean_object* v_inst_1271_, lean_object* v_xs_1272_, lean_object* v_f_1273_, lean_object* v_____do__lift_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(v_i_1268_, v_acc_1269_, v_n_1270_, v_inst_1271_, v_xs_1272_, v_f_1273_, v_____do__lift_1274_);
lean_dec_ref(v_____do__lift_1274_);
lean_dec(v_i_1268_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(lean_object* v_n_1276_, lean_object* v_inst_1277_, lean_object* v_xs_1278_, lean_object* v_f_1279_, lean_object* v_i_1280_, lean_object* v_acc_1281_){
_start:
{
lean_object* v_toApplicative_1282_; lean_object* v_toBind_1283_; lean_object* v_toPure_1284_; uint8_t v___x_1285_; 
v_toApplicative_1282_ = lean_ctor_get(v_inst_1277_, 0);
v_toBind_1283_ = lean_ctor_get(v_inst_1277_, 1);
lean_inc(v_toBind_1283_);
v_toPure_1284_ = lean_ctor_get(v_toApplicative_1282_, 1);
v___x_1285_ = lean_nat_dec_lt(v_i_1280_, v_n_1276_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
lean_inc(v_toPure_1284_);
lean_dec(v_toBind_1283_);
lean_dec(v_i_1280_);
lean_dec(v_f_1279_);
lean_dec_ref(v_xs_1278_);
lean_dec_ref(v_inst_1277_);
lean_dec(v_n_1276_);
v___x_1286_ = lean_apply_2(v_toPure_1284_, lean_box(0), v_acc_1281_);
return v___x_1286_;
}
else
{
lean_object* v___f_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_inc(v_f_1279_);
lean_inc_ref(v_xs_1278_);
lean_inc(v_i_1280_);
v___f_1287_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1287_, 0, v_i_1280_);
lean_closure_set(v___f_1287_, 1, v_acc_1281_);
lean_closure_set(v___f_1287_, 2, v_n_1276_);
lean_closure_set(v___f_1287_, 3, v_inst_1277_);
lean_closure_set(v___f_1287_, 4, v_xs_1278_);
lean_closure_set(v___f_1287_, 5, v_f_1279_);
v___x_1288_ = lean_array_fget(v_xs_1278_, v_i_1280_);
lean_dec(v_i_1280_);
lean_dec_ref(v_xs_1278_);
v___x_1289_ = lean_apply_1(v_f_1279_, v___x_1288_);
v___x_1290_ = lean_apply_4(v_toBind_1283_, lean_box(0), lean_box(0), v___x_1289_, v___f_1287_);
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(lean_object* v_i_1291_, lean_object* v_acc_1292_, lean_object* v_n_1293_, lean_object* v_inst_1294_, lean_object* v_xs_1295_, lean_object* v_f_1296_, lean_object* v_____do__lift_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = lean_unsigned_to_nat(1u);
v___x_1299_ = lean_nat_add(v_i_1291_, v___x_1298_);
v___x_1300_ = l_Array_append___redArg(v_acc_1292_, v_____do__lift_1297_);
v___x_1301_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1293_, v_inst_1294_, v_xs_1295_, v_f_1296_, v___x_1299_, v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(lean_object* v_m_1302_, lean_object* v_00_u03b1_1303_, lean_object* v_n_1304_, lean_object* v_00_u03b2_1305_, lean_object* v_k_1306_, lean_object* v_inst_1307_, lean_object* v_xs_1308_, lean_object* v_f_1309_, lean_object* v_i_1310_, lean_object* v_h_1311_, lean_object* v_acc_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1304_, v_inst_1307_, v_xs_1308_, v_f_1309_, v_i_1310_, v_acc_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(lean_object* v_m_1314_, lean_object* v_00_u03b1_1315_, lean_object* v_n_1316_, lean_object* v_00_u03b2_1317_, lean_object* v_k_1318_, lean_object* v_inst_1319_, lean_object* v_xs_1320_, lean_object* v_f_1321_, lean_object* v_i_1322_, lean_object* v_h_1323_, lean_object* v_acc_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(v_m_1314_, v_00_u03b1_1315_, v_n_1316_, v_00_u03b2_1317_, v_k_1318_, v_inst_1319_, v_xs_1320_, v_f_1321_, v_i_1322_, v_h_1323_, v_acc_1324_);
lean_dec(v_k_1318_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___redArg(lean_object* v_n_1326_, lean_object* v_inst_1327_, lean_object* v_xs_1328_, lean_object* v_f_1329_){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1332_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1326_, v_inst_1327_, v_xs_1328_, v_f_1329_, v___x_1330_, v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM(lean_object* v_m_1333_, lean_object* v_00_u03b1_1334_, lean_object* v_n_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_k_1337_, lean_object* v_inst_1338_, lean_object* v_xs_1339_, lean_object* v_f_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_unsigned_to_nat(0u);
v___x_1342_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1343_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1335_, v_inst_1338_, v_xs_1339_, v_f_1340_, v___x_1341_, v___x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___boxed(lean_object* v_m_1344_, lean_object* v_00_u03b1_1345_, lean_object* v_n_1346_, lean_object* v_00_u03b2_1347_, lean_object* v_k_1348_, lean_object* v_inst_1349_, lean_object* v_xs_1350_, lean_object* v_f_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Vector_flatMapM(v_m_1344_, v_00_u03b1_1345_, v_n_1346_, v_00_u03b2_1347_, v_k_1348_, v_inst_1349_, v_xs_1350_, v_f_1351_);
lean_dec(v_k_1348_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1353_, lean_object* v_ys_1354_, lean_object* v_inst_1355_, lean_object* v_xs_1356_, lean_object* v_f_1357_, lean_object* v_n_1358_, lean_object* v_____do__lift_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Vector_mapFinIdxM_map___redArg___lam__0(v_j_1353_, v_ys_1354_, v_inst_1355_, v_xs_1356_, v_f_1357_, v_n_1358_, v_____do__lift_1359_);
lean_dec(v_n_1358_);
lean_dec(v_j_1353_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg(lean_object* v_inst_1361_, lean_object* v_xs_1362_, lean_object* v_f_1363_, lean_object* v_i_1364_, lean_object* v_j_1365_, lean_object* v_ys_1366_){
_start:
{
lean_object* v_toApplicative_1367_; lean_object* v_toBind_1368_; lean_object* v_toPure_1369_; lean_object* v_zero_1370_; uint8_t v_isZero_1371_; 
v_toApplicative_1367_ = lean_ctor_get(v_inst_1361_, 0);
v_toBind_1368_ = lean_ctor_get(v_inst_1361_, 1);
lean_inc(v_toBind_1368_);
v_toPure_1369_ = lean_ctor_get(v_toApplicative_1367_, 1);
v_zero_1370_ = lean_unsigned_to_nat(0u);
v_isZero_1371_ = lean_nat_dec_eq(v_i_1364_, v_zero_1370_);
if (v_isZero_1371_ == 1)
{
lean_object* v___x_1372_; 
lean_inc(v_toPure_1369_);
lean_dec(v_toBind_1368_);
lean_dec(v_j_1365_);
lean_dec(v_f_1363_);
lean_dec_ref(v_xs_1362_);
lean_dec_ref(v_inst_1361_);
v___x_1372_ = lean_apply_2(v_toPure_1369_, lean_box(0), v_ys_1366_);
return v___x_1372_;
}
else
{
lean_object* v_one_1373_; lean_object* v_n_1374_; lean_object* v___f_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_one_1373_ = lean_unsigned_to_nat(1u);
v_n_1374_ = lean_nat_sub(v_i_1364_, v_one_1373_);
lean_inc(v_f_1363_);
lean_inc_ref(v_xs_1362_);
lean_inc(v_j_1365_);
v___f_1375_ = lean_alloc_closure((void*)(l_Vector_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1375_, 0, v_j_1365_);
lean_closure_set(v___f_1375_, 1, v_ys_1366_);
lean_closure_set(v___f_1375_, 2, v_inst_1361_);
lean_closure_set(v___f_1375_, 3, v_xs_1362_);
lean_closure_set(v___f_1375_, 4, v_f_1363_);
lean_closure_set(v___f_1375_, 5, v_n_1374_);
v___x_1376_ = lean_array_fget(v_xs_1362_, v_j_1365_);
lean_dec_ref(v_xs_1362_);
v___x_1377_ = lean_apply_3(v_f_1363_, v_j_1365_, v___x_1376_, lean_box(0));
v___x_1378_ = lean_apply_4(v_toBind_1368_, lean_box(0), lean_box(0), v___x_1377_, v___f_1375_);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1379_, lean_object* v_ys_1380_, lean_object* v_inst_1381_, lean_object* v_xs_1382_, lean_object* v_f_1383_, lean_object* v_n_1384_, lean_object* v_____do__lift_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1386_ = lean_unsigned_to_nat(1u);
v___x_1387_ = lean_nat_add(v_j_1379_, v___x_1386_);
v___x_1388_ = lean_array_push(v_ys_1380_, v_____do__lift_1385_);
v___x_1389_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1381_, v_xs_1382_, v_f_1383_, v_n_1384_, v___x_1387_, v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1390_, lean_object* v_xs_1391_, lean_object* v_f_1392_, lean_object* v_i_1393_, lean_object* v_j_1394_, lean_object* v_ys_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1390_, v_xs_1391_, v_f_1392_, v_i_1393_, v_j_1394_, v_ys_1395_);
lean_dec(v_i_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map(lean_object* v_n_1397_, lean_object* v_00_u03b1_1398_, lean_object* v_00_u03b2_1399_, lean_object* v_m_1400_, lean_object* v_inst_1401_, lean_object* v_xs_1402_, lean_object* v_f_1403_, lean_object* v_i_1404_, lean_object* v_j_1405_, lean_object* v_inv_1406_, lean_object* v_ys_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1401_, v_xs_1402_, v_f_1403_, v_i_1404_, v_j_1405_, v_ys_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___boxed(lean_object* v_n_1409_, lean_object* v_00_u03b1_1410_, lean_object* v_00_u03b2_1411_, lean_object* v_m_1412_, lean_object* v_inst_1413_, lean_object* v_xs_1414_, lean_object* v_f_1415_, lean_object* v_i_1416_, lean_object* v_j_1417_, lean_object* v_inv_1418_, lean_object* v_ys_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Vector_mapFinIdxM_map(v_n_1409_, v_00_u03b1_1410_, v_00_u03b2_1411_, v_m_1412_, v_inst_1413_, v_xs_1414_, v_f_1415_, v_i_1416_, v_j_1417_, v_inv_1418_, v_ys_1419_);
lean_dec(v_i_1416_);
lean_dec(v_n_1409_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg(lean_object* v_n_1421_, lean_object* v_inst_1422_, lean_object* v_xs_1423_, lean_object* v_f_1424_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1427_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1422_, v_xs_1423_, v_f_1424_, v_n_1421_, v___x_1425_, v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg___boxed(lean_object* v_n_1428_, lean_object* v_inst_1429_, lean_object* v_xs_1430_, lean_object* v_f_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Vector_mapFinIdxM___redArg(v_n_1428_, v_inst_1429_, v_xs_1430_, v_f_1431_);
lean_dec(v_n_1428_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM(lean_object* v_n_1433_, lean_object* v_00_u03b1_1434_, lean_object* v_00_u03b2_1435_, lean_object* v_m_1436_, lean_object* v_inst_1437_, lean_object* v_xs_1438_, lean_object* v_f_1439_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1442_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1437_, v_xs_1438_, v_f_1439_, v_n_1433_, v___x_1440_, v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___boxed(lean_object* v_n_1443_, lean_object* v_00_u03b1_1444_, lean_object* v_00_u03b2_1445_, lean_object* v_m_1446_, lean_object* v_inst_1447_, lean_object* v_xs_1448_, lean_object* v_f_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Vector_mapFinIdxM(v_n_1443_, v_00_u03b1_1444_, v_00_u03b2_1445_, v_m_1446_, v_inst_1447_, v_xs_1448_, v_f_1449_);
lean_dec(v_n_1443_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg(lean_object* v_n_1451_, lean_object* v_inst_1452_, lean_object* v_f_1453_, lean_object* v_xs_1454_){
_start:
{
lean_object* v___f_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___f_1455_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1455_, 0, v_f_1453_);
v___x_1456_ = lean_unsigned_to_nat(0u);
v___x_1457_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1458_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1452_, v_xs_1454_, v___f_1455_, v_n_1451_, v___x_1456_, v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg___boxed(lean_object* v_n_1459_, lean_object* v_inst_1460_, lean_object* v_f_1461_, lean_object* v_xs_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Vector_mapIdxM___redArg(v_n_1459_, v_inst_1460_, v_f_1461_, v_xs_1462_);
lean_dec(v_n_1459_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM(lean_object* v_n_1464_, lean_object* v_00_u03b1_1465_, lean_object* v_00_u03b2_1466_, lean_object* v_m_1467_, lean_object* v_inst_1468_, lean_object* v_f_1469_, lean_object* v_xs_1470_){
_start:
{
lean_object* v___f_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___f_1471_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1471_, 0, v_f_1469_);
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1474_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1468_, v_xs_1470_, v___f_1471_, v_n_1464_, v___x_1472_, v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___boxed(lean_object* v_n_1475_, lean_object* v_00_u03b1_1476_, lean_object* v_00_u03b2_1477_, lean_object* v_m_1478_, lean_object* v_inst_1479_, lean_object* v_f_1480_, lean_object* v_xs_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Vector_mapIdxM(v_n_1475_, v_00_u03b1_1476_, v_00_u03b2_1477_, v_m_1478_, v_inst_1479_, v_f_1480_, v_xs_1481_);
lean_dec(v_n_1475_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___redArg(lean_object* v_inst_1483_, lean_object* v_f_1484_, lean_object* v_xs_1485_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1483_, v_f_1484_, v_xs_1485_, v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM(lean_object* v_00_u03b2_1488_, lean_object* v_n_1489_, lean_object* v_00_u03b1_1490_, lean_object* v_m_1491_, lean_object* v_inst_1492_, lean_object* v_f_1493_, lean_object* v_xs_1494_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1492_, v_f_1493_, v_xs_1494_, v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___boxed(lean_object* v_00_u03b2_1497_, lean_object* v_n_1498_, lean_object* v_00_u03b1_1499_, lean_object* v_m_1500_, lean_object* v_inst_1501_, lean_object* v_f_1502_, lean_object* v_xs_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Vector_firstM(v_00_u03b2_1497_, v_n_1498_, v_00_u03b1_1499_, v_m_1500_, v_inst_1501_, v_f_1502_, v_xs_1503_);
lean_dec(v_n_1498_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0(lean_object* v_x_1505_){
_start:
{
lean_inc_ref(v_x_1505_);
return v_x_1505_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0___boxed(lean_object* v_x_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Vector_flatten___redArg___lam__0(v_x_1506_);
lean_dec_ref(v_x_1506_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg(lean_object* v_xs_1512_){
_start:
{
lean_object* v___f_1513_; lean_object* v___x_1514_; size_t v_sz_1515_; size_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___f_1513_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1514_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1515_ = lean_array_size(v_xs_1512_);
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1514_, v___f_1513_, v_sz_1515_, v___x_1516_, v_xs_1512_);
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1520_ = lean_array_get_size(v___x_1517_);
v___x_1521_ = lean_nat_dec_lt(v___x_1518_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_dec(v___x_1517_);
return v___x_1519_;
}
else
{
lean_object* v___f_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
v___f_1522_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1523_ = lean_usize_of_nat(v___x_1520_);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1514_, v___f_1522_, v___x_1517_, v___x_1516_, v___x_1523_, v___x_1519_);
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten(lean_object* v_00_u03b1_1525_, lean_object* v_n_1526_, lean_object* v_m_1527_, lean_object* v_xs_1528_){
_start:
{
lean_object* v___f_1529_; lean_object* v___x_1530_; size_t v_sz_1531_; size_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___f_1529_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1530_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1531_ = lean_array_size(v_xs_1528_);
v___x_1532_ = ((size_t)0ULL);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1530_, v___f_1529_, v_sz_1531_, v___x_1532_, v_xs_1528_);
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1536_ = lean_array_get_size(v___x_1533_);
v___x_1537_ = lean_nat_dec_lt(v___x_1534_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_dec(v___x_1533_);
return v___x_1535_;
}
else
{
lean_object* v___f_1538_; size_t v___x_1539_; lean_object* v___x_1540_; 
v___f_1538_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1539_ = lean_usize_of_nat(v___x_1536_);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1530_, v___f_1538_, v___x_1533_, v___x_1532_, v___x_1539_, v___x_1535_);
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___boxed(lean_object* v_00_u03b1_1541_, lean_object* v_n_1542_, lean_object* v_m_1543_, lean_object* v_xs_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Vector_flatten(v_00_u03b1_1541_, v_n_1542_, v_m_1543_, v_xs_1544_);
lean_dec(v_m_1543_);
lean_dec(v_n_1542_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg___lam__0(lean_object* v_f_1546_, lean_object* v_x1_1547_, lean_object* v_x2_1548_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_apply_1(v_f_1546_, v_x2_1548_);
v___x_1550_ = l_Array_append___redArg(v_x1_1547_, v___x_1549_);
lean_dec_ref(v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg(lean_object* v_xs_1551_, lean_object* v_f_1552_){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1555_ = lean_array_get_size(v_xs_1551_);
v___x_1556_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1557_ = lean_nat_dec_lt(v___x_1553_, v___x_1555_);
if (v___x_1557_ == 0)
{
lean_dec_ref(v_f_1552_);
lean_dec_ref(v_xs_1551_);
return v___x_1554_;
}
else
{
lean_object* v___f_1558_; size_t v___x_1559_; size_t v___x_1560_; lean_object* v___x_1561_; 
v___f_1558_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1558_, 0, v_f_1552_);
v___x_1559_ = ((size_t)0ULL);
v___x_1560_ = lean_usize_of_nat(v___x_1555_);
v___x_1561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1556_, v___f_1558_, v_xs_1551_, v___x_1559_, v___x_1560_, v___x_1554_);
return v___x_1561_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap(lean_object* v_00_u03b1_1562_, lean_object* v_n_1563_, lean_object* v_00_u03b2_1564_, lean_object* v_m_1565_, lean_object* v_xs_1566_, lean_object* v_f_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1570_ = lean_array_get_size(v_xs_1566_);
v___x_1571_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1572_ = lean_nat_dec_lt(v___x_1568_, v___x_1570_);
if (v___x_1572_ == 0)
{
lean_dec_ref(v_f_1567_);
lean_dec_ref(v_xs_1566_);
return v___x_1569_;
}
else
{
lean_object* v___f_1573_; size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v___f_1573_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1573_, 0, v_f_1567_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = lean_usize_of_nat(v___x_1570_);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1571_, v___f_1573_, v_xs_1566_, v___x_1574_, v___x_1575_, v___x_1569_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___boxed(lean_object* v_00_u03b1_1577_, lean_object* v_n_1578_, lean_object* v_00_u03b2_1579_, lean_object* v_m_1580_, lean_object* v_xs_1581_, lean_object* v_f_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Vector_flatMap(v_00_u03b1_1577_, v_n_1578_, v_00_u03b2_1579_, v_m_1580_, v_xs_1581_, v_f_1582_);
lean_dec(v_m_1580_);
lean_dec(v_n_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg(lean_object* v_xs_1584_, lean_object* v_k_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Array_zipIdx___redArg(v_xs_1584_, v_k_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg___boxed(lean_object* v_xs_1587_, lean_object* v_k_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Vector_zipIdx___redArg(v_xs_1587_, v_k_1588_);
lean_dec(v_k_1588_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx(lean_object* v_00_u03b1_1590_, lean_object* v_n_1591_, lean_object* v_xs_1592_, lean_object* v_k_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Array_zipIdx___redArg(v_xs_1592_, v_k_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_n_1596_, lean_object* v_xs_1597_, lean_object* v_k_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Vector_zipIdx(v_00_u03b1_1595_, v_n_1596_, v_xs_1597_, v_k_1598_);
lean_dec(v_k_1598_);
lean_dec(v_n_1596_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg(lean_object* v_as_1600_, lean_object* v_bs_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Array_zip___redArg(v_as_1600_, v_bs_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg___boxed(lean_object* v_as_1603_, lean_object* v_bs_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Vector_zip___redArg(v_as_1603_, v_bs_1604_);
lean_dec_ref(v_bs_1604_);
lean_dec_ref(v_as_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip(lean_object* v_00_u03b1_1606_, lean_object* v_n_1607_, lean_object* v_00_u03b2_1608_, lean_object* v_as_1609_, lean_object* v_bs_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Array_zip___redArg(v_as_1609_, v_bs_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___boxed(lean_object* v_00_u03b1_1612_, lean_object* v_n_1613_, lean_object* v_00_u03b2_1614_, lean_object* v_as_1615_, lean_object* v_bs_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Vector_zip(v_00_u03b1_1612_, v_n_1613_, v_00_u03b2_1614_, v_as_1615_, v_bs_1616_);
lean_dec_ref(v_bs_1616_);
lean_dec_ref(v_as_1615_);
lean_dec(v_n_1613_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___redArg(lean_object* v_f_1618_, lean_object* v_as_1619_, lean_object* v_bs_1620_){
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
LEAN_EXPORT lean_object* l_Vector_zipWith(lean_object* v_00_u03b1_1626_, lean_object* v_00_u03b2_1627_, lean_object* v_00_u03c6_1628_, lean_object* v_n_1629_, lean_object* v_f_1630_, lean_object* v_as_1631_, lean_object* v_bs_1632_){
_start:
{
lean_object* v___f_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___f_1633_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1633_, 0, v_f_1630_);
v___x_1634_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1637_ = l_Array_zipWithMAux___redArg(v___x_1634_, v_as_1631_, v_bs_1632_, v___f_1633_, v___x_1635_, v___x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___boxed(lean_object* v_00_u03b1_1638_, lean_object* v_00_u03b2_1639_, lean_object* v_00_u03c6_1640_, lean_object* v_n_1641_, lean_object* v_f_1642_, lean_object* v_as_1643_, lean_object* v_bs_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Vector_zipWith(v_00_u03b1_1638_, v_00_u03b2_1639_, v_00_u03c6_1640_, v_n_1641_, v_f_1642_, v_as_1643_, v_bs_1644_);
lean_dec(v_n_1641_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg(lean_object* v_xs_1646_){
_start:
{
lean_object* v___x_1647_; lean_object* v_fst_1648_; lean_object* v_snd_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v___x_1647_ = l_Array_unzip___redArg(v_xs_1646_);
v_fst_1648_ = lean_ctor_get(v___x_1647_, 0);
v_snd_1649_ = lean_ctor_get(v___x_1647_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1647_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_snd_1649_);
lean_inc(v_fst_1648_);
lean_dec(v___x_1647_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_fst_1648_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_snd_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg___boxed(lean_object* v_xs_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Vector_unzip___redArg(v_xs_1657_);
lean_dec_ref(v_xs_1657_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip(lean_object* v_00_u03b1_1659_, lean_object* v_00_u03b2_1660_, lean_object* v_n_1661_, lean_object* v_xs_1662_){
_start:
{
lean_object* v___x_1663_; lean_object* v_fst_1664_; lean_object* v_snd_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v___x_1663_ = l_Array_unzip___redArg(v_xs_1662_);
v_fst_1664_ = lean_ctor_get(v___x_1663_, 0);
v_snd_1665_ = lean_ctor_get(v___x_1663_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1663_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_snd_1665_);
lean_inc(v_fst_1664_);
lean_dec(v___x_1663_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_fst_1664_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_snd_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___boxed(lean_object* v_00_u03b1_1673_, lean_object* v_00_u03b2_1674_, lean_object* v_n_1675_, lean_object* v_xs_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Vector_unzip(v_00_u03b1_1673_, v_00_u03b2_1674_, v_n_1675_, v_xs_1676_);
lean_dec_ref(v_xs_1676_);
lean_dec(v_n_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn___redArg(lean_object* v_n_1678_, lean_object* v_f_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Array_ofFn___redArg(v_n_1678_, v_f_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn(lean_object* v_n_1681_, lean_object* v_00_u03b1_1682_, lean_object* v_f_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Array_ofFn___redArg(v_n_1681_, v_f_1683_);
return v___x_1684_;
}
}
static lean_object* _init_l_Vector_swap___auto__1(void){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1685_;
}
}
static lean_object* _init_l_Vector_swap___auto__3(void){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg(lean_object* v_xs_1687_, lean_object* v_i_1688_, lean_object* v_j_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_array_fswap(v_xs_1687_, v_i_1688_, v_j_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg___boxed(lean_object* v_xs_1691_, lean_object* v_i_1692_, lean_object* v_j_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Vector_swap___redArg(v_xs_1691_, v_i_1692_, v_j_1693_);
lean_dec(v_j_1693_);
lean_dec(v_i_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap(lean_object* v_00_u03b1_1695_, lean_object* v_n_1696_, lean_object* v_xs_1697_, lean_object* v_i_1698_, lean_object* v_j_1699_, lean_object* v_hi_1700_, lean_object* v_hj_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_array_fswap(v_xs_1697_, v_i_1698_, v_j_1699_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_n_1704_, lean_object* v_xs_1705_, lean_object* v_i_1706_, lean_object* v_j_1707_, lean_object* v_hi_1708_, lean_object* v_hj_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Vector_swap(v_00_u03b1_1703_, v_n_1704_, v_xs_1705_, v_i_1706_, v_j_1707_, v_hi_1708_, v_hj_1709_);
lean_dec(v_j_1707_);
lean_dec(v_i_1706_);
lean_dec(v_n_1704_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg(lean_object* v_xs_1711_, lean_object* v_i_1712_, lean_object* v_j_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_array_swap(v_xs_1711_, v_i_1712_, v_j_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg___boxed(lean_object* v_xs_1715_, lean_object* v_i_1716_, lean_object* v_j_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Vector_swapIfInBounds___redArg(v_xs_1715_, v_i_1716_, v_j_1717_);
lean_dec(v_j_1717_);
lean_dec(v_i_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds(lean_object* v_00_u03b1_1719_, lean_object* v_n_1720_, lean_object* v_xs_1721_, lean_object* v_i_1722_, lean_object* v_j_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_array_swap(v_xs_1721_, v_i_1722_, v_j_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___boxed(lean_object* v_00_u03b1_1725_, lean_object* v_n_1726_, lean_object* v_xs_1727_, lean_object* v_i_1728_, lean_object* v_j_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Vector_swapIfInBounds(v_00_u03b1_1725_, v_n_1726_, v_xs_1727_, v_i_1728_, v_j_1729_);
lean_dec(v_j_1729_);
lean_dec(v_i_1728_);
lean_dec(v_n_1726_);
return v_res_1730_;
}
}
static lean_object* _init_l_Vector_swapAt___auto__1(void){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg(lean_object* v_xs_1732_, lean_object* v_i_1733_, lean_object* v_x_1734_){
_start:
{
lean_object* v_e_1735_; lean_object* v_xs_x27_1736_; lean_object* v___x_1737_; 
v_e_1735_ = lean_array_fget(v_xs_1732_, v_i_1733_);
v_xs_x27_1736_ = lean_array_fset(v_xs_1732_, v_i_1733_, v_x_1734_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v_e_1735_);
lean_ctor_set(v___x_1737_, 1, v_xs_x27_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg___boxed(lean_object* v_xs_1738_, lean_object* v_i_1739_, lean_object* v_x_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Vector_swapAt___redArg(v_xs_1738_, v_i_1739_, v_x_1740_);
lean_dec(v_i_1739_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt(lean_object* v_00_u03b1_1742_, lean_object* v_n_1743_, lean_object* v_xs_1744_, lean_object* v_i_1745_, lean_object* v_x_1746_, lean_object* v_hi_1747_){
_start:
{
lean_object* v_e_1748_; lean_object* v_xs_x27_1749_; lean_object* v___x_1750_; 
v_e_1748_ = lean_array_fget(v_xs_1744_, v_i_1745_);
v_xs_x27_1749_ = lean_array_fset(v_xs_1744_, v_i_1745_, v_x_1746_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v_e_1748_);
lean_ctor_set(v___x_1750_, 1, v_xs_x27_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___boxed(lean_object* v_00_u03b1_1751_, lean_object* v_n_1752_, lean_object* v_xs_1753_, lean_object* v_i_1754_, lean_object* v_x_1755_, lean_object* v_hi_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Vector_swapAt(v_00_u03b1_1751_, v_n_1752_, v_xs_1753_, v_i_1754_, v_x_1755_, v_hi_1756_);
lean_dec(v_i_1754_);
lean_dec(v_n_1752_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___redArg(lean_object* v_xs_1762_, lean_object* v_i_1763_, lean_object* v_x_1764_){
_start:
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = lean_array_get_size(v_xs_1762_);
v___x_1766_ = lean_nat_dec_lt(v_i_1763_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v_this_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v_fst_1779_; lean_object* v_snd_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
v_this_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1767_, 0, v_x_1764_);
lean_ctor_set(v_this_1767_, 1, v_xs_1762_);
v___x_1768_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1769_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1770_ = lean_unsigned_to_nat(463u);
v___x_1771_ = lean_unsigned_to_nat(4u);
v___x_1772_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1773_ = l_Nat_reprFast(v_i_1763_);
v___x_1774_ = lean_string_append(v___x_1772_, v___x_1773_);
lean_dec_ref(v___x_1773_);
v___x_1775_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1776_ = lean_string_append(v___x_1774_, v___x_1775_);
v___x_1777_ = l_mkPanicMessageWithDecl(v___x_1768_, v___x_1769_, v___x_1770_, v___x_1771_, v___x_1776_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = l_panic___redArg(v_this_1767_, v___x_1777_);
lean_dec_ref_known(v_this_1767_, 2);
v_fst_1779_ = lean_ctor_get(v___x_1778_, 0);
v_snd_1780_ = lean_ctor_get(v___x_1778_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1778_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_snd_1780_);
lean_inc(v_fst_1779_);
lean_dec(v___x_1778_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_fst_1779_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_snd_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
else
{
lean_object* v_e_1788_; lean_object* v_xs_x27_1789_; lean_object* v___x_1790_; 
v_e_1788_ = lean_array_fget(v_xs_1762_, v_i_1763_);
v_xs_x27_1789_ = lean_array_fset(v_xs_1762_, v_i_1763_, v_x_1764_);
lean_dec(v_i_1763_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_e_1788_);
lean_ctor_set(v___x_1790_, 1, v_xs_x27_1789_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21(lean_object* v_00_u03b1_1791_, lean_object* v_n_1792_, lean_object* v_xs_1793_, lean_object* v_i_1794_, lean_object* v_x_1795_){
_start:
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = lean_array_get_size(v_xs_1793_);
v___x_1797_ = lean_nat_dec_lt(v_i_1794_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v_this_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_fst_1810_; lean_object* v_snd_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
v_this_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1798_, 0, v_x_1795_);
lean_ctor_set(v_this_1798_, 1, v_xs_1793_);
v___x_1799_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1800_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1801_ = lean_unsigned_to_nat(463u);
v___x_1802_ = lean_unsigned_to_nat(4u);
v___x_1803_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1804_ = l_Nat_reprFast(v_i_1794_);
v___x_1805_ = lean_string_append(v___x_1803_, v___x_1804_);
lean_dec_ref(v___x_1804_);
v___x_1806_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1807_ = lean_string_append(v___x_1805_, v___x_1806_);
v___x_1808_ = l_mkPanicMessageWithDecl(v___x_1799_, v___x_1800_, v___x_1801_, v___x_1802_, v___x_1807_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = l_panic___redArg(v_this_1798_, v___x_1808_);
lean_dec_ref_known(v_this_1798_, 2);
v_fst_1810_ = lean_ctor_get(v___x_1809_, 0);
v_snd_1811_ = lean_ctor_get(v___x_1809_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1809_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_snd_1811_);
lean_inc(v_fst_1810_);
lean_dec(v___x_1809_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_fst_1810_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_snd_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
lean_object* v_e_1819_; lean_object* v_xs_x27_1820_; lean_object* v___x_1821_; 
v_e_1819_ = lean_array_fget(v_xs_1793_, v_i_1794_);
v_xs_x27_1820_ = lean_array_fset(v_xs_1793_, v_i_1794_, v_x_1795_);
lean_dec(v_i_1794_);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v_e_1819_);
lean_ctor_set(v___x_1821_, 1, v_xs_x27_1820_);
return v___x_1821_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___boxed(lean_object* v_00_u03b1_1822_, lean_object* v_n_1823_, lean_object* v_xs_1824_, lean_object* v_i_1825_, lean_object* v_x_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Vector_swapAt_x21(v_00_u03b1_1822_, v_n_1823_, v_xs_1824_, v_i_1825_, v_x_1826_);
lean_dec(v_n_1823_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Vector_range(lean_object* v_n_1828_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Array_range(v_n_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Vector_range_x27(lean_object* v_start_1830_, lean_object* v_size_1831_, lean_object* v_step_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Array_range_x27(v_start_1830_, v_size_1831_, v_step_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv___redArg(lean_object* v_n_1834_, lean_object* v_xs_1835_, lean_object* v_ys_1836_, lean_object* v_r_1837_){
_start:
{
uint8_t v___x_1838_; 
v___x_1838_ = l_Array_isEqvAux___redArg(v_xs_1835_, v_ys_1836_, v_r_1837_, v_n_1834_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___redArg___boxed(lean_object* v_n_1839_, lean_object* v_xs_1840_, lean_object* v_ys_1841_, lean_object* v_r_1842_){
_start:
{
uint8_t v_res_1843_; lean_object* v_r_1844_; 
v_res_1843_ = l_Vector_isEqv___redArg(v_n_1839_, v_xs_1840_, v_ys_1841_, v_r_1842_);
lean_dec_ref(v_ys_1841_);
lean_dec_ref(v_xs_1840_);
v_r_1844_ = lean_box(v_res_1843_);
return v_r_1844_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv(lean_object* v_00_u03b1_1845_, lean_object* v_n_1846_, lean_object* v_xs_1847_, lean_object* v_ys_1848_, lean_object* v_r_1849_){
_start:
{
uint8_t v___x_1850_; 
v___x_1850_ = l_Array_isEqvAux___redArg(v_xs_1847_, v_ys_1848_, v_r_1849_, v_n_1846_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___boxed(lean_object* v_00_u03b1_1851_, lean_object* v_n_1852_, lean_object* v_xs_1853_, lean_object* v_ys_1854_, lean_object* v_r_1855_){
_start:
{
uint8_t v_res_1856_; lean_object* v_r_1857_; 
v_res_1856_ = l_Vector_isEqv(v_00_u03b1_1851_, v_n_1852_, v_xs_1853_, v_ys_1854_, v_r_1855_);
lean_dec_ref(v_ys_1854_);
lean_dec_ref(v_xs_1853_);
v_r_1857_ = lean_box(v_res_1856_);
return v_r_1857_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__0(lean_object* v_inst_1858_, lean_object* v_x1_1859_, lean_object* v_x2_1860_){
_start:
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = lean_apply_2(v_inst_1858_, v_x1_1859_, v_x2_1860_);
v___x_1862_ = lean_unbox(v___x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__0___boxed(lean_object* v_inst_1863_, lean_object* v_x1_1864_, lean_object* v_x2_1865_){
_start:
{
uint8_t v_res_1866_; lean_object* v_r_1867_; 
v_res_1866_ = l_Vector_instBEq___redArg___lam__0(v_inst_1863_, v_x1_1864_, v_x2_1865_);
v_r_1867_ = lean_box(v_res_1866_);
return v_r_1867_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__1(lean_object* v___f_1868_, lean_object* v_n_1869_, lean_object* v_xs_1870_, lean_object* v_ys_1871_){
_start:
{
uint8_t v___x_1872_; 
v___x_1872_ = l_Array_isEqvAux___redArg(v_xs_1870_, v_ys_1871_, v___f_1868_, v_n_1869_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__1___boxed(lean_object* v___f_1873_, lean_object* v_n_1874_, lean_object* v_xs_1875_, lean_object* v_ys_1876_){
_start:
{
uint8_t v_res_1877_; lean_object* v_r_1878_; 
v_res_1877_ = l_Vector_instBEq___redArg___lam__1(v___f_1873_, v_n_1874_, v_xs_1875_, v_ys_1876_);
lean_dec_ref(v_ys_1876_);
lean_dec_ref(v_xs_1875_);
v_r_1878_ = lean_box(v_res_1877_);
return v_r_1878_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg(lean_object* v_n_1879_, lean_object* v_inst_1880_){
_start:
{
lean_object* v___f_1881_; lean_object* v___f_1882_; 
v___f_1881_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1881_, 0, v_inst_1880_);
v___f_1882_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1882_, 0, v___f_1881_);
lean_closure_set(v___f_1882_, 1, v_n_1879_);
return v___f_1882_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq(lean_object* v_00_u03b1_1883_, lean_object* v_n_1884_, lean_object* v_inst_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Vector_instBEq___redArg(v_n_1884_, v_inst_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___redArg(lean_object* v_xs_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Array_reverse___redArg(v_xs_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse(lean_object* v_00_u03b1_1889_, lean_object* v_n_1890_, lean_object* v_xs_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Array_reverse___redArg(v_xs_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___boxed(lean_object* v_00_u03b1_1893_, lean_object* v_n_1894_, lean_object* v_xs_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Vector_reverse(v_00_u03b1_1893_, v_n_1894_, v_xs_1895_);
lean_dec(v_n_1894_);
return v_res_1896_;
}
}
static lean_object* _init_l_Vector_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___redArg(lean_object* v_xs_1898_, lean_object* v_i_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Array_eraseIdx___redArg(v_xs_1898_, v_i_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx(lean_object* v_00_u03b1_1901_, lean_object* v_n_1902_, lean_object* v_xs_1903_, lean_object* v_i_1904_, lean_object* v_h_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Array_eraseIdx___redArg(v_xs_1903_, v_i_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___boxed(lean_object* v_00_u03b1_1907_, lean_object* v_n_1908_, lean_object* v_xs_1909_, lean_object* v_i_1910_, lean_object* v_h_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Vector_eraseIdx(v_00_u03b1_1907_, v_n_1908_, v_xs_1909_, v_i_1910_, v_h_1911_);
lean_dec(v_n_1908_);
return v_res_1912_;
}
}
static lean_object* _init_l_Vector_eraseIdx_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1916_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1917_ = lean_unsigned_to_nat(4u);
v___x_1918_ = lean_unsigned_to_nat(444u);
v___x_1919_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__1));
v___x_1920_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1921_ = l_mkPanicMessageWithDecl(v___x_1920_, v___x_1919_, v___x_1918_, v___x_1917_, v___x_1916_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg(lean_object* v_n_1922_, lean_object* v_xs_1923_, lean_object* v_i_1924_){
_start:
{
uint8_t v___x_1925_; 
v___x_1925_ = lean_nat_dec_lt(v_i_1924_, v_n_1922_);
if (v___x_1925_ == 0)
{
lean_object* v_this_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_dec(v_i_1924_);
v_this_1926_ = lean_array_pop(v_xs_1923_);
v___x_1927_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1928_ = l_panic___redArg(v_this_1926_, v___x_1927_);
lean_dec_ref(v_this_1926_);
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Array_eraseIdx___redArg(v_xs_1923_, v_i_1924_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg___boxed(lean_object* v_n_1930_, lean_object* v_xs_1931_, lean_object* v_i_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Vector_eraseIdx_x21___redArg(v_n_1930_, v_xs_1931_, v_i_1932_);
lean_dec(v_n_1930_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21(lean_object* v_00_u03b1_1934_, lean_object* v_n_1935_, lean_object* v_xs_1936_, lean_object* v_i_1937_){
_start:
{
uint8_t v___x_1938_; 
v___x_1938_ = lean_nat_dec_lt(v_i_1937_, v_n_1935_);
if (v___x_1938_ == 0)
{
lean_object* v_this_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec(v_i_1937_);
v_this_1939_ = lean_array_pop(v_xs_1936_);
v___x_1940_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1941_ = l_panic___redArg(v_this_1939_, v___x_1940_);
lean_dec_ref(v_this_1939_);
return v___x_1941_;
}
else
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Array_eraseIdx___redArg(v_xs_1936_, v_i_1937_);
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___boxed(lean_object* v_00_u03b1_1943_, lean_object* v_n_1944_, lean_object* v_xs_1945_, lean_object* v_i_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Vector_eraseIdx_x21(v_00_u03b1_1943_, v_n_1944_, v_xs_1945_, v_i_1946_);
lean_dec(v_n_1944_);
return v_res_1947_;
}
}
static lean_object* _init_l_Vector_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg(lean_object* v_xs_1949_, lean_object* v_i_1950_, lean_object* v_x_1951_){
_start:
{
lean_object* v_j_1952_; lean_object* v_as_1953_; lean_object* v___x_1954_; 
v_j_1952_ = lean_array_get_size(v_xs_1949_);
v_as_1953_ = lean_array_push(v_xs_1949_, v_x_1951_);
v___x_1954_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1950_, v_as_1953_, v_j_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg___boxed(lean_object* v_xs_1955_, lean_object* v_i_1956_, lean_object* v_x_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Vector_insertIdx___redArg(v_xs_1955_, v_i_1956_, v_x_1957_);
lean_dec(v_i_1956_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx(lean_object* v_00_u03b1_1959_, lean_object* v_n_1960_, lean_object* v_xs_1961_, lean_object* v_i_1962_, lean_object* v_x_1963_, lean_object* v_h_1964_){
_start:
{
lean_object* v_j_1965_; lean_object* v_as_1966_; lean_object* v___x_1967_; 
v_j_1965_ = lean_array_get_size(v_xs_1961_);
v_as_1966_ = lean_array_push(v_xs_1961_, v_x_1963_);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1962_, v_as_1966_, v_j_1965_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___boxed(lean_object* v_00_u03b1_1968_, lean_object* v_n_1969_, lean_object* v_xs_1970_, lean_object* v_i_1971_, lean_object* v_x_1972_, lean_object* v_h_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Vector_insertIdx(v_00_u03b1_1968_, v_n_1969_, v_xs_1970_, v_i_1971_, v_x_1972_, v_h_1973_);
lean_dec(v_i_1971_);
lean_dec(v_n_1969_);
return v_res_1974_;
}
}
static lean_object* _init_l_Vector_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1976_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1977_ = lean_unsigned_to_nat(4u);
v___x_1978_ = lean_unsigned_to_nat(457u);
v___x_1979_ = ((lean_object*)(l_Vector_insertIdx_x21___redArg___closed__0));
v___x_1980_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1981_ = l_mkPanicMessageWithDecl(v___x_1980_, v___x_1979_, v___x_1978_, v___x_1977_, v___x_1976_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg(lean_object* v_n_1982_, lean_object* v_xs_1983_, lean_object* v_i_1984_, lean_object* v_x_1985_){
_start:
{
uint8_t v___x_1986_; 
v___x_1986_ = lean_nat_dec_le(v_i_1984_, v_n_1982_);
if (v___x_1986_ == 0)
{
lean_object* v_this_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_this_1987_ = lean_array_push(v_xs_1983_, v_x_1985_);
v___x_1988_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1989_ = l_panic___redArg(v_this_1987_, v___x_1988_);
lean_dec_ref(v_this_1987_);
return v___x_1989_;
}
else
{
lean_object* v_j_1990_; lean_object* v_as_1991_; lean_object* v___x_1992_; 
v_j_1990_ = lean_array_get_size(v_xs_1983_);
v_as_1991_ = lean_array_push(v_xs_1983_, v_x_1985_);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1984_, v_as_1991_, v_j_1990_);
return v___x_1992_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg___boxed(lean_object* v_n_1993_, lean_object* v_xs_1994_, lean_object* v_i_1995_, lean_object* v_x_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Vector_insertIdx_x21___redArg(v_n_1993_, v_xs_1994_, v_i_1995_, v_x_1996_);
lean_dec(v_i_1995_);
lean_dec(v_n_1993_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21(lean_object* v_00_u03b1_1998_, lean_object* v_n_1999_, lean_object* v_xs_2000_, lean_object* v_i_2001_, lean_object* v_x_2002_){
_start:
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_nat_dec_le(v_i_2001_, v_n_1999_);
if (v___x_2003_ == 0)
{
lean_object* v_this_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v_this_2004_ = lean_array_push(v_xs_2000_, v_x_2002_);
v___x_2005_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_2006_ = l_panic___redArg(v_this_2004_, v___x_2005_);
lean_dec_ref(v_this_2004_);
return v___x_2006_;
}
else
{
lean_object* v_j_2007_; lean_object* v_as_2008_; lean_object* v___x_2009_; 
v_j_2007_ = lean_array_get_size(v_xs_2000_);
v_as_2008_ = lean_array_push(v_xs_2000_, v_x_2002_);
v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_2001_, v_as_2008_, v_j_2007_);
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___boxed(lean_object* v_00_u03b1_2010_, lean_object* v_n_2011_, lean_object* v_xs_2012_, lean_object* v_i_2013_, lean_object* v_x_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Vector_insertIdx_x21(v_00_u03b1_2010_, v_n_2011_, v_xs_2012_, v_i_2013_, v_x_2014_);
lean_dec(v_i_2013_);
lean_dec(v_n_2011_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg(lean_object* v_n_2016_, lean_object* v_xs_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = l_Array_extract___redArg(v_xs_2017_, v___x_2018_, v_n_2016_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg___boxed(lean_object* v_n_2020_, lean_object* v_xs_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Vector_tail___redArg(v_n_2020_, v_xs_2021_);
lean_dec_ref(v_xs_2021_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail(lean_object* v_00_u03b1_2023_, lean_object* v_n_2024_, lean_object* v_xs_2025_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = lean_unsigned_to_nat(1u);
v___x_2027_ = l_Array_extract___redArg(v_xs_2025_, v___x_2026_, v_n_2024_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___boxed(lean_object* v_00_u03b1_2028_, lean_object* v_n_2029_, lean_object* v_xs_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Vector_tail(v_00_u03b1_2028_, v_n_2029_, v_xs_2030_);
lean_dec_ref(v_xs_2030_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg(lean_object* v_inst_2032_, lean_object* v_xs_2033_, lean_object* v_x_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Array_finIdxOf_x3f___redArg(v_inst_2032_, v_xs_2033_, v_x_2034_);
if (lean_obj_tag(v___x_2035_) == 0)
{
return v___x_2035_;
}
else
{
lean_object* v_val_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
v_val_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_val_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_val_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_2044_, lean_object* v_xs_2045_, lean_object* v_x_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Vector_finIdxOf_x3f___redArg(v_inst_2044_, v_xs_2045_, v_x_2046_);
lean_dec_ref(v_xs_2045_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f(lean_object* v_00_u03b1_2048_, lean_object* v_n_2049_, lean_object* v_inst_2050_, lean_object* v_xs_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Array_finIdxOf_x3f___redArg(v_inst_2050_, v_xs_2051_, v_x_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
return v___x_2053_;
}
else
{
lean_object* v_val_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
v_val_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_val_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_val_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_2062_, lean_object* v_n_2063_, lean_object* v_inst_2064_, lean_object* v_xs_2065_, lean_object* v_x_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Vector_finIdxOf_x3f(v_00_u03b1_2062_, v_n_2063_, v_inst_2064_, v_xs_2065_, v_x_2066_);
lean_dec_ref(v_xs_2065_);
lean_dec(v_n_2063_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg(lean_object* v_p_2068_, lean_object* v_xs_2069_){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2068_, v_xs_2069_, v___x_2070_);
if (lean_obj_tag(v___x_2071_) == 0)
{
return v___x_2071_;
}
else
{
lean_object* v_val_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
v_val_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_val_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_val_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2080_, lean_object* v_xs_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Vector_findFinIdx_x3f___redArg(v_p_2080_, v_xs_2081_);
lean_dec_ref(v_xs_2081_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f(lean_object* v_00_u03b1_2083_, lean_object* v_n_2084_, lean_object* v_p_2085_, lean_object* v_xs_2086_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2085_, v_xs_2086_, v___x_2087_);
if (lean_obj_tag(v___x_2088_) == 0)
{
return v___x_2088_;
}
else
{
lean_object* v_val_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
v_val_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_val_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_val_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2097_, lean_object* v_n_2098_, lean_object* v_p_2099_, lean_object* v_xs_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Vector_findFinIdx_x3f(v_00_u03b1_2097_, v_n_2098_, v_p_2099_, v_xs_2100_);
lean_dec_ref(v_xs_2100_);
lean_dec(v_n_2098_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__0(lean_object* v_toPure_2102_, lean_object* v_____s_2103_){
_start:
{
lean_object* v_fst_2104_; 
v_fst_2104_ = lean_ctor_get(v_____s_2103_, 0);
lean_inc(v_fst_2104_);
lean_dec_ref(v_____s_2103_);
if (lean_obj_tag(v_fst_2104_) == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_apply_2(v_toPure_2102_, lean_box(0), v___x_2105_);
return v___x_2106_;
}
else
{
lean_object* v_val_2107_; lean_object* v___x_2108_; 
v_val_2107_ = lean_ctor_get(v_fst_2104_, 0);
lean_inc(v_val_2107_);
lean_dec_ref_known(v_fst_2104_, 1);
v___x_2108_ = lean_apply_2(v_toPure_2102_, lean_box(0), v_val_2107_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1(lean_object* v___x_2109_, lean_object* v_toPure_2110_, lean_object* v_a_2111_, lean_object* v___x_2112_, uint8_t v_____do__lift_2113_){
_start:
{
if (v_____do__lift_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec(v_a_2111_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2109_);
v___x_2115_ = lean_apply_2(v_toPure_2110_, lean_box(0), v___x_2114_);
return v___x_2115_;
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_dec_ref(v___x_2109_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v_a_2111_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_2112_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
v___x_2120_ = lean_apply_2(v_toPure_2110_, lean_box(0), v___x_2119_);
return v___x_2120_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_2121_, lean_object* v_toPure_2122_, lean_object* v_a_2123_, lean_object* v___x_2124_, lean_object* v_____do__lift_2125_){
_start:
{
uint8_t v_____do__lift_124__boxed_2126_; lean_object* v_res_2127_; 
v_____do__lift_124__boxed_2126_ = lean_unbox(v_____do__lift_2125_);
v_res_2127_ = l_Vector_findM_x3f___redArg___lam__1(v___x_2121_, v_toPure_2122_, v_a_2123_, v___x_2124_, v_____do__lift_124__boxed_2126_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2(lean_object* v___x_2128_, lean_object* v_toPure_2129_, lean_object* v___x_2130_, lean_object* v_f_2131_, lean_object* v_toBind_2132_, lean_object* v_a_2133_, lean_object* v_x_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___f_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_inc(v_a_2133_);
v___f_2136_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2136_, 0, v___x_2128_);
lean_closure_set(v___f_2136_, 1, v_toPure_2129_);
lean_closure_set(v___f_2136_, 2, v_a_2133_);
lean_closure_set(v___f_2136_, 3, v___x_2130_);
v___x_2137_ = lean_apply_1(v_f_2131_, v_a_2133_);
v___x_2138_ = lean_apply_4(v_toBind_2132_, lean_box(0), lean_box(0), v___x_2137_, v___f_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2___boxed(lean_object* v___x_2139_, lean_object* v_toPure_2140_, lean_object* v___x_2141_, lean_object* v_f_2142_, lean_object* v_toBind_2143_, lean_object* v_a_2144_, lean_object* v_x_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Vector_findM_x3f___redArg___lam__2(v___x_2139_, v_toPure_2140_, v___x_2141_, v_f_2142_, v_toBind_2143_, v_a_2144_, v_x_2145_, v___y_2146_);
lean_dec_ref(v___y_2146_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg(lean_object* v_inst_2151_, lean_object* v_f_2152_, lean_object* v_as_2153_){
_start:
{
lean_object* v_toApplicative_2154_; lean_object* v_toBind_2155_; lean_object* v_toPure_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___f_2159_; lean_object* v___f_2160_; size_t v_sz_2161_; size_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v_toApplicative_2154_ = lean_ctor_get(v_inst_2151_, 0);
v_toBind_2155_ = lean_ctor_get(v_inst_2151_, 1);
lean_inc_n(v_toBind_2155_, 2);
v_toPure_2156_ = lean_ctor_get(v_toApplicative_2154_, 1);
v___x_2157_ = lean_box(0);
v___x_2158_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2156_, 2);
v___f_2159_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2159_, 0, v_toPure_2156_);
v___f_2160_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2160_, 0, v___x_2158_);
lean_closure_set(v___f_2160_, 1, v_toPure_2156_);
lean_closure_set(v___f_2160_, 2, v___x_2157_);
lean_closure_set(v___f_2160_, 3, v_f_2152_);
lean_closure_set(v___f_2160_, 4, v_toBind_2155_);
v_sz_2161_ = lean_array_size(v_as_2153_);
v___x_2162_ = ((size_t)0ULL);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2151_, v_as_2153_, v___f_2160_, v_sz_2161_, v___x_2162_, v___x_2158_);
v___x_2164_ = lean_apply_4(v_toBind_2155_, lean_box(0), lean_box(0), v___x_2163_, v___f_2159_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f(lean_object* v_n_2165_, lean_object* v_00_u03b1_2166_, lean_object* v_m_2167_, lean_object* v_inst_2168_, lean_object* v_f_2169_, lean_object* v_as_2170_){
_start:
{
lean_object* v_toApplicative_2171_; lean_object* v_toBind_2172_; lean_object* v_toPure_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___f_2176_; lean_object* v___f_2177_; size_t v_sz_2178_; size_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_toApplicative_2171_ = lean_ctor_get(v_inst_2168_, 0);
v_toBind_2172_ = lean_ctor_get(v_inst_2168_, 1);
lean_inc_n(v_toBind_2172_, 2);
v_toPure_2173_ = lean_ctor_get(v_toApplicative_2171_, 1);
v___x_2174_ = lean_box(0);
v___x_2175_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2173_, 2);
v___f_2176_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2176_, 0, v_toPure_2173_);
v___f_2177_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2177_, 0, v___x_2175_);
lean_closure_set(v___f_2177_, 1, v_toPure_2173_);
lean_closure_set(v___f_2177_, 2, v___x_2174_);
lean_closure_set(v___f_2177_, 3, v_f_2169_);
lean_closure_set(v___f_2177_, 4, v_toBind_2172_);
v_sz_2178_ = lean_array_size(v_as_2170_);
v___x_2179_ = ((size_t)0ULL);
v___x_2180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2168_, v_as_2170_, v___f_2177_, v_sz_2178_, v___x_2179_, v___x_2175_);
v___x_2181_ = lean_apply_4(v_toBind_2172_, lean_box(0), lean_box(0), v___x_2180_, v___f_2176_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___boxed(lean_object* v_n_2182_, lean_object* v_00_u03b1_2183_, lean_object* v_m_2184_, lean_object* v_inst_2185_, lean_object* v_f_2186_, lean_object* v_as_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Vector_findM_x3f(v_n_2182_, v_00_u03b1_2183_, v_m_2184_, v_inst_2185_, v_f_2186_, v_as_2187_);
lean_dec(v_n_2182_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__1(lean_object* v___x_2189_, lean_object* v_toPure_2190_, lean_object* v___x_2191_, lean_object* v_____do__lift_2192_){
_start:
{
if (lean_obj_tag(v_____do__lift_2192_) == 1)
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_dec_ref(v___x_2191_);
v___x_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2193_, 0, v_____do__lift_2192_);
v___x_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v___x_2189_);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
v___x_2196_ = lean_apply_2(v_toPure_2190_, lean_box(0), v___x_2195_);
return v___x_2196_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec(v_____do__lift_2192_);
v___x_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2191_);
v___x_2198_ = lean_apply_2(v_toPure_2190_, lean_box(0), v___x_2197_);
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0(lean_object* v_f_2199_, lean_object* v_toBind_2200_, lean_object* v___f_2201_, lean_object* v_a_2202_, lean_object* v_x_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_apply_1(v_f_2199_, v_a_2202_);
v___x_2206_ = lean_apply_4(v_toBind_2200_, lean_box(0), lean_box(0), v___x_2205_, v___f_2201_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0___boxed(lean_object* v_f_2207_, lean_object* v_toBind_2208_, lean_object* v___f_2209_, lean_object* v_a_2210_, lean_object* v_x_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Vector_findSomeM_x3f___redArg___lam__0(v_f_2207_, v_toBind_2208_, v___f_2209_, v_a_2210_, v_x_2211_, v___y_2212_);
lean_dec_ref(v___y_2212_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg(lean_object* v_inst_2214_, lean_object* v_f_2215_, lean_object* v_as_2216_){
_start:
{
lean_object* v_toApplicative_2217_; lean_object* v_toBind_2218_; lean_object* v_toPure_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___f_2222_; lean_object* v___f_2223_; lean_object* v___f_2224_; size_t v_sz_2225_; size_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_toApplicative_2217_ = lean_ctor_get(v_inst_2214_, 0);
v_toBind_2218_ = lean_ctor_get(v_inst_2214_, 1);
lean_inc_n(v_toBind_2218_, 2);
v_toPure_2219_ = lean_ctor_get(v_toApplicative_2217_, 1);
v___x_2220_ = lean_box(0);
v___x_2221_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2219_, 2);
v___f_2222_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2222_, 0, v_toPure_2219_);
v___f_2223_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2223_, 0, v___x_2220_);
lean_closure_set(v___f_2223_, 1, v_toPure_2219_);
lean_closure_set(v___f_2223_, 2, v___x_2221_);
v___f_2224_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2224_, 0, v_f_2215_);
lean_closure_set(v___f_2224_, 1, v_toBind_2218_);
lean_closure_set(v___f_2224_, 2, v___f_2223_);
v_sz_2225_ = lean_array_size(v_as_2216_);
v___x_2226_ = ((size_t)0ULL);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2214_, v_as_2216_, v___f_2224_, v_sz_2225_, v___x_2226_, v___x_2221_);
v___x_2228_ = lean_apply_4(v_toBind_2218_, lean_box(0), lean_box(0), v___x_2227_, v___f_2222_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f(lean_object* v_m_2229_, lean_object* v_00_u03b1_2230_, lean_object* v_00_u03b2_2231_, lean_object* v_n_2232_, lean_object* v_inst_2233_, lean_object* v_f_2234_, lean_object* v_as_2235_){
_start:
{
lean_object* v_toApplicative_2236_; lean_object* v_toBind_2237_; lean_object* v_toPure_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___f_2241_; lean_object* v___f_2242_; lean_object* v___f_2243_; size_t v_sz_2244_; size_t v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v_toApplicative_2236_ = lean_ctor_get(v_inst_2233_, 0);
v_toBind_2237_ = lean_ctor_get(v_inst_2233_, 1);
lean_inc_n(v_toBind_2237_, 2);
v_toPure_2238_ = lean_ctor_get(v_toApplicative_2236_, 1);
v___x_2239_ = lean_box(0);
v___x_2240_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2238_, 2);
v___f_2241_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2241_, 0, v_toPure_2238_);
v___f_2242_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2242_, 0, v___x_2239_);
lean_closure_set(v___f_2242_, 1, v_toPure_2238_);
lean_closure_set(v___f_2242_, 2, v___x_2240_);
v___f_2243_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2243_, 0, v_f_2234_);
lean_closure_set(v___f_2243_, 1, v_toBind_2237_);
lean_closure_set(v___f_2243_, 2, v___f_2242_);
v_sz_2244_ = lean_array_size(v_as_2235_);
v___x_2245_ = ((size_t)0ULL);
v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2233_, v_as_2235_, v___f_2243_, v_sz_2244_, v___x_2245_, v___x_2240_);
v___x_2247_ = lean_apply_4(v_toBind_2237_, lean_box(0), lean_box(0), v___x_2246_, v___f_2241_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___boxed(lean_object* v_m_2248_, lean_object* v_00_u03b1_2249_, lean_object* v_00_u03b2_2250_, lean_object* v_n_2251_, lean_object* v_inst_2252_, lean_object* v_f_2253_, lean_object* v_as_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Vector_findSomeM_x3f(v_m_2248_, v_00_u03b1_2249_, v_00_u03b2_2250_, v_n_2251_, v_inst_2252_, v_f_2253_, v_as_2254_);
lean_dec(v_n_2251_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2256_, lean_object* v_a_2257_, uint8_t v_____do__lift_2258_){
_start:
{
if (v_____do__lift_2258_ == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_dec(v_a_2257_);
v___x_2259_ = lean_box(0);
v___x_2260_ = lean_apply_2(v_toPure_2256_, lean_box(0), v___x_2259_);
return v___x_2260_;
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2261_, 0, v_a_2257_);
v___x_2262_ = lean_apply_2(v_toPure_2256_, lean_box(0), v___x_2261_);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2263_, lean_object* v_a_2264_, lean_object* v_____do__lift_2265_){
_start:
{
uint8_t v_____do__lift_50__boxed_2266_; lean_object* v_res_2267_; 
v_____do__lift_50__boxed_2266_ = lean_unbox(v_____do__lift_2265_);
v_res_2267_ = l_Vector_findRevM_x3f___redArg___lam__0(v_toPure_2263_, v_a_2264_, v_____do__lift_50__boxed_2266_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2268_, lean_object* v_f_2269_, lean_object* v_toBind_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v___f_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_inc(v_a_2271_);
v___f_2272_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2272_, 0, v_toPure_2268_);
lean_closure_set(v___f_2272_, 1, v_a_2271_);
v___x_2273_ = lean_apply_1(v_f_2269_, v_a_2271_);
v___x_2274_ = lean_apply_4(v_toBind_2270_, lean_box(0), lean_box(0), v___x_2273_, v___f_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg(lean_object* v_inst_2275_, lean_object* v_f_2276_, lean_object* v_as_2277_){
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
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f(lean_object* v_n_2284_, lean_object* v_00_u03b1_2285_, lean_object* v_m_2286_, lean_object* v_inst_2287_, lean_object* v_f_2288_, lean_object* v_as_2289_){
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
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___boxed(lean_object* v_n_2296_, lean_object* v_00_u03b1_2297_, lean_object* v_m_2298_, lean_object* v_inst_2299_, lean_object* v_f_2300_, lean_object* v_as_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Vector_findRevM_x3f(v_n_2296_, v_00_u03b1_2297_, v_m_2298_, v_inst_2299_, v_f_2300_, v_as_2301_);
lean_dec(v_n_2296_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___redArg(lean_object* v_inst_2303_, lean_object* v_f_2304_, lean_object* v_as_2305_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_array_get_size(v_as_2305_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2303_, v_f_2304_, v_as_2305_, v___x_2306_, lean_box(0));
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f(lean_object* v_m_2308_, lean_object* v_00_u03b1_2309_, lean_object* v_00_u03b2_2310_, lean_object* v_n_2311_, lean_object* v_inst_2312_, lean_object* v_f_2313_, lean_object* v_as_2314_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_array_get_size(v_as_2314_);
v___x_2316_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2312_, v_f_2313_, v_as_2314_, v___x_2315_, lean_box(0));
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___boxed(lean_object* v_m_2317_, lean_object* v_00_u03b1_2318_, lean_object* v_00_u03b2_2319_, lean_object* v_n_2320_, lean_object* v_inst_2321_, lean_object* v_f_2322_, lean_object* v_as_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Vector_findSomeRevM_x3f(v_m_2317_, v_00_u03b1_2318_, v_00_u03b2_2319_, v_n_2320_, v_inst_2321_, v_f_2322_, v_as_2323_);
lean_dec(v_n_2320_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0(lean_object* v_f_2325_, lean_object* v___x_2326_, lean_object* v___x_2327_, lean_object* v_a_2328_, lean_object* v_x_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v___x_2331_; uint8_t v___x_2332_; 
lean_inc(v_a_2328_);
v___x_2331_ = lean_apply_1(v_f_2325_, v_a_2328_);
v___x_2332_ = lean_unbox(v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; 
lean_dec(v_a_2328_);
v___x_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2326_);
return v___x_2333_;
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec_ref(v___x_2326_);
v___x_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2334_, 0, v_a_2328_);
v___x_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
lean_ctor_set(v___x_2336_, 1, v___x_2327_);
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
return v___x_2337_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0___boxed(lean_object* v_f_2338_, lean_object* v___x_2339_, lean_object* v___x_2340_, lean_object* v_a_2341_, lean_object* v_x_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Vector_find_x3f___redArg___lam__0(v_f_2338_, v___x_2339_, v___x_2340_, v_a_2341_, v_x_2342_, v___y_2343_);
lean_dec_ref(v___y_2343_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg(lean_object* v_f_2345_, lean_object* v_as_2346_){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___f_2351_; size_t v_sz_2352_; size_t v___x_2353_; lean_object* v___x_2354_; lean_object* v_fst_2355_; 
v___x_2347_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2348_ = lean_box(0);
v___x_2349_ = lean_box(0);
v___x_2350_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2351_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2351_, 0, v_f_2345_);
lean_closure_set(v___f_2351_, 1, v___x_2350_);
lean_closure_set(v___f_2351_, 2, v___x_2349_);
v_sz_2352_ = lean_array_size(v_as_2346_);
v___x_2353_ = ((size_t)0ULL);
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2347_, v_as_2346_, v___f_2351_, v_sz_2352_, v___x_2353_, v___x_2350_);
v_fst_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_fst_2355_);
lean_dec(v___x_2354_);
if (lean_obj_tag(v_fst_2355_) == 0)
{
return v___x_2348_;
}
else
{
lean_object* v_val_2356_; 
v_val_2356_ = lean_ctor_get(v_fst_2355_, 0);
lean_inc(v_val_2356_);
lean_dec_ref_known(v_fst_2355_, 1);
return v_val_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f(lean_object* v_n_2357_, lean_object* v_00_u03b1_2358_, lean_object* v_f_2359_, lean_object* v_as_2360_){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___f_2365_; size_t v_sz_2366_; size_t v___x_2367_; lean_object* v___x_2368_; lean_object* v_fst_2369_; 
v___x_2361_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2362_ = lean_box(0);
v___x_2363_ = lean_box(0);
v___x_2364_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2365_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2365_, 0, v_f_2359_);
lean_closure_set(v___f_2365_, 1, v___x_2364_);
lean_closure_set(v___f_2365_, 2, v___x_2363_);
v_sz_2366_ = lean_array_size(v_as_2360_);
v___x_2367_ = ((size_t)0ULL);
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2361_, v_as_2360_, v___f_2365_, v_sz_2366_, v___x_2367_, v___x_2364_);
v_fst_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_fst_2369_);
lean_dec(v___x_2368_);
if (lean_obj_tag(v_fst_2369_) == 0)
{
return v___x_2362_;
}
else
{
lean_object* v_val_2370_; 
v_val_2370_ = lean_ctor_get(v_fst_2369_, 0);
lean_inc(v_val_2370_);
lean_dec_ref_known(v_fst_2369_, 1);
return v_val_2370_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___boxed(lean_object* v_n_2371_, lean_object* v_00_u03b1_2372_, lean_object* v_f_2373_, lean_object* v_as_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Vector_find_x3f(v_n_2371_, v_00_u03b1_2372_, v_f_2373_, v_as_2374_);
lean_dec(v_n_2371_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg___lam__0(lean_object* v_f_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2378_; uint8_t v___x_2379_; 
lean_inc(v_a_2377_);
v___x_2378_ = lean_apply_1(v_f_2376_, v_a_2377_);
v___x_2379_ = lean_unbox(v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
lean_dec(v_a_2377_);
v___x_2380_ = lean_box(0);
return v___x_2380_;
}
else
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2381_, 0, v_a_2377_);
return v___x_2381_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg(lean_object* v_f_2382_, lean_object* v_as_2383_){
_start:
{
lean_object* v___f_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___f_2384_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2384_, 0, v_f_2382_);
v___x_2385_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2386_ = lean_array_get_size(v_as_2383_);
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2385_, v___f_2384_, v_as_2383_, v___x_2386_, lean_box(0));
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f(lean_object* v_n_2388_, lean_object* v_00_u03b1_2389_, lean_object* v_f_2390_, lean_object* v_as_2391_){
_start:
{
lean_object* v___f_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___f_2392_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2392_, 0, v_f_2390_);
v___x_2393_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2394_ = lean_array_get_size(v_as_2391_);
v___x_2395_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2393_, v___f_2392_, v_as_2391_, v___x_2394_, lean_box(0));
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___boxed(lean_object* v_n_2396_, lean_object* v_00_u03b1_2397_, lean_object* v_f_2398_, lean_object* v_as_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Vector_findRev_x3f(v_n_2396_, v_00_u03b1_2397_, v_f_2398_, v_as_2399_);
lean_dec(v_n_2396_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0(lean_object* v_f_2401_, lean_object* v___x_2402_, lean_object* v___x_2403_, lean_object* v_a_2404_, lean_object* v_x_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = lean_apply_1(v_f_2401_, v_a_2404_);
if (lean_obj_tag(v___x_2407_) == 1)
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec_ref(v___x_2403_);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
lean_ctor_set(v___x_2409_, 1, v___x_2402_);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
else
{
lean_object* v___x_2411_; 
lean_dec(v___x_2407_);
v___x_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2403_);
return v___x_2411_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2412_, lean_object* v___x_2413_, lean_object* v___x_2414_, lean_object* v_a_2415_, lean_object* v_x_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Vector_findSome_x3f___redArg___lam__0(v_f_2412_, v___x_2413_, v___x_2414_, v_a_2415_, v_x_2416_, v___y_2417_);
lean_dec_ref(v___y_2417_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg(lean_object* v_f_2419_, lean_object* v_as_2420_){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___f_2425_; size_t v_sz_2426_; size_t v___x_2427_; lean_object* v___x_2428_; lean_object* v_fst_2429_; 
v___x_2421_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2422_ = lean_box(0);
v___x_2423_ = lean_box(0);
v___x_2424_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2425_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2425_, 0, v_f_2419_);
lean_closure_set(v___f_2425_, 1, v___x_2423_);
lean_closure_set(v___f_2425_, 2, v___x_2424_);
v_sz_2426_ = lean_array_size(v_as_2420_);
v___x_2427_ = ((size_t)0ULL);
v___x_2428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2421_, v_as_2420_, v___f_2425_, v_sz_2426_, v___x_2427_, v___x_2424_);
v_fst_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_fst_2429_);
lean_dec(v___x_2428_);
if (lean_obj_tag(v_fst_2429_) == 0)
{
return v___x_2422_;
}
else
{
lean_object* v_val_2430_; 
v_val_2430_ = lean_ctor_get(v_fst_2429_, 0);
lean_inc(v_val_2430_);
lean_dec_ref_known(v_fst_2429_, 1);
return v_val_2430_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f(lean_object* v_00_u03b1_2431_, lean_object* v_00_u03b2_2432_, lean_object* v_n_2433_, lean_object* v_f_2434_, lean_object* v_as_2435_){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___f_2440_; size_t v_sz_2441_; size_t v___x_2442_; lean_object* v___x_2443_; lean_object* v_fst_2444_; 
v___x_2436_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2437_ = lean_box(0);
v___x_2438_ = lean_box(0);
v___x_2439_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2440_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2440_, 0, v_f_2434_);
lean_closure_set(v___f_2440_, 1, v___x_2438_);
lean_closure_set(v___f_2440_, 2, v___x_2439_);
v_sz_2441_ = lean_array_size(v_as_2435_);
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2436_, v_as_2435_, v___f_2440_, v_sz_2441_, v___x_2442_, v___x_2439_);
v_fst_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_fst_2444_);
lean_dec(v___x_2443_);
if (lean_obj_tag(v_fst_2444_) == 0)
{
return v___x_2437_;
}
else
{
lean_object* v_val_2445_; 
v_val_2445_ = lean_ctor_get(v_fst_2444_, 0);
lean_inc(v_val_2445_);
lean_dec_ref_known(v_fst_2444_, 1);
return v_val_2445_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___boxed(lean_object* v_00_u03b1_2446_, lean_object* v_00_u03b2_2447_, lean_object* v_n_2448_, lean_object* v_f_2449_, lean_object* v_as_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Vector_findSome_x3f(v_00_u03b1_2446_, v_00_u03b2_2447_, v_n_2448_, v_f_2449_, v_as_2450_);
lean_dec(v_n_2448_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2452_, lean_object* v_x_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_apply_1(v_f_2452_, v_x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg(lean_object* v_f_2455_, lean_object* v_as_2456_){
_start:
{
lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___f_2457_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2457_, 0, v_f_2455_);
v___x_2458_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2459_ = lean_array_get_size(v_as_2456_);
v___x_2460_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2458_, v___f_2457_, v_as_2456_, v___x_2459_, lean_box(0));
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f(lean_object* v_00_u03b1_2461_, lean_object* v_00_u03b2_2462_, lean_object* v_n_2463_, lean_object* v_f_2464_, lean_object* v_as_2465_){
_start:
{
lean_object* v___f_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___f_2466_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2466_, 0, v_f_2464_);
v___x_2467_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2468_ = lean_array_get_size(v_as_2465_);
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2467_, v___f_2466_, v_as_2465_, v___x_2468_, lean_box(0));
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___boxed(lean_object* v_00_u03b1_2470_, lean_object* v_00_u03b2_2471_, lean_object* v_n_2472_, lean_object* v_f_2473_, lean_object* v_as_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Vector_findSomeRev_x3f(v_00_u03b1_2470_, v_00_u03b2_2471_, v_n_2472_, v_f_2473_, v_as_2474_);
lean_dec(v_n_2472_);
return v_res_2475_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf___redArg(lean_object* v_inst_2476_, lean_object* v_xs_2477_, lean_object* v_ys_2478_){
_start:
{
uint8_t v___x_2479_; 
v___x_2479_ = l_Array_isPrefixOf___redArg(v_inst_2476_, v_xs_2477_, v_ys_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___redArg___boxed(lean_object* v_inst_2480_, lean_object* v_xs_2481_, lean_object* v_ys_2482_){
_start:
{
uint8_t v_res_2483_; lean_object* v_r_2484_; 
v_res_2483_ = l_Vector_isPrefixOf___redArg(v_inst_2480_, v_xs_2481_, v_ys_2482_);
lean_dec_ref(v_ys_2482_);
lean_dec_ref(v_xs_2481_);
v_r_2484_ = lean_box(v_res_2483_);
return v_r_2484_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf(lean_object* v_00_u03b1_2485_, lean_object* v_m_2486_, lean_object* v_n_2487_, lean_object* v_inst_2488_, lean_object* v_xs_2489_, lean_object* v_ys_2490_){
_start:
{
uint8_t v___x_2491_; 
v___x_2491_ = l_Array_isPrefixOf___redArg(v_inst_2488_, v_xs_2489_, v_ys_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___boxed(lean_object* v_00_u03b1_2492_, lean_object* v_m_2493_, lean_object* v_n_2494_, lean_object* v_inst_2495_, lean_object* v_xs_2496_, lean_object* v_ys_2497_){
_start:
{
uint8_t v_res_2498_; lean_object* v_r_2499_; 
v_res_2498_ = l_Vector_isPrefixOf(v_00_u03b1_2492_, v_m_2493_, v_n_2494_, v_inst_2495_, v_xs_2496_, v_ys_2497_);
lean_dec_ref(v_ys_2497_);
lean_dec_ref(v_xs_2496_);
lean_dec(v_n_2494_);
lean_dec(v_m_2493_);
v_r_2499_ = lean_box(v_res_2498_);
return v_r_2499_;
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___redArg(lean_object* v_inst_2500_, lean_object* v_p_2501_, lean_object* v_xs_2502_){
_start:
{
lean_object* v_toApplicative_2503_; lean_object* v_toPure_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v_toApplicative_2503_ = lean_ctor_get(v_inst_2500_, 0);
v_toPure_2504_ = lean_ctor_get(v_toApplicative_2503_, 1);
v___x_2505_ = lean_unsigned_to_nat(0u);
v___x_2506_ = lean_array_get_size(v_xs_2502_);
v___x_2507_ = lean_nat_dec_lt(v___x_2505_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_inc(v_toPure_2504_);
lean_dec_ref(v_xs_2502_);
lean_dec(v_p_2501_);
lean_dec_ref(v_inst_2500_);
v___x_2508_ = lean_box(v___x_2507_);
v___x_2509_ = lean_apply_2(v_toPure_2504_, lean_box(0), v___x_2508_);
return v___x_2509_;
}
else
{
if (v___x_2507_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_inc(v_toPure_2504_);
lean_dec_ref(v_xs_2502_);
lean_dec(v_p_2501_);
lean_dec_ref(v_inst_2500_);
v___x_2510_ = lean_box(v___x_2507_);
v___x_2511_ = lean_apply_2(v_toPure_2504_, lean_box(0), v___x_2510_);
return v___x_2511_;
}
else
{
size_t v___x_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = lean_usize_of_nat(v___x_2506_);
v___x_2514_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2500_, v_p_2501_, v_xs_2502_, v___x_2512_, v___x_2513_);
return v___x_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM(lean_object* v_m_2515_, lean_object* v_00_u03b1_2516_, lean_object* v_n_2517_, lean_object* v_inst_2518_, lean_object* v_p_2519_, lean_object* v_xs_2520_){
_start:
{
lean_object* v_toApplicative_2521_; lean_object* v_toPure_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v_toApplicative_2521_ = lean_ctor_get(v_inst_2518_, 0);
v_toPure_2522_ = lean_ctor_get(v_toApplicative_2521_, 1);
v___x_2523_ = lean_unsigned_to_nat(0u);
v___x_2524_ = lean_array_get_size(v_xs_2520_);
v___x_2525_ = lean_nat_dec_lt(v___x_2523_, v___x_2524_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_inc(v_toPure_2522_);
lean_dec_ref(v_xs_2520_);
lean_dec(v_p_2519_);
lean_dec_ref(v_inst_2518_);
v___x_2526_ = lean_box(v___x_2525_);
v___x_2527_ = lean_apply_2(v_toPure_2522_, lean_box(0), v___x_2526_);
return v___x_2527_;
}
else
{
if (v___x_2525_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_inc(v_toPure_2522_);
lean_dec_ref(v_xs_2520_);
lean_dec(v_p_2519_);
lean_dec_ref(v_inst_2518_);
v___x_2528_ = lean_box(v___x_2525_);
v___x_2529_ = lean_apply_2(v_toPure_2522_, lean_box(0), v___x_2528_);
return v___x_2529_;
}
else
{
size_t v___x_2530_; size_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = ((size_t)0ULL);
v___x_2531_ = lean_usize_of_nat(v___x_2524_);
v___x_2532_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2518_, v_p_2519_, v_xs_2520_, v___x_2530_, v___x_2531_);
return v___x_2532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___boxed(lean_object* v_m_2533_, lean_object* v_00_u03b1_2534_, lean_object* v_n_2535_, lean_object* v_inst_2536_, lean_object* v_p_2537_, lean_object* v_xs_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Vector_anyM(v_m_2533_, v_00_u03b1_2534_, v_n_2535_, v_inst_2536_, v_p_2537_, v_xs_2538_);
lean_dec(v_n_2535_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0(lean_object* v_toPure_2540_, uint8_t v_____do__lift_2541_){
_start:
{
if (v_____do__lift_2541_ == 0)
{
uint8_t v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = 1;
v___x_2543_ = lean_box(v___x_2542_);
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
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0___boxed(lean_object* v_toPure_2548_, lean_object* v_____do__lift_2549_){
_start:
{
uint8_t v_____do__lift_112__boxed_2550_; lean_object* v_res_2551_; 
v_____do__lift_112__boxed_2550_ = lean_unbox(v_____do__lift_2549_);
v_res_2551_ = l_Vector_allM___redArg___lam__0(v_toPure_2548_, v_____do__lift_112__boxed_2550_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1(lean_object* v_toPure_2552_, uint8_t v___x_2553_, uint8_t v_____do__lift_2554_){
_start:
{
if (v_____do__lift_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_box(v___x_2553_);
v___x_2556_ = lean_apply_2(v_toPure_2552_, lean_box(0), v___x_2555_);
return v___x_2556_;
}
else
{
uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = 0;
v___x_2558_ = lean_box(v___x_2557_);
v___x_2559_ = lean_apply_2(v_toPure_2552_, lean_box(0), v___x_2558_);
return v___x_2559_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1___boxed(lean_object* v_toPure_2560_, lean_object* v___x_2561_, lean_object* v_____do__lift_2562_){
_start:
{
uint8_t v___x_127__boxed_2563_; uint8_t v_____do__lift_128__boxed_2564_; lean_object* v_res_2565_; 
v___x_127__boxed_2563_ = lean_unbox(v___x_2561_);
v_____do__lift_128__boxed_2564_ = lean_unbox(v_____do__lift_2562_);
v_res_2565_ = l_Vector_allM___redArg___lam__1(v_toPure_2560_, v___x_127__boxed_2563_, v_____do__lift_128__boxed_2564_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__2(lean_object* v_p_2566_, lean_object* v_toBind_2567_, lean_object* v___f_2568_, lean_object* v_v_2569_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_apply_1(v_p_2566_, v_v_2569_);
v___x_2571_ = lean_apply_4(v_toBind_2567_, lean_box(0), lean_box(0), v___x_2570_, v___f_2568_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg(lean_object* v_inst_2572_, lean_object* v_p_2573_, lean_object* v_xs_2574_){
_start:
{
lean_object* v_toApplicative_2575_; lean_object* v_toBind_2576_; lean_object* v_toPure_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___f_2580_; uint8_t v___x_2581_; 
v_toApplicative_2575_ = lean_ctor_get(v_inst_2572_, 0);
v_toBind_2576_ = lean_ctor_get(v_inst_2572_, 1);
lean_inc(v_toBind_2576_);
v_toPure_2577_ = lean_ctor_get(v_toApplicative_2575_, 1);
v___x_2578_ = lean_unsigned_to_nat(0u);
v___x_2579_ = lean_array_get_size(v_xs_2574_);
lean_inc(v_toPure_2577_);
v___f_2580_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2580_, 0, v_toPure_2577_);
v___x_2581_ = lean_nat_dec_lt(v___x_2578_, v___x_2579_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_inc(v_toPure_2577_);
lean_dec_ref(v_xs_2574_);
lean_dec(v_p_2573_);
lean_dec_ref(v_inst_2572_);
v___x_2582_ = lean_box(v___x_2581_);
v___x_2583_ = lean_apply_2(v_toPure_2577_, lean_box(0), v___x_2582_);
v___x_2584_ = lean_apply_4(v_toBind_2576_, lean_box(0), lean_box(0), v___x_2583_, v___f_2580_);
return v___x_2584_;
}
else
{
if (v___x_2581_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_inc(v_toPure_2577_);
lean_dec_ref(v_xs_2574_);
lean_dec(v_p_2573_);
lean_dec_ref(v_inst_2572_);
v___x_2585_ = lean_box(v___x_2581_);
v___x_2586_ = lean_apply_2(v_toPure_2577_, lean_box(0), v___x_2585_);
v___x_2587_ = lean_apply_4(v_toBind_2576_, lean_box(0), lean_box(0), v___x_2586_, v___f_2580_);
return v___x_2587_;
}
else
{
lean_object* v___x_2588_; lean_object* v___f_2589_; lean_object* v___f_2590_; size_t v___x_2591_; size_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2588_ = lean_box(v___x_2581_);
lean_inc(v_toPure_2577_);
v___f_2589_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2589_, 0, v_toPure_2577_);
lean_closure_set(v___f_2589_, 1, v___x_2588_);
lean_inc(v_toBind_2576_);
v___f_2590_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2590_, 0, v_p_2573_);
lean_closure_set(v___f_2590_, 1, v_toBind_2576_);
lean_closure_set(v___f_2590_, 2, v___f_2589_);
v___x_2591_ = ((size_t)0ULL);
v___x_2592_ = lean_usize_of_nat(v___x_2579_);
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2572_, v___f_2590_, v_xs_2574_, v___x_2591_, v___x_2592_);
v___x_2594_ = lean_apply_4(v_toBind_2576_, lean_box(0), lean_box(0), v___x_2593_, v___f_2580_);
return v___x_2594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM(lean_object* v_m_2595_, lean_object* v_00_u03b1_2596_, lean_object* v_n_2597_, lean_object* v_inst_2598_, lean_object* v_p_2599_, lean_object* v_xs_2600_){
_start:
{
lean_object* v_toApplicative_2601_; lean_object* v_toBind_2602_; lean_object* v_toPure_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___f_2606_; uint8_t v___x_2607_; 
v_toApplicative_2601_ = lean_ctor_get(v_inst_2598_, 0);
v_toBind_2602_ = lean_ctor_get(v_inst_2598_, 1);
lean_inc(v_toBind_2602_);
v_toPure_2603_ = lean_ctor_get(v_toApplicative_2601_, 1);
v___x_2604_ = lean_unsigned_to_nat(0u);
v___x_2605_ = lean_array_get_size(v_xs_2600_);
lean_inc(v_toPure_2603_);
v___f_2606_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2606_, 0, v_toPure_2603_);
v___x_2607_ = lean_nat_dec_lt(v___x_2604_, v___x_2605_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_inc(v_toPure_2603_);
lean_dec_ref(v_xs_2600_);
lean_dec(v_p_2599_);
lean_dec_ref(v_inst_2598_);
v___x_2608_ = lean_box(v___x_2607_);
v___x_2609_ = lean_apply_2(v_toPure_2603_, lean_box(0), v___x_2608_);
v___x_2610_ = lean_apply_4(v_toBind_2602_, lean_box(0), lean_box(0), v___x_2609_, v___f_2606_);
return v___x_2610_;
}
else
{
if (v___x_2607_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_inc(v_toPure_2603_);
lean_dec_ref(v_xs_2600_);
lean_dec(v_p_2599_);
lean_dec_ref(v_inst_2598_);
v___x_2611_ = lean_box(v___x_2607_);
v___x_2612_ = lean_apply_2(v_toPure_2603_, lean_box(0), v___x_2611_);
v___x_2613_ = lean_apply_4(v_toBind_2602_, lean_box(0), lean_box(0), v___x_2612_, v___f_2606_);
return v___x_2613_;
}
else
{
lean_object* v___x_2614_; lean_object* v___f_2615_; lean_object* v___f_2616_; size_t v___x_2617_; size_t v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2614_ = lean_box(v___x_2607_);
lean_inc(v_toPure_2603_);
v___f_2615_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2615_, 0, v_toPure_2603_);
lean_closure_set(v___f_2615_, 1, v___x_2614_);
lean_inc(v_toBind_2602_);
v___f_2616_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2616_, 0, v_p_2599_);
lean_closure_set(v___f_2616_, 1, v_toBind_2602_);
lean_closure_set(v___f_2616_, 2, v___f_2615_);
v___x_2617_ = ((size_t)0ULL);
v___x_2618_ = lean_usize_of_nat(v___x_2605_);
v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2598_, v___f_2616_, v_xs_2600_, v___x_2617_, v___x_2618_);
v___x_2620_ = lean_apply_4(v_toBind_2602_, lean_box(0), lean_box(0), v___x_2619_, v___f_2606_);
return v___x_2620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___boxed(lean_object* v_m_2621_, lean_object* v_00_u03b1_2622_, lean_object* v_n_2623_, lean_object* v_inst_2624_, lean_object* v_p_2625_, lean_object* v_xs_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Vector_allM(v_m_2621_, v_00_u03b1_2622_, v_n_2623_, v_inst_2624_, v_p_2625_, v_xs_2626_);
lean_dec(v_n_2623_);
return v_res_2627_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg___lam__0(lean_object* v_p_2628_, lean_object* v_x_2629_){
_start:
{
lean_object* v___x_2630_; uint8_t v___x_2631_; 
v___x_2630_ = lean_apply_1(v_p_2628_, v_x_2629_);
v___x_2631_ = lean_unbox(v___x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___lam__0___boxed(lean_object* v_p_2632_, lean_object* v_x_2633_){
_start:
{
uint8_t v_res_2634_; lean_object* v_r_2635_; 
v_res_2634_ = l_Vector_any___redArg___lam__0(v_p_2632_, v_x_2633_);
v_r_2635_ = lean_box(v_res_2634_);
return v_r_2635_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg(lean_object* v_xs_2636_, lean_object* v_p_2637_){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = lean_array_get_size(v_xs_2636_);
v___x_2640_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2641_ = lean_nat_dec_lt(v___x_2638_, v___x_2639_);
if (v___x_2641_ == 0)
{
lean_dec_ref(v_p_2637_);
lean_dec_ref(v_xs_2636_);
return v___x_2641_;
}
else
{
if (v___x_2641_ == 0)
{
lean_dec_ref(v_p_2637_);
lean_dec_ref(v_xs_2636_);
return v___x_2641_;
}
else
{
lean_object* v___f_2642_; size_t v___x_2643_; size_t v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___f_2642_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2642_, 0, v_p_2637_);
v___x_2643_ = ((size_t)0ULL);
v___x_2644_ = lean_usize_of_nat(v___x_2639_);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2640_, v___f_2642_, v_xs_2636_, v___x_2643_, v___x_2644_);
v___x_2646_ = lean_unbox(v___x_2645_);
lean_dec(v___x_2645_);
return v___x_2646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___boxed(lean_object* v_xs_2647_, lean_object* v_p_2648_){
_start:
{
uint8_t v_res_2649_; lean_object* v_r_2650_; 
v_res_2649_ = l_Vector_any___redArg(v_xs_2647_, v_p_2648_);
v_r_2650_ = lean_box(v_res_2649_);
return v_r_2650_;
}
}
LEAN_EXPORT uint8_t l_Vector_any(lean_object* v_00_u03b1_2651_, lean_object* v_n_2652_, lean_object* v_xs_2653_, lean_object* v_p_2654_){
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
LEAN_EXPORT lean_object* l_Vector_any___boxed(lean_object* v_00_u03b1_2664_, lean_object* v_n_2665_, lean_object* v_xs_2666_, lean_object* v_p_2667_){
_start:
{
uint8_t v_res_2668_; lean_object* v_r_2669_; 
v_res_2668_ = l_Vector_any(v_00_u03b1_2664_, v_n_2665_, v_xs_2666_, v_p_2667_);
lean_dec(v_n_2665_);
v_r_2669_ = lean_box(v_res_2668_);
return v_r_2669_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg___lam__0(lean_object* v_p_2670_, uint8_t v___x_2671_, lean_object* v_v_2672_){
_start:
{
lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2673_ = lean_apply_1(v_p_2670_, v_v_2672_);
v___x_2674_ = lean_unbox(v___x_2673_);
if (v___x_2674_ == 0)
{
return v___x_2671_;
}
else
{
uint8_t v___x_2675_; 
v___x_2675_ = 0;
return v___x_2675_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___lam__0___boxed(lean_object* v_p_2676_, lean_object* v___x_2677_, lean_object* v_v_2678_){
_start:
{
uint8_t v___x_75__boxed_2679_; uint8_t v_res_2680_; lean_object* v_r_2681_; 
v___x_75__boxed_2679_ = lean_unbox(v___x_2677_);
v_res_2680_ = l_Vector_all___redArg___lam__0(v_p_2676_, v___x_75__boxed_2679_, v_v_2678_);
v_r_2681_ = lean_box(v_res_2680_);
return v_r_2681_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg(lean_object* v_xs_2682_, lean_object* v_p_2683_){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2684_ = lean_unsigned_to_nat(0u);
v___x_2685_ = lean_array_get_size(v_xs_2682_);
v___x_2686_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2687_ = lean_nat_dec_lt(v___x_2684_, v___x_2685_);
if (v___x_2687_ == 0)
{
uint8_t v___x_2688_; 
lean_dec_ref(v_p_2683_);
lean_dec_ref(v_xs_2682_);
v___x_2688_ = 1;
return v___x_2688_;
}
else
{
if (v___x_2687_ == 0)
{
lean_dec_ref(v_p_2683_);
lean_dec_ref(v_xs_2682_);
return v___x_2687_;
}
else
{
lean_object* v___x_2689_; lean_object* v___f_2690_; size_t v___x_2691_; size_t v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2689_ = lean_box(v___x_2687_);
v___f_2690_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2690_, 0, v_p_2683_);
lean_closure_set(v___f_2690_, 1, v___x_2689_);
v___x_2691_ = ((size_t)0ULL);
v___x_2692_ = lean_usize_of_nat(v___x_2685_);
v___x_2693_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2686_, v___f_2690_, v_xs_2682_, v___x_2691_, v___x_2692_);
v___x_2694_ = lean_unbox(v___x_2693_);
lean_dec(v___x_2693_);
if (v___x_2694_ == 0)
{
return v___x_2687_;
}
else
{
uint8_t v___x_2695_; 
v___x_2695_ = 0;
return v___x_2695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___boxed(lean_object* v_xs_2696_, lean_object* v_p_2697_){
_start:
{
uint8_t v_res_2698_; lean_object* v_r_2699_; 
v_res_2698_ = l_Vector_all___redArg(v_xs_2696_, v_p_2697_);
v_r_2699_ = lean_box(v_res_2698_);
return v_r_2699_;
}
}
LEAN_EXPORT uint8_t l_Vector_all(lean_object* v_00_u03b1_2700_, lean_object* v_n_2701_, lean_object* v_xs_2702_, lean_object* v_p_2703_){
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
LEAN_EXPORT lean_object* l_Vector_all___boxed(lean_object* v_00_u03b1_2716_, lean_object* v_n_2717_, lean_object* v_xs_2718_, lean_object* v_p_2719_){
_start:
{
uint8_t v_res_2720_; lean_object* v_r_2721_; 
v_res_2720_ = l_Vector_all(v_00_u03b1_2716_, v_n_2717_, v_xs_2718_, v_p_2719_);
lean_dec(v_n_2717_);
v_r_2721_ = lean_box(v_res_2720_);
return v_r_2721_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0(lean_object* v_p_2722_, lean_object* v_x1_2723_, lean_object* v_x2_2724_){
_start:
{
lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = lean_apply_1(v_p_2722_, v_x1_2723_);
v___x_2726_ = lean_unbox(v___x_2725_);
if (v___x_2726_ == 0)
{
lean_inc(v_x2_2724_);
return v_x2_2724_;
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = lean_unsigned_to_nat(1u);
v___x_2728_ = lean_nat_add(v_x2_2724_, v___x_2727_);
return v___x_2728_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0___boxed(lean_object* v_p_2729_, lean_object* v_x1_2730_, lean_object* v_x2_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Vector_countP___redArg___lam__0(v_p_2729_, v_x1_2730_, v_x2_2731_);
lean_dec(v_x2_2731_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg(lean_object* v_p_2733_, lean_object* v_xs_2734_){
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
LEAN_EXPORT lean_object* l_Vector_countP(lean_object* v_00_u03b1_2743_, lean_object* v_n_2744_, lean_object* v_p_2745_, lean_object* v_xs_2746_){
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
lean_dec_ref(v_p_2745_);
return v___x_2747_;
}
else
{
lean_object* v___f_2751_; size_t v___x_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
v___f_2751_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2751_, 0, v_p_2745_);
v___x_2752_ = lean_usize_of_nat(v___x_2748_);
v___x_2753_ = ((size_t)0ULL);
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2749_, v___f_2751_, v_xs_2746_, v___x_2752_, v___x_2753_, v___x_2747_);
return v___x_2754_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_n_2756_, lean_object* v_p_2757_, lean_object* v_xs_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Vector_countP(v_00_u03b1_2755_, v_n_2756_, v_p_2757_, v_xs_2758_);
lean_dec(v_n_2756_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0(lean_object* v_inst_2760_, lean_object* v_a_2761_, lean_object* v_x1_2762_, lean_object* v_x2_2763_){
_start:
{
lean_object* v___x_2764_; uint8_t v___x_2765_; 
v___x_2764_ = lean_apply_2(v_inst_2760_, v_x1_2762_, v_a_2761_);
v___x_2765_ = lean_unbox(v___x_2764_);
if (v___x_2765_ == 0)
{
lean_inc(v_x2_2763_);
return v_x2_2763_;
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_unsigned_to_nat(1u);
v___x_2767_ = lean_nat_add(v_x2_2763_, v___x_2766_);
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0___boxed(lean_object* v_inst_2768_, lean_object* v_a_2769_, lean_object* v_x1_2770_, lean_object* v_x2_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Vector_count___redArg___lam__0(v_inst_2768_, v_a_2769_, v_x1_2770_, v_x2_2771_);
lean_dec(v_x2_2771_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg(lean_object* v_inst_2773_, lean_object* v_a_2774_, lean_object* v_xs_2775_){
_start:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2776_ = lean_unsigned_to_nat(0u);
v___x_2777_ = lean_array_get_size(v_xs_2775_);
v___x_2778_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2779_ = lean_nat_dec_lt(v___x_2776_, v___x_2777_);
if (v___x_2779_ == 0)
{
lean_dec_ref(v_xs_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_inst_2773_);
return v___x_2776_;
}
else
{
lean_object* v___f_2780_; size_t v___x_2781_; size_t v___x_2782_; lean_object* v___x_2783_; 
v___f_2780_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2780_, 0, v_inst_2773_);
lean_closure_set(v___f_2780_, 1, v_a_2774_);
v___x_2781_ = lean_usize_of_nat(v___x_2777_);
v___x_2782_ = ((size_t)0ULL);
v___x_2783_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2778_, v___f_2780_, v_xs_2775_, v___x_2781_, v___x_2782_, v___x_2776_);
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count(lean_object* v_00_u03b1_2784_, lean_object* v_n_2785_, lean_object* v_inst_2786_, lean_object* v_a_2787_, lean_object* v_xs_2788_){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2789_ = lean_unsigned_to_nat(0u);
v___x_2790_ = lean_array_get_size(v_xs_2788_);
v___x_2791_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2792_ = lean_nat_dec_lt(v___x_2789_, v___x_2790_);
if (v___x_2792_ == 0)
{
lean_dec_ref(v_xs_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_inst_2786_);
return v___x_2789_;
}
else
{
lean_object* v___f_2793_; size_t v___x_2794_; size_t v___x_2795_; lean_object* v___x_2796_; 
v___f_2793_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2793_, 0, v_inst_2786_);
lean_closure_set(v___f_2793_, 1, v_a_2787_);
v___x_2794_ = lean_usize_of_nat(v___x_2790_);
v___x_2795_ = ((size_t)0ULL);
v___x_2796_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2791_, v___f_2793_, v_xs_2788_, v___x_2794_, v___x_2795_, v___x_2789_);
return v___x_2796_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___boxed(lean_object* v_00_u03b1_2797_, lean_object* v_n_2798_, lean_object* v_inst_2799_, lean_object* v_a_2800_, lean_object* v_xs_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Vector_count(v_00_u03b1_2797_, v_n_2798_, v_inst_2799_, v_a_2800_, v_xs_2801_);
lean_dec(v_n_2798_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___redArg(lean_object* v_inst_2803_, lean_object* v_xs_2804_, lean_object* v_a_2805_, lean_object* v_b_2806_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Array_replace___redArg(v_inst_2803_, v_xs_2804_, v_a_2805_, v_b_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace(lean_object* v_00_u03b1_2808_, lean_object* v_n_2809_, lean_object* v_inst_2810_, lean_object* v_xs_2811_, lean_object* v_a_2812_, lean_object* v_b_2813_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Array_replace___redArg(v_inst_2810_, v_xs_2811_, v_a_2812_, v_b_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___boxed(lean_object* v_00_u03b1_2815_, lean_object* v_n_2816_, lean_object* v_inst_2817_, lean_object* v_xs_2818_, lean_object* v_a_2819_, lean_object* v_b_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Vector_replace(v_00_u03b1_2815_, v_n_2816_, v_inst_2817_, v_xs_2818_, v_a_2819_, v_b_2820_);
lean_dec(v_n_2816_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg___lam__0(lean_object* v_inst_2822_, lean_object* v_x1_2823_, lean_object* v_x2_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = lean_apply_2(v_inst_2822_, v_x1_2823_, v_x2_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg(lean_object* v_inst_2826_, lean_object* v_inst_2827_, lean_object* v_xs_2828_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2829_ = lean_array_get_size(v_xs_2828_);
v___x_2830_ = lean_unsigned_to_nat(0u);
v___x_2831_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2832_ = lean_nat_dec_lt(v___x_2830_, v___x_2829_);
if (v___x_2832_ == 0)
{
lean_dec_ref(v_xs_2828_);
lean_dec(v_inst_2826_);
return v_inst_2827_;
}
else
{
lean_object* v___f_2833_; size_t v___x_2834_; size_t v___x_2835_; lean_object* v___x_2836_; 
v___f_2833_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2833_, 0, v_inst_2826_);
v___x_2834_ = lean_usize_of_nat(v___x_2829_);
v___x_2835_ = ((size_t)0ULL);
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2831_, v___f_2833_, v_xs_2828_, v___x_2834_, v___x_2835_, v_inst_2827_);
return v___x_2836_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum(lean_object* v_00_u03b1_2837_, lean_object* v_n_2838_, lean_object* v_inst_2839_, lean_object* v_inst_2840_, lean_object* v_xs_2841_){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v___x_2842_ = lean_array_get_size(v_xs_2841_);
v___x_2843_ = lean_unsigned_to_nat(0u);
v___x_2844_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2845_ = lean_nat_dec_lt(v___x_2843_, v___x_2842_);
if (v___x_2845_ == 0)
{
lean_dec_ref(v_xs_2841_);
lean_dec(v_inst_2839_);
return v_inst_2840_;
}
else
{
lean_object* v___f_2846_; size_t v___x_2847_; size_t v___x_2848_; lean_object* v___x_2849_; 
v___f_2846_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2846_, 0, v_inst_2839_);
v___x_2847_ = lean_usize_of_nat(v___x_2842_);
v___x_2848_ = ((size_t)0ULL);
v___x_2849_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2844_, v___f_2846_, v_xs_2841_, v___x_2847_, v___x_2848_, v_inst_2840_);
return v___x_2849_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum___boxed(lean_object* v_00_u03b1_2850_, lean_object* v_n_2851_, lean_object* v_inst_2852_, lean_object* v_inst_2853_, lean_object* v_xs_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Vector_sum(v_00_u03b1_2850_, v_n_2851_, v_inst_2852_, v_inst_2853_, v_xs_2854_);
lean_dec(v_n_2851_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Vector_prod___redArg(lean_object* v_inst_2856_, lean_object* v_inst_2857_, lean_object* v_xs_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v___x_2859_ = lean_array_get_size(v_xs_2858_);
v___x_2860_ = lean_unsigned_to_nat(0u);
v___x_2861_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2862_ = lean_nat_dec_lt(v___x_2860_, v___x_2859_);
if (v___x_2862_ == 0)
{
lean_dec_ref(v_xs_2858_);
lean_dec(v_inst_2856_);
return v_inst_2857_;
}
else
{
lean_object* v___f_2863_; size_t v___x_2864_; size_t v___x_2865_; lean_object* v___x_2866_; 
v___f_2863_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2863_, 0, v_inst_2856_);
v___x_2864_ = lean_usize_of_nat(v___x_2859_);
v___x_2865_ = ((size_t)0ULL);
v___x_2866_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2861_, v___f_2863_, v_xs_2858_, v___x_2864_, v___x_2865_, v_inst_2857_);
return v___x_2866_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod(lean_object* v_00_u03b1_2867_, lean_object* v_n_2868_, lean_object* v_inst_2869_, lean_object* v_inst_2870_, lean_object* v_xs_2871_){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2872_ = lean_array_get_size(v_xs_2871_);
v___x_2873_ = lean_unsigned_to_nat(0u);
v___x_2874_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2875_ = lean_nat_dec_lt(v___x_2873_, v___x_2872_);
if (v___x_2875_ == 0)
{
lean_dec_ref(v_xs_2871_);
lean_dec(v_inst_2869_);
return v_inst_2870_;
}
else
{
lean_object* v___f_2876_; size_t v___x_2877_; size_t v___x_2878_; lean_object* v___x_2879_; 
v___f_2876_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2876_, 0, v_inst_2869_);
v___x_2877_ = lean_usize_of_nat(v___x_2872_);
v___x_2878_ = ((size_t)0ULL);
v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2874_, v___f_2876_, v_xs_2871_, v___x_2877_, v___x_2878_, v_inst_2870_);
return v___x_2879_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod___boxed(lean_object* v_00_u03b1_2880_, lean_object* v_n_2881_, lean_object* v_inst_2882_, lean_object* v_inst_2883_, lean_object* v_xs_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Vector_prod(v_00_u03b1_2880_, v_n_2881_, v_inst_2882_, v_inst_2883_, v_xs_2884_);
lean_dec(v_n_2881_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg(lean_object* v_m_2886_, lean_object* v_n_2887_, lean_object* v_a_2888_, lean_object* v_xs_2889_){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2890_ = lean_nat_sub(v_n_2887_, v_m_2886_);
v___x_2891_ = lean_mk_array(v___x_2890_, v_a_2888_);
v___x_2892_ = l_Array_append___redArg(v___x_2891_, v_xs_2889_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg___boxed(lean_object* v_m_2893_, lean_object* v_n_2894_, lean_object* v_a_2895_, lean_object* v_xs_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Vector_leftpad___redArg(v_m_2893_, v_n_2894_, v_a_2895_, v_xs_2896_);
lean_dec_ref(v_xs_2896_);
lean_dec(v_n_2894_);
lean_dec(v_m_2893_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad(lean_object* v_00_u03b1_2898_, lean_object* v_m_2899_, lean_object* v_n_2900_, lean_object* v_a_2901_, lean_object* v_xs_2902_){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = lean_nat_sub(v_n_2900_, v_m_2899_);
v___x_2904_ = lean_mk_array(v___x_2903_, v_a_2901_);
v___x_2905_ = l_Array_append___redArg(v___x_2904_, v_xs_2902_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___boxed(lean_object* v_00_u03b1_2906_, lean_object* v_m_2907_, lean_object* v_n_2908_, lean_object* v_a_2909_, lean_object* v_xs_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Vector_leftpad(v_00_u03b1_2906_, v_m_2907_, v_n_2908_, v_a_2909_, v_xs_2910_);
lean_dec_ref(v_xs_2910_);
lean_dec(v_n_2908_);
lean_dec(v_m_2907_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg(lean_object* v_m_2912_, lean_object* v_n_2913_, lean_object* v_a_2914_, lean_object* v_xs_2915_){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2916_ = lean_nat_sub(v_n_2913_, v_m_2912_);
v___x_2917_ = lean_mk_array(v___x_2916_, v_a_2914_);
v___x_2918_ = l_Array_append___redArg(v_xs_2915_, v___x_2917_);
lean_dec_ref(v___x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg___boxed(lean_object* v_m_2919_, lean_object* v_n_2920_, lean_object* v_a_2921_, lean_object* v_xs_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Vector_rightpad___redArg(v_m_2919_, v_n_2920_, v_a_2921_, v_xs_2922_);
lean_dec(v_n_2920_);
lean_dec(v_m_2919_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad(lean_object* v_00_u03b1_2924_, lean_object* v_m_2925_, lean_object* v_n_2926_, lean_object* v_a_2927_, lean_object* v_xs_2928_){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = lean_nat_sub(v_n_2926_, v_m_2925_);
v___x_2930_ = lean_mk_array(v___x_2929_, v_a_2927_);
v___x_2931_ = l_Array_append___redArg(v_xs_2928_, v___x_2930_);
lean_dec_ref(v___x_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___boxed(lean_object* v_00_u03b1_2932_, lean_object* v_m_2933_, lean_object* v_n_2934_, lean_object* v_a_2935_, lean_object* v_xs_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Vector_rightpad(v_00_u03b1_2932_, v_m_2933_, v_n_2934_, v_a_2935_, v_xs_2936_);
lean_dec(v_n_2934_);
lean_dec(v_m_2933_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_f_2938_, lean_object* v_a_2939_, lean_object* v_h_2940_, lean_object* v_b_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_apply_3(v_f_2938_, v_a_2939_, lean_box(0), v_b_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_inst_2943_, lean_object* v_00_u03b2_2944_, lean_object* v_xs_2945_, lean_object* v_b_2946_, lean_object* v_f_2947_){
_start:
{
lean_object* v___f_2948_; size_t v_sz_2949_; size_t v___x_2950_; lean_object* v___x_2951_; 
v___f_2948_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2948_, 0, v_f_2947_);
v_sz_2949_ = lean_array_size(v_xs_2945_);
v___x_2950_ = ((size_t)0ULL);
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2943_, v_xs_2945_, v___f_2948_, v_sz_2949_, v___x_2950_, v_b_2946_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_2952_){
_start:
{
lean_object* v___f_2953_; 
v___f_2953_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2953_, 0, v_inst_2952_);
return v___f_2953_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_2954_, lean_object* v_00_u03b1_2955_, lean_object* v_n_2956_, lean_object* v_inst_2957_){
_start:
{
lean_object* v___f_2958_; 
v___f_2958_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2958_, 0, v_inst_2957_);
return v___f_2958_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(lean_object* v_m_2959_, lean_object* v_00_u03b1_2960_, lean_object* v_n_2961_, lean_object* v_inst_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Vector_instForIn_x27InferInstanceMembershipOfMonad(v_m_2959_, v_00_u03b1_2960_, v_n_2961_, v_inst_2962_);
lean_dec(v_n_2961_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad___redArg(lean_object* v_n_2964_, lean_object* v_inst_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2966_, 0, lean_box(0));
lean_closure_set(v___x_2966_, 1, lean_box(0));
lean_closure_set(v___x_2966_, 2, v_n_2964_);
lean_closure_set(v___x_2966_, 3, v_inst_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad(lean_object* v_m_2967_, lean_object* v_00_u03b1_2968_, lean_object* v_n_2969_, lean_object* v_inst_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2971_, 0, lean_box(0));
lean_closure_set(v___x_2971_, 1, lean_box(0));
lean_closure_set(v___x_2971_, 2, v_n_2969_);
lean_closure_set(v___x_2971_, 3, v_inst_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___redArg(){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_box(0);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___redArg___boxed(lean_object* v___dummy_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Vector_instLT___redArg();
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object* v_00_u03b1_2976_, lean_object* v_n_2977_, lean_object* v_inst_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_box(0);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object* v_00_u03b1_2980_, lean_object* v_n_2981_, lean_object* v_inst_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Vector_instLT(v_00_u03b1_2980_, v_n_2981_, v_inst_2982_);
lean_dec(v_n_2981_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___redArg(){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_box(0);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___redArg___boxed(lean_object* v___dummy_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Vector_instLE___redArg();
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE(lean_object* v_00_u03b1_2988_, lean_object* v_n_2989_, lean_object* v_inst_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_box(0);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___boxed(lean_object* v_00_u03b1_2992_, lean_object* v_n_2993_, lean_object* v_inst_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Vector_instLE(v_00_u03b1_2992_, v_n_2993_, v_inst_2994_);
lean_dec(v_n_2993_);
return v_res_2995_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__2(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = ((lean_object*)(l_Vector_lex___auto__1___closed__0));
v___x_3003_ = l_Lean_mkAtom(v___x_3002_);
return v___x_3003_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__3(void){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = lean_obj_once(&l_Vector_lex___auto__1___closed__2, &l_Vector_lex___auto__1___closed__2_once, _init_l_Vector_lex___auto__1___closed__2);
v___x_3005_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3006_ = lean_array_push(v___x_3005_, v___x_3004_);
return v___x_3006_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_3020_ = l_Lean_mkAtom(v___x_3019_);
return v___x_3020_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = lean_obj_once(&l_Vector_lex___auto__1___closed__8, &l_Vector_lex___auto__1___closed__8_once, _init_l_Vector_lex___auto__1___closed__8);
v___x_3022_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3023_ = lean_array_push(v___x_3022_, v___x_3021_);
return v___x_3023_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3037_ = ((lean_object*)(l_Vector_lex___auto__1___closed__14));
v___x_3038_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3039_ = lean_array_push(v___x_3038_, v___x_3037_);
return v___x_3039_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3040_ = lean_obj_once(&l_Vector_lex___auto__1___closed__15, &l_Vector_lex___auto__1___closed__15_once, _init_l_Vector_lex___auto__1___closed__15);
v___x_3041_ = ((lean_object*)(l_Vector_lex___auto__1___closed__11));
v___x_3042_ = lean_box(2);
v___x_3043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
lean_ctor_set(v___x_3043_, 1, v___x_3041_);
lean_ctor_set(v___x_3043_, 2, v___x_3040_);
return v___x_3043_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_3045_ = lean_obj_once(&l_Vector_lex___auto__1___closed__9, &l_Vector_lex___auto__1___closed__9_once, _init_l_Vector_lex___auto__1___closed__9);
v___x_3046_ = lean_array_push(v___x_3045_, v___x_3044_);
return v___x_3046_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3047_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3048_ = ((lean_object*)(l_Vector_lex___auto__1___closed__7));
v___x_3049_ = lean_box(2);
v___x_3050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v___x_3048_);
lean_ctor_set(v___x_3050_, 2, v___x_3047_);
return v___x_3050_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = lean_obj_once(&l_Vector_lex___auto__1___closed__18, &l_Vector_lex___auto__1___closed__18_once, _init_l_Vector_lex___auto__1___closed__18);
v___x_3052_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3053_ = lean_array_push(v___x_3052_, v___x_3051_);
return v___x_3053_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = ((lean_object*)(l_Vector_lex___auto__1___closed__24));
v___x_3065_ = l_Lean_mkAtom(v___x_3064_);
return v___x_3065_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = lean_obj_once(&l_Vector_lex___auto__1___closed__25, &l_Vector_lex___auto__1___closed__25_once, _init_l_Vector_lex___auto__1___closed__25);
v___x_3067_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3068_ = lean_array_push(v___x_3067_, v___x_3066_);
return v___x_3068_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_3070_ = lean_obj_once(&l_Vector_lex___auto__1___closed__26, &l_Vector_lex___auto__1___closed__26_once, _init_l_Vector_lex___auto__1___closed__26);
v___x_3071_ = lean_array_push(v___x_3070_, v___x_3069_);
return v___x_3071_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3072_ = lean_obj_once(&l_Vector_lex___auto__1___closed__27, &l_Vector_lex___auto__1___closed__27_once, _init_l_Vector_lex___auto__1___closed__27);
v___x_3073_ = ((lean_object*)(l_Vector_lex___auto__1___closed__23));
v___x_3074_ = lean_box(2);
v___x_3075_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3073_);
lean_ctor_set(v___x_3075_, 2, v___x_3072_);
return v___x_3075_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3077_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3078_ = lean_array_push(v___x_3077_, v___x_3076_);
return v___x_3078_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__31(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = ((lean_object*)(l_Vector_lex___auto__1___closed__30));
v___x_3081_ = l_Lean_mkAtom(v___x_3080_);
return v___x_3081_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3082_ = lean_obj_once(&l_Vector_lex___auto__1___closed__31, &l_Vector_lex___auto__1___closed__31_once, _init_l_Vector_lex___auto__1___closed__31);
v___x_3083_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3084_ = lean_array_push(v___x_3083_, v___x_3082_);
return v___x_3084_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__33(void){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3086_ = lean_obj_once(&l_Vector_lex___auto__1___closed__32, &l_Vector_lex___auto__1___closed__32_once, _init_l_Vector_lex___auto__1___closed__32);
v___x_3087_ = lean_array_push(v___x_3086_, v___x_3085_);
return v___x_3087_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__34(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3088_ = lean_obj_once(&l_Vector_lex___auto__1___closed__33, &l_Vector_lex___auto__1___closed__33_once, _init_l_Vector_lex___auto__1___closed__33);
v___x_3089_ = ((lean_object*)(l_Vector_lex___auto__1___closed__21));
v___x_3090_ = lean_box(2);
v___x_3091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
lean_ctor_set(v___x_3091_, 1, v___x_3089_);
lean_ctor_set(v___x_3091_, 2, v___x_3088_);
return v___x_3091_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__35(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_obj_once(&l_Vector_lex___auto__1___closed__34, &l_Vector_lex___auto__1___closed__34_once, _init_l_Vector_lex___auto__1___closed__34);
v___x_3093_ = lean_obj_once(&l_Vector_lex___auto__1___closed__19, &l_Vector_lex___auto__1___closed__19_once, _init_l_Vector_lex___auto__1___closed__19);
v___x_3094_ = lean_array_push(v___x_3093_, v___x_3092_);
return v___x_3094_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__36(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_3096_ = l_Lean_mkAtom(v___x_3095_);
return v___x_3096_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = lean_obj_once(&l_Vector_lex___auto__1___closed__36, &l_Vector_lex___auto__1___closed__36_once, _init_l_Vector_lex___auto__1___closed__36);
v___x_3098_ = lean_obj_once(&l_Vector_lex___auto__1___closed__35, &l_Vector_lex___auto__1___closed__35_once, _init_l_Vector_lex___auto__1___closed__35);
v___x_3099_ = lean_array_push(v___x_3098_, v___x_3097_);
return v___x_3099_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3100_ = lean_obj_once(&l_Vector_lex___auto__1___closed__37, &l_Vector_lex___auto__1___closed__37_once, _init_l_Vector_lex___auto__1___closed__37);
v___x_3101_ = ((lean_object*)(l_Vector_lex___auto__1___closed__5));
v___x_3102_ = lean_box(2);
v___x_3103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
lean_ctor_set(v___x_3103_, 1, v___x_3101_);
lean_ctor_set(v___x_3103_, 2, v___x_3100_);
return v___x_3103_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = lean_obj_once(&l_Vector_lex___auto__1___closed__38, &l_Vector_lex___auto__1___closed__38_once, _init_l_Vector_lex___auto__1___closed__38);
v___x_3105_ = lean_obj_once(&l_Vector_lex___auto__1___closed__3, &l_Vector_lex___auto__1___closed__3_once, _init_l_Vector_lex___auto__1___closed__3);
v___x_3106_ = lean_array_push(v___x_3105_, v___x_3104_);
return v___x_3106_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3107_ = lean_obj_once(&l_Vector_lex___auto__1___closed__39, &l_Vector_lex___auto__1___closed__39_once, _init_l_Vector_lex___auto__1___closed__39);
v___x_3108_ = ((lean_object*)(l_Vector_lex___auto__1___closed__1));
v___x_3109_ = lean_box(2);
v___x_3110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
lean_ctor_set(v___x_3110_, 1, v___x_3108_);
lean_ctor_set(v___x_3110_, 2, v___x_3107_);
return v___x_3110_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = lean_obj_once(&l_Vector_lex___auto__1___closed__40, &l_Vector_lex___auto__1___closed__40_once, _init_l_Vector_lex___auto__1___closed__40);
v___x_3112_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3113_ = lean_array_push(v___x_3112_, v___x_3111_);
return v___x_3113_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3114_ = lean_obj_once(&l_Vector_lex___auto__1___closed__41, &l_Vector_lex___auto__1___closed__41_once, _init_l_Vector_lex___auto__1___closed__41);
v___x_3115_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_3116_ = lean_box(2);
v___x_3117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
lean_ctor_set(v___x_3117_, 1, v___x_3115_);
lean_ctor_set(v___x_3117_, 2, v___x_3114_);
return v___x_3117_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = lean_obj_once(&l_Vector_lex___auto__1___closed__42, &l_Vector_lex___auto__1___closed__42_once, _init_l_Vector_lex___auto__1___closed__42);
v___x_3119_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3120_ = lean_array_push(v___x_3119_, v___x_3118_);
return v___x_3120_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3121_ = lean_obj_once(&l_Vector_lex___auto__1___closed__43, &l_Vector_lex___auto__1___closed__43_once, _init_l_Vector_lex___auto__1___closed__43);
v___x_3122_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_3123_ = lean_box(2);
v___x_3124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
lean_ctor_set(v___x_3124_, 1, v___x_3122_);
lean_ctor_set(v___x_3124_, 2, v___x_3121_);
return v___x_3124_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3125_ = lean_obj_once(&l_Vector_lex___auto__1___closed__44, &l_Vector_lex___auto__1___closed__44_once, _init_l_Vector_lex___auto__1___closed__44);
v___x_3126_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3127_ = lean_array_push(v___x_3126_, v___x_3125_);
return v___x_3127_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3128_ = lean_obj_once(&l_Vector_lex___auto__1___closed__45, &l_Vector_lex___auto__1___closed__45_once, _init_l_Vector_lex___auto__1___closed__45);
v___x_3129_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_3130_ = lean_box(2);
v___x_3131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
lean_ctor_set(v___x_3131_, 1, v___x_3129_);
lean_ctor_set(v___x_3131_, 2, v___x_3128_);
return v___x_3131_;
}
}
static lean_object* _init_l_Vector_lex___auto__1(void){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = lean_obj_once(&l_Vector_lex___auto__1___closed__46, &l_Vector_lex___auto__1___closed__46_once, _init_l_Vector_lex___auto__1___closed__46);
return v___x_3132_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg(lean_object* v_n_3133_, lean_object* v_inst_3134_, lean_object* v_xs_3135_, lean_object* v_ys_3136_, lean_object* v_lt_3137_, lean_object* v_i_3138_){
_start:
{
uint8_t v___x_3139_; 
v___x_3139_ = lean_nat_dec_le(v_n_3133_, v_i_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3140_ = lean_array_fget_borrowed(v_xs_3135_, v_i_3138_);
v___x_3141_ = lean_array_fget_borrowed(v_ys_3136_, v_i_3138_);
lean_inc_ref(v_lt_3137_);
lean_inc(v___x_3141_);
lean_inc(v___x_3140_);
v___x_3142_ = lean_apply_2(v_lt_3137_, v___x_3140_, v___x_3141_);
v___x_3143_ = lean_unbox(v___x_3142_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; uint8_t v___x_3145_; 
lean_inc_ref(v_inst_3134_);
lean_inc(v___x_3141_);
lean_inc(v___x_3140_);
v___x_3144_ = lean_apply_2(v_inst_3134_, v___x_3140_, v___x_3141_);
v___x_3145_ = lean_unbox(v___x_3144_);
if (v___x_3145_ == 0)
{
uint8_t v___x_3146_; 
lean_dec(v_i_3138_);
lean_dec_ref(v_lt_3137_);
lean_dec_ref(v_inst_3134_);
v___x_3146_ = lean_unbox(v___x_3144_);
return v___x_3146_;
}
else
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = lean_unsigned_to_nat(1u);
v___x_3148_ = lean_nat_add(v_i_3138_, v___x_3147_);
lean_dec(v_i_3138_);
v_i_3138_ = v___x_3148_;
goto _start;
}
}
else
{
uint8_t v___x_3150_; 
lean_dec(v_i_3138_);
lean_dec_ref(v_lt_3137_);
lean_dec_ref(v_inst_3134_);
v___x_3150_ = lean_unbox(v___x_3142_);
return v___x_3150_;
}
}
else
{
uint8_t v___x_3151_; 
lean_dec(v_i_3138_);
lean_dec_ref(v_lt_3137_);
lean_dec_ref(v_inst_3134_);
v___x_3151_ = 0;
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg___boxed(lean_object* v_n_3152_, lean_object* v_inst_3153_, lean_object* v_xs_3154_, lean_object* v_ys_3155_, lean_object* v_lt_3156_, lean_object* v_i_3157_){
_start:
{
uint8_t v_res_3158_; lean_object* v_r_3159_; 
v_res_3158_ = l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg(v_n_3152_, v_inst_3153_, v_xs_3154_, v_ys_3155_, v_lt_3156_, v_i_3157_);
lean_dec_ref(v_ys_3155_);
lean_dec_ref(v_xs_3154_);
lean_dec(v_n_3152_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Vector_Basic_0__Vector_lex_go(lean_object* v_00_u03b1_3160_, lean_object* v_n_3161_, lean_object* v_inst_3162_, lean_object* v_xs_3163_, lean_object* v_ys_3164_, lean_object* v_lt_3165_, lean_object* v_i_3166_){
_start:
{
uint8_t v___x_3167_; 
v___x_3167_ = l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg(v_n_3161_, v_inst_3162_, v_xs_3163_, v_ys_3164_, v_lt_3165_, v_i_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_lex_go___boxed(lean_object* v_00_u03b1_3168_, lean_object* v_n_3169_, lean_object* v_inst_3170_, lean_object* v_xs_3171_, lean_object* v_ys_3172_, lean_object* v_lt_3173_, lean_object* v_i_3174_){
_start:
{
uint8_t v_res_3175_; lean_object* v_r_3176_; 
v_res_3175_ = l___private_Init_Data_Vector_Basic_0__Vector_lex_go(v_00_u03b1_3168_, v_n_3169_, v_inst_3170_, v_xs_3171_, v_ys_3172_, v_lt_3173_, v_i_3174_);
lean_dec_ref(v_ys_3172_);
lean_dec_ref(v_xs_3171_);
lean_dec(v_n_3169_);
v_r_3176_ = lean_box(v_res_3175_);
return v_r_3176_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object* v_n_3177_, lean_object* v_inst_3178_, lean_object* v_xs_3179_, lean_object* v_ys_3180_, lean_object* v_lt_3181_){
_start:
{
lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg(v_n_3177_, v_inst_3178_, v_xs_3179_, v_ys_3180_, v_lt_3181_, v___x_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object* v_n_3184_, lean_object* v_inst_3185_, lean_object* v_xs_3186_, lean_object* v_ys_3187_, lean_object* v_lt_3188_){
_start:
{
uint8_t v_res_3189_; lean_object* v_r_3190_; 
v_res_3189_ = l_Vector_lex___redArg(v_n_3184_, v_inst_3185_, v_xs_3186_, v_ys_3187_, v_lt_3188_);
lean_dec_ref(v_ys_3187_);
lean_dec_ref(v_xs_3186_);
lean_dec(v_n_3184_);
v_r_3190_ = lean_box(v_res_3189_);
return v_r_3190_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex(lean_object* v_00_u03b1_3191_, lean_object* v_n_3192_, lean_object* v_inst_3193_, lean_object* v_xs_3194_, lean_object* v_ys_3195_, lean_object* v_lt_3196_){
_start:
{
uint8_t v___x_3197_; 
v___x_3197_ = l_Vector_lex___redArg(v_n_3192_, v_inst_3193_, v_xs_3194_, v_ys_3195_, v_lt_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object* v_00_u03b1_3198_, lean_object* v_n_3199_, lean_object* v_inst_3200_, lean_object* v_xs_3201_, lean_object* v_ys_3202_, lean_object* v_lt_3203_){
_start:
{
uint8_t v_res_3204_; lean_object* v_r_3205_; 
v_res_3204_ = l_Vector_lex(v_00_u03b1_3198_, v_n_3199_, v_inst_3200_, v_xs_3201_, v_ys_3202_, v_lt_3203_);
lean_dec_ref(v_ys_3202_);
lean_dec_ref(v_xs_3201_);
lean_dec(v_n_3199_);
v_r_3205_ = lean_box(v_res_3204_);
return v_r_3205_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_InsertIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_MapIdx(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Array_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
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
lean_object* initialize_Init_Data_Array_InsertIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MapIdx(uint8_t builtin);
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
res = initialize_Init_Data_Array_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MapIdx(builtin);
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
