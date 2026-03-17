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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Array_finIdxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
static const lean_string_object l_instReprVector_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_instReprVector_repr___redArg___closed__0 = (const lean_object*)&l_instReprVector_repr___redArg___closed__0_value;
static const lean_string_object l_instReprVector_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_instReprVector_repr___redArg___closed__1 = (const lean_object*)&l_instReprVector_repr___redArg___closed__1_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__1_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__2 = (const lean_object*)&l_instReprVector_repr___redArg___closed__2_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instReprVector_repr___redArg___closed__2_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__3 = (const lean_object*)&l_instReprVector_repr___redArg___closed__3_value;
static const lean_string_object l_instReprVector_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_instReprVector_repr___redArg___closed__4 = (const lean_object*)&l_instReprVector_repr___redArg___closed__4_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__4_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__5 = (const lean_object*)&l_instReprVector_repr___redArg___closed__5_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__3_value),((lean_object*)&l_instReprVector_repr___redArg___closed__5_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__6 = (const lean_object*)&l_instReprVector_repr___redArg___closed__6_value;
static lean_once_cell_t l_instReprVector_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprVector_repr___redArg___closed__7;
static const lean_string_object l_instReprVector_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_instReprVector_repr___redArg___closed__8 = (const lean_object*)&l_instReprVector_repr___redArg___closed__8_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__8_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__9 = (const lean_object*)&l_instReprVector_repr___redArg___closed__9_value;
static const lean_string_object l_instReprVector_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "size_toArray"};
static const lean_object* l_instReprVector_repr___redArg___closed__10 = (const lean_object*)&l_instReprVector_repr___redArg___closed__10_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__10_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__11 = (const lean_object*)&l_instReprVector_repr___redArg___closed__11_value;
static const lean_string_object l_instReprVector_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_instReprVector_repr___redArg___closed__12 = (const lean_object*)&l_instReprVector_repr___redArg___closed__12_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__12_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__13 = (const lean_object*)&l_instReprVector_repr___redArg___closed__13_value;
static const lean_string_object l_instReprVector_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_instReprVector_repr___redArg___closed__14 = (const lean_object*)&l_instReprVector_repr___redArg___closed__14_value;
static lean_once_cell_t l_instReprVector_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprVector_repr___redArg___closed__15;
static lean_once_cell_t l_instReprVector_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprVector_repr___redArg___closed__16;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__0_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__17 = (const lean_object*)&l_instReprVector_repr___redArg___closed__17_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__14_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__18 = (const lean_object*)&l_instReprVector_repr___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_instReprVector_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprVector_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprVector_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprVector___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprVector(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__12 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__13 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__11_value),((lean_object*)&l_instReprVector_repr___redArg___closed__8_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__14 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__8_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__15 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__6_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__16 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__17 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__18 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__19 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__20 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value;
LEAN_EXPORT const lean_object* l_Vector_term_x23v_x5b___x2c_x5d = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value;
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
LEAN_EXPORT lean_object* l_Vector_unexpandMk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_unexpandMk___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_instReprVector_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(11u);
v___x_15_ = lean_nat_to_int(v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l_instReprVector_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__0));
v___x_27_ = lean_string_length(v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l_instReprVector_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_obj_once(&l_instReprVector_repr___redArg___closed__15, &l_instReprVector_repr___redArg___closed__15_once, _init_l_instReprVector_repr___redArg___closed__15);
v___x_29_ = lean_nat_to_int(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_instReprVector_repr___redArg(lean_object* v_inst_34_, lean_object* v_x_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_36_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__5));
v___x_37_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__6));
v___x_38_ = lean_obj_once(&l_instReprVector_repr___redArg___closed__7, &l_instReprVector_repr___redArg___closed__7_once, _init_l_instReprVector_repr___redArg___closed__7);
v___x_39_ = l_Array_repr___redArg(v_inst_34_, v_x_35_);
v___x_40_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_38_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
v___x_41_ = 0;
v___x_42_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_42_, 0, v___x_40_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*1, v___x_41_);
v___x_43_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_37_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__9));
v___x_45_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_43_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = lean_box(1);
v___x_47_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_45_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__11));
v___x_49_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_47_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_36_);
v___x_51_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__13));
v___x_52_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = lean_obj_once(&l_instReprVector_repr___redArg___closed__16, &l_instReprVector_repr___redArg___closed__16_once, _init_l_instReprVector_repr___redArg___closed__16);
v___x_54_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__17));
v___x_55_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_52_);
v___x_56_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__18));
v___x_57_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_53_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*1, v___x_41_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_instReprVector_repr(lean_object* v_00_u03b1_60_, lean_object* v_n_61_, lean_object* v_inst_62_, lean_object* v_x_63_, lean_object* v_prec_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_instReprVector_repr___redArg(v_inst_62_, v_x_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_instReprVector_repr___boxed(lean_object* v_00_u03b1_66_, lean_object* v_n_67_, lean_object* v_inst_68_, lean_object* v_x_69_, lean_object* v_prec_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_instReprVector_repr(v_00_u03b1_66_, v_n_67_, v_inst_68_, v_x_69_, v_prec_70_);
lean_dec(v_prec_70_);
lean_dec(v_n_67_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_instReprVector___redArg(lean_object* v_n_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_closure((void*)(l_instReprVector_repr___boxed), 5, 3);
lean_closure_set(v___x_74_, 0, lean_box(0));
lean_closure_set(v___x_74_, 1, v_n_72_);
lean_closure_set(v___x_74_, 2, v_inst_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_instReprVector(lean_object* v_00_u03b1_75_, lean_object* v_n_76_, lean_object* v_inst_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_closure((void*)(l_instReprVector_repr___boxed), 5, 3);
lean_closure_set(v___x_78_, 0, lean_box(0));
lean_closure_set(v___x_78_, 1, v_n_76_);
lean_closure_set(v___x_78_, 2, v_inst_77_);
return v___x_78_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq___redArg(lean_object* v_inst_79_, lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = l_Array_instDecidableEqImpl___redArg(v_inst_79_, v_x_80_, v_x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___redArg___boxed(lean_object* v_inst_83_, lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_instDecidableEqVector_decEq___redArg(v_inst_83_, v_x_84_, v_x_85_);
lean_dec_ref(v_x_85_);
lean_dec_ref(v_x_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq(lean_object* v_00_u03b1_88_, lean_object* v_n_89_, lean_object* v_inst_90_, lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = l_Array_instDecidableEqImpl___redArg(v_inst_90_, v_x_91_, v_x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___boxed(lean_object* v_00_u03b1_94_, lean_object* v_n_95_, lean_object* v_inst_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_instDecidableEqVector_decEq(v_00_u03b1_94_, v_n_95_, v_inst_96_, v_x_97_, v_x_98_);
lean_dec_ref(v_x_98_);
lean_dec_ref(v_x_97_);
lean_dec(v_n_95_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector___redArg(lean_object* v_inst_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = l_Array_instDecidableEqImpl___redArg(v_inst_101_, v_x_102_, v_x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector___redArg___boxed(lean_object* v_inst_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_instDecidableEqVector___redArg(v_inst_105_, v_x_106_, v_x_107_);
lean_dec_ref(v_x_107_);
lean_dec_ref(v_x_106_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector(lean_object* v_00_u03b1_110_, lean_object* v_n_111_, lean_object* v_inst_112_, lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = l_Array_instDecidableEqImpl___redArg(v_inst_112_, v_x_113_, v_x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector___boxed(lean_object* v_00_u03b1_116_, lean_object* v_n_117_, lean_object* v_inst_118_, lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_instDecidableEqVector(v_00_u03b1_116_, v_n_117_, v_inst_118_, v_x_119_, v_x_120_);
lean_dec_ref(v_x_120_);
lean_dec_ref(v_x_119_);
lean_dec(v_n_117_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___redArg(lean_object* v_xs_123_){
_start:
{
lean_inc_ref(v_xs_123_);
return v_xs_123_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___redArg___boxed(lean_object* v_xs_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Array_toVector___redArg(v_xs_124_);
lean_dec_ref(v_xs_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector(lean_object* v_00_u03b1_126_, lean_object* v_xs_127_){
_start:
{
lean_inc_ref(v_xs_127_);
return v_xs_127_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___boxed(lean_object* v_00_u03b1_128_, lean_object* v_xs_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Array_toVector(v_00_u03b1_128_, v_xs_129_);
lean_dec_ref(v_xs_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___redArg(lean_object* v_n_131_){
_start:
{
lean_inc(v_n_131_);
return v_n_131_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___redArg___boxed(lean_object* v_n_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Vector_size___redArg(v_n_132_);
lean_dec(v_n_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Vector_size(lean_object* v_00_u03b1_134_, lean_object* v_n_135_, lean_object* v_x_136_){
_start:
{
lean_inc(v_n_135_);
return v_n_135_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___boxed(lean_object* v_00_u03b1_137_, lean_object* v_n_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Vector_size(v_00_u03b1_137_, v_n_138_, v_x_139_);
lean_dec_ref(v_x_139_);
lean_dec(v_n_138_);
return v_res_140_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5));
v___x_199_ = l_String_toRawSubstring_x27(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18));
v___x_227_ = l_String_toRawSubstring_x27(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26(void){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Array_mkArray0(lean_box(0));
return v___x_236_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27));
v___x_239_ = l_String_toRawSubstring_x27(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(lean_object* v_x_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__2));
lean_inc(v_x_248_);
v___x_252_ = l_Lean_Syntax_isOfKind(v_x_248_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec_ref(v_a_249_);
lean_dec(v_x_248_);
v___x_253_ = lean_box(1);
v___x_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v_a_250_);
return v___x_254_;
}
else
{
lean_object* v_quotContext_255_; lean_object* v_currMacroScope_256_; lean_object* v_ref_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_elems_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_quotContext_255_ = lean_ctor_get(v_a_249_, 1);
lean_inc(v_quotContext_255_);
v_currMacroScope_256_ = lean_ctor_get(v_a_249_, 2);
lean_inc(v_currMacroScope_256_);
v_ref_257_ = lean_ctor_get(v_a_249_, 5);
lean_inc(v_ref_257_);
lean_dec_ref(v_a_249_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = l_Lean_Syntax_getArg(v_x_248_, v___x_258_);
lean_dec(v_x_248_);
v_elems_260_ = l_Lean_Syntax_getArgs(v___x_259_);
lean_dec(v___x_259_);
v___x_261_ = 0;
v___x_262_ = l_Lean_SourceInfo_fromRef(v_ref_257_, v___x_261_);
lean_dec(v_ref_257_);
v___x_263_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4));
v___x_264_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6);
v___x_265_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8));
lean_inc(v_currMacroScope_256_);
lean_inc(v_quotContext_255_);
v___x_266_ = l_Lean_addMacroScope(v_quotContext_255_, v___x_265_, v_currMacroScope_256_);
v___x_267_ = lean_box(0);
v___x_268_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12));
lean_inc(v___x_262_);
v___x_269_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_269_, 0, v___x_262_);
lean_ctor_set(v___x_269_, 1, v___x_264_);
lean_ctor_set(v___x_269_, 2, v___x_266_);
lean_ctor_set(v___x_269_, 3, v___x_268_);
v___x_270_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_271_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16));
v___x_272_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
lean_inc(v___x_262_);
v___x_273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_262_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19);
v___x_275_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20));
lean_inc(v_currMacroScope_256_);
lean_inc(v_quotContext_255_);
v___x_276_ = l_Lean_addMacroScope(v_quotContext_255_, v___x_275_, v_currMacroScope_256_);
lean_inc(v___x_262_);
v___x_277_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_277_, 0, v___x_262_);
lean_ctor_set(v___x_277_, 1, v___x_274_);
lean_ctor_set(v___x_277_, 2, v___x_276_);
lean_ctor_set(v___x_277_, 3, v___x_267_);
v___x_278_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21));
lean_inc(v___x_262_);
v___x_279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_262_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_elems_260_);
v___x_281_ = lean_array_get_size(v___x_280_);
lean_dec_ref(v___x_280_);
v___x_282_ = l_Nat_reprFast(v___x_281_);
v___x_283_ = lean_box(2);
v___x_284_ = l_Lean_Syntax_mkNumLit(v___x_282_, v___x_283_);
v___x_285_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
lean_inc(v___x_262_);
v___x_286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_262_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
lean_inc(v___x_262_);
v___x_287_ = l_Lean_Syntax_node5(v___x_262_, v___x_271_, v___x_273_, v___x_277_, v___x_279_, v___x_284_, v___x_286_);
v___x_288_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24));
v___x_289_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25));
lean_inc(v___x_262_);
v___x_290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_262_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
v___x_292_ = l_Array_append___redArg(v___x_291_, v_elems_260_);
lean_dec_ref(v_elems_260_);
lean_inc(v___x_262_);
v___x_293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_293_, 0, v___x_262_);
lean_ctor_set(v___x_293_, 1, v___x_270_);
lean_ctor_set(v___x_293_, 2, v___x_292_);
v___x_294_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__17));
lean_inc(v___x_262_);
v___x_295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_262_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
lean_inc(v___x_262_);
v___x_296_ = l_Lean_Syntax_node3(v___x_262_, v___x_288_, v___x_290_, v___x_293_, v___x_295_);
v___x_297_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28);
v___x_298_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29));
v___x_299_ = l_Lean_addMacroScope(v_quotContext_255_, v___x_298_, v_currMacroScope_256_);
v___x_300_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31));
lean_inc(v___x_262_);
v___x_301_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_301_, 0, v___x_262_);
lean_ctor_set(v___x_301_, 1, v___x_297_);
lean_ctor_set(v___x_301_, 2, v___x_299_);
lean_ctor_set(v___x_301_, 3, v___x_300_);
lean_inc(v___x_262_);
v___x_302_ = l_Lean_Syntax_node3(v___x_262_, v___x_270_, v___x_287_, v___x_296_, v___x_301_);
v___x_303_ = l_Lean_Syntax_node2(v___x_262_, v___x_263_, v___x_269_, v___x_302_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v_a_250_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_unexpandMk(lean_object* v_x_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4));
lean_inc(v_x_305_);
v___x_309_ = l_Lean_Syntax_isOfKind(v_x_305_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_x_305_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_a_307_);
return v___x_311_;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = l_Lean_Syntax_getArg(v_x_305_, v___x_312_);
lean_dec(v_x_305_);
v___x_314_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_313_);
v___x_315_ = l_Lean_Syntax_matchesNull(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_a_307_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = l_Lean_Syntax_getArg(v___x_313_, v___x_318_);
lean_dec(v___x_313_);
v___x_320_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24));
lean_inc(v___x_319_);
v___x_321_ = l_Lean_Syntax_isOfKind(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_a_307_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_324_ = l_Lean_Syntax_getArg(v___x_319_, v___x_312_);
lean_dec(v___x_319_);
v___x_325_ = l_Lean_Syntax_getArgs(v___x_324_);
lean_dec(v___x_324_);
v___x_326_ = 0;
v___x_327_ = l_Lean_SourceInfo_fromRef(v_a_306_, v___x_326_);
v___x_328_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__2));
v___x_329_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__5));
lean_inc(v___x_327_);
v___x_330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_327_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_332_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
v___x_333_ = l_Array_append___redArg(v___x_332_, v___x_325_);
lean_dec_ref(v___x_325_);
lean_inc(v___x_327_);
v___x_334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_334_, 0, v___x_327_);
lean_ctor_set(v___x_334_, 1, v___x_331_);
lean_ctor_set(v___x_334_, 2, v___x_333_);
v___x_335_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__17));
lean_inc(v___x_327_);
v___x_336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_327_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = l_Lean_Syntax_node3(v___x_327_, v___x_328_, v___x_330_, v___x_334_, v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_a_307_);
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unexpandMk___boxed(lean_object* v_x_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Vector_unexpandMk(v_x_339_, v_a_340_, v_a_341_);
lean_dec(v_a_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList___redArg(lean_object* v_xs_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lean_array_to_list(v_xs_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList(lean_object* v_00_u03b1_345_, lean_object* v_n_346_, lean_object* v_xs_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_array_to_list(v_xs_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList___boxed(lean_object* v_00_u03b1_349_, lean_object* v_n_350_, lean_object* v_xs_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Vector_toList(v_00_u03b1_349_, v_n_350_, v_xs_351_);
lean_dec(v_n_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray___redArg(lean_object* v_mk_353_, lean_object* v_x_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_apply_2(v_mk_353_, v_x_354_, lean_box(0));
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray(lean_object* v_00_u03b1_356_, lean_object* v_n_357_, lean_object* v_motive_358_, lean_object* v_mk_359_, lean_object* v_x_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_apply_2(v_mk_359_, v_x_360_, lean_box(0));
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray___boxed(lean_object* v_00_u03b1_362_, lean_object* v_n_363_, lean_object* v_motive_364_, lean_object* v_mk_365_, lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Vector_elimAsArray(v_00_u03b1_362_, v_n_363_, v_motive_364_, v_mk_365_, v_x_366_);
lean_dec(v_n_363_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList___redArg(lean_object* v_mk_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_toList_370_; lean_object* v___x_371_; 
v_toList_370_ = lean_array_to_list(v_x_369_);
v___x_371_ = lean_apply_2(v_mk_368_, v_toList_370_, lean_box(0));
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList(lean_object* v_00_u03b1_372_, lean_object* v_n_373_, lean_object* v_motive_374_, lean_object* v_mk_375_, lean_object* v_x_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Vector_elimAsList___redArg(v_mk_375_, v_x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList___boxed(lean_object* v_00_u03b1_378_, lean_object* v_n_379_, lean_object* v_motive_380_, lean_object* v_mk_381_, lean_object* v_x_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Vector_elimAsList(v_00_u03b1_378_, v_n_379_, v_motive_380_, v_mk_381_, v_x_382_);
lean_dec(v_n_379_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg(lean_object* v_capacity_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_mk_empty_array_with_capacity(v_capacity_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Vector_emptyWithCapacity___redArg(v_capacity_386_);
lean_dec(v_capacity_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity(lean_object* v_00_u03b1_388_, lean_object* v_capacity_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = lean_mk_empty_array_with_capacity(v_capacity_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___boxed(lean_object* v_00_u03b1_391_, lean_object* v_capacity_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Vector_emptyWithCapacity(v_00_u03b1_391_, v_capacity_392_);
lean_dec(v_capacity_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Vector_replicate___redArg(lean_object* v_n_394_, lean_object* v_v_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = lean_mk_array(v_n_394_, v_v_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Vector_replicate(lean_object* v_00_u03b1_397_, lean_object* v_n_398_, lean_object* v_v_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_mk_array(v_n_398_, v_v_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Vector_singleton___redArg(lean_object* v_v_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_mk_empty_array_with_capacity(v___x_402_);
v___x_404_ = lean_array_push(v___x_403_, v_v_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Vector_singleton(lean_object* v_00_u03b1_405_, lean_object* v_v_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_mk_empty_array_with_capacity(v___x_407_);
v___x_409_ = lean_array_push(v___x_408_, v_v_406_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Vector_instInhabited___redArg(lean_object* v_n_410_, lean_object* v_inst_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = lean_mk_array(v_n_410_, v_inst_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Vector_instInhabited(lean_object* v_00_u03b1_413_, lean_object* v_n_414_, lean_object* v_inst_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = lean_mk_array(v_n_414_, v_inst_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___redArg(lean_object* v_xs_417_, lean_object* v_i_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = lean_array_fget_borrowed(v_xs_417_, v_i_418_);
lean_inc(v___x_419_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___redArg___boxed(lean_object* v_xs_420_, lean_object* v_i_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Vector_get___redArg(v_xs_420_, v_i_421_);
lean_dec(v_i_421_);
lean_dec_ref(v_xs_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Vector_get(lean_object* v_00_u03b1_423_, lean_object* v_n_424_, lean_object* v_xs_425_, lean_object* v_i_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = lean_array_fget_borrowed(v_xs_425_, v_i_426_);
lean_inc(v___x_427_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___boxed(lean_object* v_00_u03b1_428_, lean_object* v_n_429_, lean_object* v_xs_430_, lean_object* v_i_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Vector_get(v_00_u03b1_428_, v_n_429_, v_xs_430_, v_i_431_);
lean_dec(v_i_431_);
lean_dec_ref(v_xs_430_);
lean_dec(v_n_429_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___redArg(lean_object* v_xs_433_, size_t v_i_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = lean_array_uget_borrowed(v_xs_433_, v_i_434_);
lean_inc(v___x_435_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___redArg___boxed(lean_object* v_xs_436_, lean_object* v_i_437_){
_start:
{
size_t v_i_boxed_438_; lean_object* v_res_439_; 
v_i_boxed_438_ = lean_unbox_usize(v_i_437_);
lean_dec(v_i_437_);
v_res_439_ = l_Vector_uget___redArg(v_xs_436_, v_i_boxed_438_);
lean_dec_ref(v_xs_436_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget(lean_object* v_00_u03b1_440_, lean_object* v_n_441_, lean_object* v_xs_442_, size_t v_i_443_, lean_object* v_h_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = lean_array_uget_borrowed(v_xs_442_, v_i_443_);
lean_inc(v___x_445_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___boxed(lean_object* v_00_u03b1_446_, lean_object* v_n_447_, lean_object* v_xs_448_, lean_object* v_i_449_, lean_object* v_h_450_){
_start:
{
size_t v_i_boxed_451_; lean_object* v_res_452_; 
v_i_boxed_451_ = lean_unbox_usize(v_i_449_);
lean_dec(v_i_449_);
v_res_452_ = l_Vector_uget(v_00_u03b1_446_, v_n_447_, v_xs_448_, v_i_boxed_451_, v_h_450_);
lean_dec_ref(v_xs_448_);
lean_dec(v_n_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___lam__0(lean_object* v_xs_453_, lean_object* v_i_454_, lean_object* v_h_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = lean_array_fget_borrowed(v_xs_453_, v_i_454_);
lean_inc(v___x_456_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___lam__0___boxed(lean_object* v_xs_457_, lean_object* v_i_458_, lean_object* v_h_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Vector_instGetElemNatLt___lam__0(v_xs_457_, v_i_458_, v_h_459_);
lean_dec(v_i_458_);
lean_dec_ref(v_xs_457_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt(lean_object* v_00_u03b1_462_, lean_object* v_n_463_){
_start:
{
lean_object* v___f_464_; 
v___f_464_ = ((lean_object*)(l_Vector_instGetElemNatLt___closed__0));
return v___f_464_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___boxed(lean_object* v_00_u03b1_465_, lean_object* v_n_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Vector_instGetElemNatLt(v_00_u03b1_465_, v_n_466_);
lean_dec(v_n_466_);
return v_res_467_;
}
}
LEAN_EXPORT uint8_t l_Vector_contains___redArg(lean_object* v_inst_468_, lean_object* v_xs_469_, lean_object* v_a_470_){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = l_Array_contains___redArg(v_inst_468_, v_xs_469_, v_a_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Vector_contains___redArg___boxed(lean_object* v_inst_472_, lean_object* v_xs_473_, lean_object* v_a_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_Vector_contains___redArg(v_inst_472_, v_xs_473_, v_a_474_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT uint8_t l_Vector_contains(lean_object* v_00_u03b1_477_, lean_object* v_n_478_, lean_object* v_inst_479_, lean_object* v_xs_480_, lean_object* v_a_481_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = l_Array_contains___redArg(v_inst_479_, v_xs_480_, v_a_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Vector_contains___boxed(lean_object* v_00_u03b1_483_, lean_object* v_n_484_, lean_object* v_inst_485_, lean_object* v_xs_486_, lean_object* v_a_487_){
_start:
{
uint8_t v_res_488_; lean_object* v_r_489_; 
v_res_488_ = l_Vector_contains(v_00_u03b1_483_, v_n_484_, v_inst_485_, v_xs_486_, v_a_487_);
lean_dec(v_n_484_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership(lean_object* v_00_u03b1_490_, lean_object* v_n_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = lean_box(0);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership___boxed(lean_object* v_00_u03b1_493_, lean_object* v_n_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Vector_instMembership(v_00_u03b1_493_, v_n_494_);
lean_dec(v_n_494_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg(lean_object* v_xs_496_, lean_object* v_i_497_, lean_object* v_default_498_){
_start:
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_array_get_size(v_xs_496_);
v___x_500_ = lean_nat_dec_lt(v_i_497_, v___x_499_);
if (v___x_500_ == 0)
{
lean_inc(v_default_498_);
return v_default_498_;
}
else
{
lean_object* v___x_501_; 
v___x_501_ = lean_array_fget_borrowed(v_xs_496_, v_i_497_);
lean_inc(v___x_501_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg___boxed(lean_object* v_xs_502_, lean_object* v_i_503_, lean_object* v_default_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Vector_getD___redArg(v_xs_502_, v_i_503_, v_default_504_);
lean_dec(v_default_504_);
lean_dec(v_i_503_);
lean_dec_ref(v_xs_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD(lean_object* v_00_u03b1_506_, lean_object* v_n_507_, lean_object* v_xs_508_, lean_object* v_i_509_, lean_object* v_default_510_){
_start:
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_array_get_size(v_xs_508_);
v___x_512_ = lean_nat_dec_lt(v_i_509_, v___x_511_);
if (v___x_512_ == 0)
{
lean_inc(v_default_510_);
return v_default_510_;
}
else
{
lean_object* v___x_513_; 
v___x_513_ = lean_array_fget_borrowed(v_xs_508_, v_i_509_);
lean_inc(v___x_513_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___boxed(lean_object* v_00_u03b1_514_, lean_object* v_n_515_, lean_object* v_xs_516_, lean_object* v_i_517_, lean_object* v_default_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Vector_getD(v_00_u03b1_514_, v_n_515_, v_xs_516_, v_i_517_, v_default_518_);
lean_dec(v_default_518_);
lean_dec(v_i_517_);
lean_dec_ref(v_xs_516_);
lean_dec(v_n_515_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg(lean_object* v_inst_520_, lean_object* v_xs_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_522_ = lean_array_get_size(v_xs_521_);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_sub(v___x_522_, v___x_523_);
v___x_525_ = lean_array_get_borrowed(v_inst_520_, v_xs_521_, v___x_524_);
lean_dec(v___x_524_);
lean_inc(v___x_525_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg___boxed(lean_object* v_inst_526_, lean_object* v_xs_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Vector_back_x21___redArg(v_inst_526_, v_xs_527_);
lean_dec_ref(v_xs_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21(lean_object* v_00_u03b1_529_, lean_object* v_n_530_, lean_object* v_inst_531_, lean_object* v_xs_532_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_533_ = lean_array_get_size(v_xs_532_);
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_sub(v___x_533_, v___x_534_);
v___x_536_ = lean_array_get_borrowed(v_inst_531_, v_xs_532_, v___x_535_);
lean_dec(v___x_535_);
lean_inc(v___x_536_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___boxed(lean_object* v_00_u03b1_537_, lean_object* v_n_538_, lean_object* v_inst_539_, lean_object* v_xs_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Vector_back_x21(v_00_u03b1_537_, v_n_538_, v_inst_539_, v_xs_540_);
lean_dec_ref(v_xs_540_);
lean_dec(v_n_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg(lean_object* v_xs_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_543_ = lean_array_get_size(v_xs_542_);
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_nat_sub(v___x_543_, v___x_544_);
v___x_546_ = lean_nat_dec_lt(v___x_545_, v___x_543_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
lean_dec(v___x_545_);
v___x_547_ = lean_box(0);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_array_fget_borrowed(v_xs_542_, v___x_545_);
lean_dec(v___x_545_);
lean_inc(v___x_548_);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg___boxed(lean_object* v_xs_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Vector_back_x3f___redArg(v_xs_550_);
lean_dec_ref(v_xs_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f(lean_object* v_00_u03b1_552_, lean_object* v_n_553_, lean_object* v_xs_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_555_ = lean_array_get_size(v_xs_554_);
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_sub(v___x_555_, v___x_556_);
v___x_558_ = lean_nat_dec_lt(v___x_557_, v___x_555_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec(v___x_557_);
v___x_559_ = lean_box(0);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_array_fget_borrowed(v_xs_554_, v___x_557_);
lean_dec(v___x_557_);
lean_inc(v___x_560_);
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___boxed(lean_object* v_00_u03b1_562_, lean_object* v_n_563_, lean_object* v_xs_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Vector_back_x3f(v_00_u03b1_562_, v_n_563_, v_xs_564_);
lean_dec_ref(v_xs_564_);
lean_dec(v_n_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg(lean_object* v_n_566_, lean_object* v_xs_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_sub(v_n_566_, v___x_568_);
v___x_570_ = lean_array_fget_borrowed(v_xs_567_, v___x_569_);
lean_dec(v___x_569_);
lean_inc(v___x_570_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg___boxed(lean_object* v_n_571_, lean_object* v_xs_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Vector_back___redArg(v_n_571_, v_xs_572_);
lean_dec_ref(v_xs_572_);
lean_dec(v_n_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Vector_back(lean_object* v_n_574_, lean_object* v_00_u03b1_575_, lean_object* v_inst_576_, lean_object* v_xs_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_sub(v_n_574_, v___x_578_);
v___x_580_ = lean_array_fget_borrowed(v_xs_577_, v___x_579_);
lean_dec(v___x_579_);
lean_inc(v___x_580_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___boxed(lean_object* v_n_581_, lean_object* v_00_u03b1_582_, lean_object* v_inst_583_, lean_object* v_xs_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Vector_back(v_n_581_, v_00_u03b1_582_, v_inst_583_, v_xs_584_);
lean_dec_ref(v_xs_584_);
lean_dec(v_n_581_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg(lean_object* v_xs_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_array_fget_borrowed(v_xs_586_, v___x_587_);
lean_inc(v___x_588_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg___boxed(lean_object* v_xs_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Vector_head___redArg(v_xs_589_);
lean_dec_ref(v_xs_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Vector_head(lean_object* v_n_591_, lean_object* v_00_u03b1_592_, lean_object* v_inst_593_, lean_object* v_xs_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_array_fget_borrowed(v_xs_594_, v___x_595_);
lean_inc(v___x_596_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___boxed(lean_object* v_n_597_, lean_object* v_00_u03b1_598_, lean_object* v_inst_599_, lean_object* v_xs_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Vector_head(v_n_597_, v_00_u03b1_598_, v_inst_599_, v_xs_600_);
lean_dec_ref(v_xs_600_);
lean_dec(v_n_597_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___redArg(lean_object* v_xs_602_, lean_object* v_x_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = lean_array_push(v_xs_602_, v_x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Vector_push(lean_object* v_00_u03b1_605_, lean_object* v_n_606_, lean_object* v_xs_607_, lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_array_push(v_xs_607_, v_x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___boxed(lean_object* v_00_u03b1_610_, lean_object* v_n_611_, lean_object* v_xs_612_, lean_object* v_x_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Vector_push(v_00_u03b1_610_, v_n_611_, v_xs_612_, v_x_613_);
lean_dec(v_n_611_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___redArg(lean_object* v_xs_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_array_pop(v_xs_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop(lean_object* v_00_u03b1_617_, lean_object* v_n_618_, lean_object* v_xs_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_array_pop(v_xs_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___boxed(lean_object* v_00_u03b1_621_, lean_object* v_n_622_, lean_object* v_xs_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Vector_pop(v_00_u03b1_621_, v_n_622_, v_xs_623_);
lean_dec(v_n_622_);
return v_res_624_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__9(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Vector_set___auto__1___closed__8));
v___x_645_ = l_Lean_mkAtom(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__10(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_obj_once(&l_Vector_set___auto__1___closed__9, &l_Vector_set___auto__1___closed__9_once, _init_l_Vector_set___auto__1___closed__9);
v___x_647_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_648_ = lean_array_push(v___x_647_, v___x_646_);
return v___x_648_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__11(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_649_ = lean_obj_once(&l_Vector_set___auto__1___closed__10, &l_Vector_set___auto__1___closed__10_once, _init_l_Vector_set___auto__1___closed__10);
v___x_650_ = ((lean_object*)(l_Vector_set___auto__1___closed__7));
v___x_651_ = lean_box(2);
v___x_652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_650_);
lean_ctor_set(v___x_652_, 2, v___x_649_);
return v___x_652_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__12(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_obj_once(&l_Vector_set___auto__1___closed__11, &l_Vector_set___auto__1___closed__11_once, _init_l_Vector_set___auto__1___closed__11);
v___x_654_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_655_ = lean_array_push(v___x_654_, v___x_653_);
return v___x_655_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__13(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = lean_obj_once(&l_Vector_set___auto__1___closed__12, &l_Vector_set___auto__1___closed__12_once, _init_l_Vector_set___auto__1___closed__12);
v___x_657_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_658_ = lean_box(2);
v___x_659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
lean_ctor_set(v___x_659_, 2, v___x_656_);
return v___x_659_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__14(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = lean_obj_once(&l_Vector_set___auto__1___closed__13, &l_Vector_set___auto__1___closed__13_once, _init_l_Vector_set___auto__1___closed__13);
v___x_661_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_662_ = lean_array_push(v___x_661_, v___x_660_);
return v___x_662_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__15(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_663_ = lean_obj_once(&l_Vector_set___auto__1___closed__14, &l_Vector_set___auto__1___closed__14_once, _init_l_Vector_set___auto__1___closed__14);
v___x_664_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_665_ = lean_box(2);
v___x_666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___x_664_);
lean_ctor_set(v___x_666_, 2, v___x_663_);
return v___x_666_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__16(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_obj_once(&l_Vector_set___auto__1___closed__15, &l_Vector_set___auto__1___closed__15_once, _init_l_Vector_set___auto__1___closed__15);
v___x_668_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_669_ = lean_array_push(v___x_668_, v___x_667_);
return v___x_669_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__17(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_obj_once(&l_Vector_set___auto__1___closed__16, &l_Vector_set___auto__1___closed__16_once, _init_l_Vector_set___auto__1___closed__16);
v___x_671_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_672_ = lean_box(2);
v___x_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
lean_ctor_set(v___x_673_, 2, v___x_670_);
return v___x_673_;
}
}
static lean_object* _init_l_Vector_set___auto__1(void){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg(lean_object* v_xs_675_, lean_object* v_i_676_, lean_object* v_x_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_array_fset(v_xs_675_, v_i_676_, v_x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg___boxed(lean_object* v_xs_679_, lean_object* v_i_680_, lean_object* v_x_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Vector_set___redArg(v_xs_679_, v_i_680_, v_x_681_);
lean_dec(v_i_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Vector_set(lean_object* v_00_u03b1_683_, lean_object* v_n_684_, lean_object* v_xs_685_, lean_object* v_i_686_, lean_object* v_x_687_, lean_object* v_h_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_array_fset(v_xs_685_, v_i_686_, v_x_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___boxed(lean_object* v_00_u03b1_690_, lean_object* v_n_691_, lean_object* v_xs_692_, lean_object* v_i_693_, lean_object* v_x_694_, lean_object* v_h_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Vector_set(v_00_u03b1_690_, v_n_691_, v_xs_692_, v_i_693_, v_x_694_, v_h_695_);
lean_dec(v_i_693_);
lean_dec(v_n_691_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg(lean_object* v_xs_697_, lean_object* v_i_698_, lean_object* v_x_699_){
_start:
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_array_get_size(v_xs_697_);
v___x_701_ = lean_nat_dec_lt(v_i_698_, v___x_700_);
if (v___x_701_ == 0)
{
lean_dec(v_x_699_);
return v_xs_697_;
}
else
{
lean_object* v___x_702_; 
v___x_702_ = lean_array_fset(v_xs_697_, v_i_698_, v_x_699_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg___boxed(lean_object* v_xs_703_, lean_object* v_i_704_, lean_object* v_x_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Vector_setIfInBounds___redArg(v_xs_703_, v_i_704_, v_x_705_);
lean_dec(v_i_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds(lean_object* v_00_u03b1_707_, lean_object* v_n_708_, lean_object* v_xs_709_, lean_object* v_i_710_, lean_object* v_x_711_){
_start:
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_array_get_size(v_xs_709_);
v___x_713_ = lean_nat_dec_lt(v_i_710_, v___x_712_);
if (v___x_713_ == 0)
{
lean_dec(v_x_711_);
return v_xs_709_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_array_fset(v_xs_709_, v_i_710_, v_x_711_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___boxed(lean_object* v_00_u03b1_715_, lean_object* v_n_716_, lean_object* v_xs_717_, lean_object* v_i_718_, lean_object* v_x_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Vector_setIfInBounds(v_00_u03b1_715_, v_n_716_, v_xs_717_, v_i_718_, v_x_719_);
lean_dec(v_i_718_);
lean_dec(v_n_716_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg(lean_object* v_xs_721_, lean_object* v_i_722_, lean_object* v_x_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_array_set(v_xs_721_, v_i_722_, v_x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg___boxed(lean_object* v_xs_725_, lean_object* v_i_726_, lean_object* v_x_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Vector_set_x21___redArg(v_xs_725_, v_i_726_, v_x_727_);
lean_dec(v_i_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21(lean_object* v_00_u03b1_729_, lean_object* v_n_730_, lean_object* v_xs_731_, lean_object* v_i_732_, lean_object* v_x_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_array_set(v_xs_731_, v_i_732_, v_x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___boxed(lean_object* v_00_u03b1_735_, lean_object* v_n_736_, lean_object* v_xs_737_, lean_object* v_i_738_, lean_object* v_x_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Vector_set_x21(v_00_u03b1_735_, v_n_736_, v_xs_737_, v_i_738_, v_x_739_);
lean_dec(v_i_738_);
lean_dec(v_n_736_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___redArg(lean_object* v_inst_741_, lean_object* v_f_742_, lean_object* v_b_743_, lean_object* v_xs_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_array_get_size(v_xs_744_);
v___x_747_ = lean_nat_dec_lt(v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v_toApplicative_748_; lean_object* v_toPure_749_; lean_object* v___x_750_; 
lean_dec_ref(v_xs_744_);
lean_dec(v_f_742_);
v_toApplicative_748_ = lean_ctor_get(v_inst_741_, 0);
lean_inc_ref(v_toApplicative_748_);
lean_dec_ref(v_inst_741_);
v_toPure_749_ = lean_ctor_get(v_toApplicative_748_, 1);
lean_inc(v_toPure_749_);
lean_dec_ref(v_toApplicative_748_);
v___x_750_ = lean_apply_2(v_toPure_749_, lean_box(0), v_b_743_);
return v___x_750_;
}
else
{
uint8_t v___x_751_; 
v___x_751_ = lean_nat_dec_le(v___x_746_, v___x_746_);
if (v___x_751_ == 0)
{
if (v___x_747_ == 0)
{
lean_object* v_toApplicative_752_; lean_object* v_toPure_753_; lean_object* v___x_754_; 
lean_dec_ref(v_xs_744_);
lean_dec(v_f_742_);
v_toApplicative_752_ = lean_ctor_get(v_inst_741_, 0);
lean_inc_ref(v_toApplicative_752_);
lean_dec_ref(v_inst_741_);
v_toPure_753_ = lean_ctor_get(v_toApplicative_752_, 1);
lean_inc(v_toPure_753_);
lean_dec_ref(v_toApplicative_752_);
v___x_754_ = lean_apply_2(v_toPure_753_, lean_box(0), v_b_743_);
return v___x_754_;
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_of_nat(v___x_746_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_741_, v_f_742_, v_xs_744_, v___x_755_, v___x_756_, v_b_743_);
return v___x_757_;
}
}
else
{
size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
v___x_758_ = ((size_t)0ULL);
v___x_759_ = lean_usize_of_nat(v___x_746_);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_741_, v_f_742_, v_xs_744_, v___x_758_, v___x_759_, v_b_743_);
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM(lean_object* v_m_761_, lean_object* v_00_u03b2_762_, lean_object* v_00_u03b1_763_, lean_object* v_n_764_, lean_object* v_inst_765_, lean_object* v_f_766_, lean_object* v_b_767_, lean_object* v_xs_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_array_get_size(v_xs_768_);
v___x_771_ = lean_nat_dec_lt(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v_toApplicative_772_; lean_object* v_toPure_773_; lean_object* v___x_774_; 
lean_dec_ref(v_xs_768_);
lean_dec(v_f_766_);
v_toApplicative_772_ = lean_ctor_get(v_inst_765_, 0);
lean_inc_ref(v_toApplicative_772_);
lean_dec_ref(v_inst_765_);
v_toPure_773_ = lean_ctor_get(v_toApplicative_772_, 1);
lean_inc(v_toPure_773_);
lean_dec_ref(v_toApplicative_772_);
v___x_774_ = lean_apply_2(v_toPure_773_, lean_box(0), v_b_767_);
return v___x_774_;
}
else
{
uint8_t v___x_775_; 
v___x_775_ = lean_nat_dec_le(v___x_770_, v___x_770_);
if (v___x_775_ == 0)
{
if (v___x_771_ == 0)
{
lean_object* v_toApplicative_776_; lean_object* v_toPure_777_; lean_object* v___x_778_; 
lean_dec_ref(v_xs_768_);
lean_dec(v_f_766_);
v_toApplicative_776_ = lean_ctor_get(v_inst_765_, 0);
lean_inc_ref(v_toApplicative_776_);
lean_dec_ref(v_inst_765_);
v_toPure_777_ = lean_ctor_get(v_toApplicative_776_, 1);
lean_inc(v_toPure_777_);
lean_dec_ref(v_toApplicative_776_);
v___x_778_ = lean_apply_2(v_toPure_777_, lean_box(0), v_b_767_);
return v___x_778_;
}
else
{
size_t v___x_779_; size_t v___x_780_; lean_object* v___x_781_; 
v___x_779_ = ((size_t)0ULL);
v___x_780_ = lean_usize_of_nat(v___x_770_);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_765_, v_f_766_, v_xs_768_, v___x_779_, v___x_780_, v_b_767_);
return v___x_781_;
}
}
else
{
size_t v___x_782_; size_t v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((size_t)0ULL);
v___x_783_ = lean_usize_of_nat(v___x_770_);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_765_, v_f_766_, v_xs_768_, v___x_782_, v___x_783_, v_b_767_);
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___boxed(lean_object* v_m_785_, lean_object* v_00_u03b2_786_, lean_object* v_00_u03b1_787_, lean_object* v_n_788_, lean_object* v_inst_789_, lean_object* v_f_790_, lean_object* v_b_791_, lean_object* v_xs_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Vector_foldlM(v_m_785_, v_00_u03b2_786_, v_00_u03b1_787_, v_n_788_, v_inst_789_, v_f_790_, v_b_791_, v_xs_792_);
lean_dec(v_n_788_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___redArg(lean_object* v_inst_794_, lean_object* v_f_795_, lean_object* v_b_796_, lean_object* v_xs_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_798_ = lean_array_get_size(v_xs_797_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_nat_dec_lt(v___x_799_, v___x_798_);
if (v___x_800_ == 0)
{
lean_object* v_toApplicative_801_; lean_object* v_toPure_802_; lean_object* v___x_803_; 
lean_dec_ref(v_xs_797_);
lean_dec(v_f_795_);
v_toApplicative_801_ = lean_ctor_get(v_inst_794_, 0);
lean_inc_ref(v_toApplicative_801_);
lean_dec_ref(v_inst_794_);
v_toPure_802_ = lean_ctor_get(v_toApplicative_801_, 1);
lean_inc(v_toPure_802_);
lean_dec_ref(v_toApplicative_801_);
v___x_803_ = lean_apply_2(v_toPure_802_, lean_box(0), v_b_796_);
return v___x_803_;
}
else
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_804_ = lean_usize_of_nat(v___x_798_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_794_, v_f_795_, v_xs_797_, v___x_804_, v___x_805_, v_b_796_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM(lean_object* v_m_807_, lean_object* v_00_u03b1_808_, lean_object* v_00_u03b2_809_, lean_object* v_n_810_, lean_object* v_inst_811_, lean_object* v_f_812_, lean_object* v_b_813_, lean_object* v_xs_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_815_ = lean_array_get_size(v_xs_814_);
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = lean_nat_dec_lt(v___x_816_, v___x_815_);
if (v___x_817_ == 0)
{
lean_object* v_toApplicative_818_; lean_object* v_toPure_819_; lean_object* v___x_820_; 
lean_dec_ref(v_xs_814_);
lean_dec(v_f_812_);
v_toApplicative_818_ = lean_ctor_get(v_inst_811_, 0);
lean_inc_ref(v_toApplicative_818_);
lean_dec_ref(v_inst_811_);
v_toPure_819_ = lean_ctor_get(v_toApplicative_818_, 1);
lean_inc(v_toPure_819_);
lean_dec_ref(v_toApplicative_818_);
v___x_820_ = lean_apply_2(v_toPure_819_, lean_box(0), v_b_813_);
return v___x_820_;
}
else
{
size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_usize_of_nat(v___x_815_);
v___x_822_ = ((size_t)0ULL);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_811_, v_f_812_, v_xs_814_, v___x_821_, v___x_822_, v_b_813_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___boxed(lean_object* v_m_824_, lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_n_827_, lean_object* v_inst_828_, lean_object* v_f_829_, lean_object* v_b_830_, lean_object* v_xs_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Vector_foldrM(v_m_824_, v_00_u03b1_825_, v_00_u03b2_826_, v_n_827_, v_inst_828_, v_f_829_, v_b_830_, v_xs_831_);
lean_dec(v_n_827_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg___lam__0(lean_object* v_f_833_, lean_object* v_x1_834_, lean_object* v_x2_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = lean_apply_2(v_f_833_, v_x1_834_, v_x2_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg(lean_object* v_f_856_, lean_object* v_b_857_, lean_object* v_xs_858_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = lean_array_get_size(v_xs_858_);
v___x_861_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_862_ = lean_nat_dec_lt(v___x_859_, v___x_860_);
if (v___x_862_ == 0)
{
lean_dec_ref(v_xs_858_);
lean_dec(v_f_856_);
return v_b_857_;
}
else
{
lean_object* v___f_863_; uint8_t v___x_864_; 
v___f_863_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_863_, 0, v_f_856_);
v___x_864_ = lean_nat_dec_le(v___x_860_, v___x_860_);
if (v___x_864_ == 0)
{
if (v___x_862_ == 0)
{
lean_dec_ref(v___f_863_);
lean_dec_ref(v_xs_858_);
return v_b_857_;
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_860_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_861_, v___f_863_, v_xs_858_, v___x_865_, v___x_866_, v_b_857_);
return v___x_867_;
}
}
else
{
size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((size_t)0ULL);
v___x_869_ = lean_usize_of_nat(v___x_860_);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_861_, v___f_863_, v_xs_858_, v___x_868_, v___x_869_, v_b_857_);
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl(lean_object* v_00_u03b2_871_, lean_object* v_00_u03b1_872_, lean_object* v_n_873_, lean_object* v_f_874_, lean_object* v_b_875_, lean_object* v_xs_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_array_get_size(v_xs_876_);
v___x_879_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_880_ = lean_nat_dec_lt(v___x_877_, v___x_878_);
if (v___x_880_ == 0)
{
lean_dec_ref(v_xs_876_);
lean_dec(v_f_874_);
return v_b_875_;
}
else
{
lean_object* v___f_881_; uint8_t v___x_882_; 
v___f_881_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_881_, 0, v_f_874_);
v___x_882_ = lean_nat_dec_le(v___x_878_, v___x_878_);
if (v___x_882_ == 0)
{
if (v___x_880_ == 0)
{
lean_dec_ref(v___f_881_);
lean_dec_ref(v_xs_876_);
return v_b_875_;
}
else
{
size_t v___x_883_; size_t v___x_884_; lean_object* v___x_885_; 
v___x_883_ = ((size_t)0ULL);
v___x_884_ = lean_usize_of_nat(v___x_878_);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_879_, v___f_881_, v_xs_876_, v___x_883_, v___x_884_, v_b_875_);
return v___x_885_;
}
}
else
{
size_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; 
v___x_886_ = ((size_t)0ULL);
v___x_887_ = lean_usize_of_nat(v___x_878_);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_879_, v___f_881_, v_xs_876_, v___x_886_, v___x_887_, v_b_875_);
return v___x_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___boxed(lean_object* v_00_u03b2_889_, lean_object* v_00_u03b1_890_, lean_object* v_n_891_, lean_object* v_f_892_, lean_object* v_b_893_, lean_object* v_xs_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Vector_foldl(v_00_u03b2_889_, v_00_u03b1_890_, v_n_891_, v_f_892_, v_b_893_, v_xs_894_);
lean_dec(v_n_891_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___redArg(lean_object* v_f_896_, lean_object* v_b_897_, lean_object* v_xs_898_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_899_ = lean_array_get_size(v_xs_898_);
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_902_ = lean_nat_dec_lt(v___x_900_, v___x_899_);
if (v___x_902_ == 0)
{
lean_dec_ref(v_xs_898_);
lean_dec(v_f_896_);
return v_b_897_;
}
else
{
lean_object* v___f_903_; size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; 
v___f_903_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_903_, 0, v_f_896_);
v___x_904_ = lean_usize_of_nat(v___x_899_);
v___x_905_ = ((size_t)0ULL);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_901_, v___f_903_, v_xs_898_, v___x_904_, v___x_905_, v_b_897_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_n_909_, lean_object* v_f_910_, lean_object* v_b_911_, lean_object* v_xs_912_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_913_ = lean_array_get_size(v_xs_912_);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_916_ = lean_nat_dec_lt(v___x_914_, v___x_913_);
if (v___x_916_ == 0)
{
lean_dec_ref(v_xs_912_);
lean_dec(v_f_910_);
return v_b_911_;
}
else
{
lean_object* v___f_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; 
v___f_917_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_917_, 0, v_f_910_);
v___x_918_ = lean_usize_of_nat(v___x_913_);
v___x_919_ = ((size_t)0ULL);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_915_, v___f_917_, v_xs_912_, v___x_918_, v___x_919_, v_b_911_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___boxed(lean_object* v_00_u03b1_921_, lean_object* v_00_u03b2_922_, lean_object* v_n_923_, lean_object* v_f_924_, lean_object* v_b_925_, lean_object* v_xs_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Vector_foldr(v_00_u03b1_921_, v_00_u03b2_922_, v_n_923_, v_f_924_, v_b_925_, v_xs_926_);
lean_dec(v_n_923_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg(lean_object* v_xs_928_, lean_object* v_ys_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Array_append___redArg(v_xs_928_, v_ys_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg___boxed(lean_object* v_xs_931_, lean_object* v_ys_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Vector_append___redArg(v_xs_931_, v_ys_932_);
lean_dec_ref(v_ys_932_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Vector_append(lean_object* v_00_u03b1_934_, lean_object* v_n_935_, lean_object* v_m_936_, lean_object* v_xs_937_, lean_object* v_ys_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Array_append___redArg(v_xs_937_, v_ys_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___boxed(lean_object* v_00_u03b1_940_, lean_object* v_n_941_, lean_object* v_m_942_, lean_object* v_xs_943_, lean_object* v_ys_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Vector_append(v_00_u03b1_940_, v_n_941_, v_m_942_, v_xs_943_, v_ys_944_);
lean_dec_ref(v_ys_944_);
lean_dec(v_m_942_);
lean_dec(v_n_941_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat___redArg(lean_object* v_n_946_, lean_object* v_m_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_948_, 0, lean_box(0));
lean_closure_set(v___x_948_, 1, v_n_946_);
lean_closure_set(v___x_948_, 2, v_m_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat(lean_object* v_00_u03b1_949_, lean_object* v_n_950_, lean_object* v_m_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_952_, 0, lean_box(0));
lean_closure_set(v___x_952_, 1, v_n_950_);
lean_closure_set(v___x_952_, 2, v_m_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg(lean_object* v_xs_953_){
_start:
{
lean_inc_ref(v_xs_953_);
return v_xs_953_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg___boxed(lean_object* v_xs_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Vector_cast___redArg(v_xs_954_);
lean_dec_ref(v_xs_954_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast(lean_object* v_n_956_, lean_object* v_m_957_, lean_object* v_00_u03b1_958_, lean_object* v_h_959_, lean_object* v_xs_960_){
_start:
{
lean_inc_ref(v_xs_960_);
return v_xs_960_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___boxed(lean_object* v_n_961_, lean_object* v_m_962_, lean_object* v_00_u03b1_963_, lean_object* v_h_964_, lean_object* v_xs_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Vector_cast(v_n_961_, v_m_962_, v_00_u03b1_963_, v_h_964_, v_xs_965_);
lean_dec_ref(v_xs_965_);
lean_dec(v_m_962_);
lean_dec(v_n_961_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg(lean_object* v_xs_967_, lean_object* v_start_968_, lean_object* v_stop_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Array_extract___redArg(v_xs_967_, v_start_968_, v_stop_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg___boxed(lean_object* v_xs_971_, lean_object* v_start_972_, lean_object* v_stop_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Vector_extract___redArg(v_xs_971_, v_start_972_, v_stop_973_);
lean_dec_ref(v_xs_971_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract(lean_object* v_00_u03b1_975_, lean_object* v_n_976_, lean_object* v_xs_977_, lean_object* v_start_978_, lean_object* v_stop_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Array_extract___redArg(v_xs_977_, v_start_978_, v_stop_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___boxed(lean_object* v_00_u03b1_981_, lean_object* v_n_982_, lean_object* v_xs_983_, lean_object* v_start_984_, lean_object* v_stop_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Vector_extract(v_00_u03b1_981_, v_n_982_, v_xs_983_, v_start_984_, v_stop_985_);
lean_dec_ref(v_xs_983_);
lean_dec(v_n_982_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg(lean_object* v_n_987_, lean_object* v_xs_988_, lean_object* v_i_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = l_Array_extract___redArg(v_xs_988_, v___x_990_, v_i_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg___boxed(lean_object* v_n_992_, lean_object* v_xs_993_, lean_object* v_i_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Vector_take___redArg(v_n_992_, v_xs_993_, v_i_994_);
lean_dec_ref(v_xs_993_);
lean_dec(v_n_992_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Vector_take(lean_object* v_00_u03b1_996_, lean_object* v_n_997_, lean_object* v_xs_998_, lean_object* v_i_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = l_Array_extract___redArg(v_xs_998_, v___x_1000_, v_i_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___boxed(lean_object* v_00_u03b1_1002_, lean_object* v_n_1003_, lean_object* v_xs_1004_, lean_object* v_i_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Vector_take(v_00_u03b1_1002_, v_n_1003_, v_xs_1004_, v_i_1005_);
lean_dec_ref(v_xs_1004_);
lean_dec(v_n_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg(lean_object* v_xs_1007_, lean_object* v_i_1008_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_array_get_size(v_xs_1007_);
v___x_1010_ = l_Array_extract___redArg(v_xs_1007_, v_i_1008_, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg___boxed(lean_object* v_xs_1011_, lean_object* v_i_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Vector_drop___redArg(v_xs_1011_, v_i_1012_);
lean_dec_ref(v_xs_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop(lean_object* v_00_u03b1_1014_, lean_object* v_n_1015_, lean_object* v_xs_1016_, lean_object* v_i_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_array_get_size(v_xs_1016_);
v___x_1019_ = l_Array_extract___redArg(v_xs_1016_, v_i_1017_, v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___boxed(lean_object* v_00_u03b1_1020_, lean_object* v_n_1021_, lean_object* v_xs_1022_, lean_object* v_i_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Vector_drop(v_00_u03b1_1020_, v_n_1021_, v_xs_1022_, v_i_1023_);
lean_dec_ref(v_xs_1022_);
lean_dec(v_n_1021_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg(lean_object* v_xs_1025_, lean_object* v_i_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Array_shrink___redArg(v_xs_1025_, v_i_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg___boxed(lean_object* v_xs_1028_, lean_object* v_i_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Vector_shrink___redArg(v_xs_1028_, v_i_1029_);
lean_dec(v_i_1029_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink(lean_object* v_00_u03b1_1031_, lean_object* v_n_1032_, lean_object* v_xs_1033_, lean_object* v_i_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Array_shrink___redArg(v_xs_1033_, v_i_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___boxed(lean_object* v_00_u03b1_1036_, lean_object* v_n_1037_, lean_object* v_xs_1038_, lean_object* v_i_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Vector_shrink(v_00_u03b1_1036_, v_n_1037_, v_xs_1038_, v_i_1039_);
lean_dec(v_i_1039_);
lean_dec(v_n_1037_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg___lam__0(lean_object* v_f_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_apply_1(v_f_1041_, v_x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg(lean_object* v_f_1044_, lean_object* v_xs_1045_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; size_t v_sz_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
v___f_1046_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1046_, 0, v_f_1044_);
v___x_1047_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1048_ = lean_array_size(v_xs_1045_);
v___x_1049_ = ((size_t)0ULL);
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1047_, v___f_1046_, v_sz_1048_, v___x_1049_, v_xs_1045_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Vector_map(lean_object* v_00_u03b1_1051_, lean_object* v_00_u03b2_1052_, lean_object* v_n_1053_, lean_object* v_f_1054_, lean_object* v_xs_1055_){
_start:
{
lean_object* v___f_1056_; lean_object* v___x_1057_; size_t v_sz_1058_; size_t v___x_1059_; lean_object* v___x_1060_; 
v___f_1056_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1056_, 0, v_f_1054_);
v___x_1057_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1058_ = lean_array_size(v_xs_1055_);
v___x_1059_ = ((size_t)0ULL);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1057_, v___f_1056_, v_sz_1058_, v___x_1059_, v_xs_1055_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_00_u03b2_1062_, lean_object* v_n_1063_, lean_object* v_f_1064_, lean_object* v_xs_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Vector_map(v_00_u03b1_1061_, v_00_u03b2_1062_, v_n_1063_, v_f_1064_, v_xs_1065_);
lean_dec(v_n_1063_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg___lam__0(lean_object* v_f_1067_, lean_object* v_i_1068_, lean_object* v_a_1069_, lean_object* v_x_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_apply_2(v_f_1067_, v_i_1068_, v_a_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg(lean_object* v_f_1072_, lean_object* v_xs_1073_){
_start:
{
lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___f_1074_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1074_, 0, v_f_1072_);
v___x_1075_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1076_ = lean_array_get_size(v_xs_1073_);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_mk_empty_array_with_capacity(v___x_1076_);
v___x_1079_ = l_Array_mapFinIdxM_map___redArg(v___x_1075_, v_xs_1073_, v___f_1074_, v___x_1076_, v___x_1077_, v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx(lean_object* v_00_u03b1_1080_, lean_object* v_00_u03b2_1081_, lean_object* v_n_1082_, lean_object* v_f_1083_, lean_object* v_xs_1084_){
_start:
{
lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___f_1085_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1085_, 0, v_f_1083_);
v___x_1086_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1087_ = lean_array_get_size(v_xs_1084_);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = lean_mk_empty_array_with_capacity(v___x_1087_);
v___x_1090_ = l_Array_mapFinIdxM_map___redArg(v___x_1086_, v_xs_1084_, v___f_1085_, v___x_1087_, v___x_1088_, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___boxed(lean_object* v_00_u03b1_1091_, lean_object* v_00_u03b2_1092_, lean_object* v_n_1093_, lean_object* v_f_1094_, lean_object* v_xs_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Vector_mapIdx(v_00_u03b1_1091_, v_00_u03b2_1092_, v_n_1093_, v_f_1094_, v_xs_1095_);
lean_dec(v_n_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg___lam__0(lean_object* v_f_1097_, lean_object* v_x1_1098_, lean_object* v_x2_1099_, lean_object* v_x3_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_apply_3(v_f_1097_, v_x1_1098_, v_x2_1099_, lean_box(0));
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg(lean_object* v_xs_1102_, lean_object* v_f_1103_){
_start:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___f_1104_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1104_, 0, v_f_1103_);
v___x_1105_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1106_ = lean_array_get_size(v_xs_1102_);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_mk_empty_array_with_capacity(v___x_1106_);
v___x_1109_ = l_Array_mapFinIdxM_map___redArg(v___x_1105_, v_xs_1102_, v___f_1104_, v___x_1106_, v___x_1107_, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx(lean_object* v_00_u03b1_1110_, lean_object* v_n_1111_, lean_object* v_00_u03b2_1112_, lean_object* v_xs_1113_, lean_object* v_f_1114_){
_start:
{
lean_object* v___f_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___f_1115_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1115_, 0, v_f_1114_);
v___x_1116_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1117_ = lean_array_get_size(v_xs_1113_);
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = lean_mk_empty_array_with_capacity(v___x_1117_);
v___x_1120_ = l_Array_mapFinIdxM_map___redArg(v___x_1116_, v_xs_1113_, v___f_1115_, v___x_1117_, v___x_1118_, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___boxed(lean_object* v_00_u03b1_1121_, lean_object* v_n_1122_, lean_object* v_00_u03b2_1123_, lean_object* v_xs_1124_, lean_object* v_f_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Vector_mapFinIdx(v_00_u03b1_1121_, v_n_1122_, v_00_u03b2_1123_, v_xs_1124_, v_f_1125_);
lean_dec(v_n_1122_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(lean_object* v_k_1127_, lean_object* v_acc_1128_, lean_object* v_n_1129_, lean_object* v_inst_1130_, lean_object* v_f_1131_, lean_object* v_xs_1132_, lean_object* v_____do__lift_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(v_k_1127_, v_acc_1128_, v_n_1129_, v_inst_1130_, v_f_1131_, v_xs_1132_, v_____do__lift_1133_);
lean_dec(v_k_1127_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(lean_object* v_n_1135_, lean_object* v_inst_1136_, lean_object* v_f_1137_, lean_object* v_xs_1138_, lean_object* v_k_1139_, lean_object* v_acc_1140_){
_start:
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_nat_dec_lt(v_k_1139_, v_n_1135_);
if (v___x_1141_ == 0)
{
lean_object* v_toApplicative_1142_; lean_object* v_toPure_1143_; lean_object* v___x_1144_; 
lean_dec(v_k_1139_);
lean_dec_ref(v_xs_1138_);
lean_dec(v_f_1137_);
lean_dec(v_n_1135_);
v_toApplicative_1142_ = lean_ctor_get(v_inst_1136_, 0);
lean_inc_ref(v_toApplicative_1142_);
lean_dec_ref(v_inst_1136_);
v_toPure_1143_ = lean_ctor_get(v_toApplicative_1142_, 1);
lean_inc(v_toPure_1143_);
lean_dec_ref(v_toApplicative_1142_);
v___x_1144_ = lean_apply_2(v_toPure_1143_, lean_box(0), v_acc_1140_);
return v___x_1144_;
}
else
{
lean_object* v_toBind_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v_toBind_1145_ = lean_ctor_get(v_inst_1136_, 1);
lean_inc(v_toBind_1145_);
lean_inc_ref(v_xs_1138_);
lean_inc(v_f_1137_);
lean_inc(v_k_1139_);
v___f_1146_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1146_, 0, v_k_1139_);
lean_closure_set(v___f_1146_, 1, v_acc_1140_);
lean_closure_set(v___f_1146_, 2, v_n_1135_);
lean_closure_set(v___f_1146_, 3, v_inst_1136_);
lean_closure_set(v___f_1146_, 4, v_f_1137_);
lean_closure_set(v___f_1146_, 5, v_xs_1138_);
v___x_1147_ = lean_array_fget(v_xs_1138_, v_k_1139_);
lean_dec(v_k_1139_);
lean_dec_ref(v_xs_1138_);
v___x_1148_ = lean_apply_1(v_f_1137_, v___x_1147_);
v___x_1149_ = lean_apply_4(v_toBind_1145_, lean_box(0), lean_box(0), v___x_1148_, v___f_1146_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(lean_object* v_k_1150_, lean_object* v_acc_1151_, lean_object* v_n_1152_, lean_object* v_inst_1153_, lean_object* v_f_1154_, lean_object* v_xs_1155_, lean_object* v_____do__lift_1156_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = lean_nat_add(v_k_1150_, v___x_1157_);
v___x_1159_ = lean_array_push(v_acc_1151_, v_____do__lift_1156_);
v___x_1160_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1152_, v_inst_1153_, v_f_1154_, v_xs_1155_, v___x_1158_, v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(lean_object* v_m_1161_, lean_object* v_00_u03b1_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_n_1164_, lean_object* v_inst_1165_, lean_object* v_f_1166_, lean_object* v_xs_1167_, lean_object* v_k_1168_, lean_object* v_h_1169_, lean_object* v_acc_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1164_, v_inst_1165_, v_f_1166_, v_xs_1167_, v_k_1168_, v_acc_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM___redArg(lean_object* v_n_1174_, lean_object* v_inst_1175_, lean_object* v_f_1176_, lean_object* v_xs_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_unsigned_to_nat(0u);
v___x_1179_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1180_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1174_, v_inst_1175_, v_f_1176_, v_xs_1177_, v___x_1178_, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM(lean_object* v_m_1181_, lean_object* v_00_u03b1_1182_, lean_object* v_00_u03b2_1183_, lean_object* v_n_1184_, lean_object* v_inst_1185_, lean_object* v_f_1186_, lean_object* v_xs_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1190_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1184_, v_inst_1185_, v_f_1186_, v_xs_1187_, v___x_1188_, v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg___lam__0(lean_object* v_f_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_apply_1(v_f_1191_, v___y_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg(lean_object* v_inst_1195_, lean_object* v_xs_1196_, lean_object* v_f_1197_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_array_get_size(v_xs_1196_);
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_nat_dec_lt(v___x_1198_, v___x_1199_);
if (v___x_1201_ == 0)
{
lean_object* v_toApplicative_1202_; lean_object* v_toPure_1203_; lean_object* v___x_1204_; 
lean_dec(v_f_1197_);
lean_dec_ref(v_xs_1196_);
v_toApplicative_1202_ = lean_ctor_get(v_inst_1195_, 0);
lean_inc_ref(v_toApplicative_1202_);
lean_dec_ref(v_inst_1195_);
v_toPure_1203_ = lean_ctor_get(v_toApplicative_1202_, 1);
lean_inc(v_toPure_1203_);
lean_dec_ref(v_toApplicative_1202_);
v___x_1204_ = lean_apply_2(v_toPure_1203_, lean_box(0), v___x_1200_);
return v___x_1204_;
}
else
{
lean_object* v___f_1205_; uint8_t v___x_1206_; 
v___f_1205_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1205_, 0, v_f_1197_);
v___x_1206_ = lean_nat_dec_le(v___x_1199_, v___x_1199_);
if (v___x_1206_ == 0)
{
if (v___x_1201_ == 0)
{
lean_object* v_toApplicative_1207_; lean_object* v_toPure_1208_; lean_object* v___x_1209_; 
lean_dec_ref(v___f_1205_);
lean_dec_ref(v_xs_1196_);
v_toApplicative_1207_ = lean_ctor_get(v_inst_1195_, 0);
lean_inc_ref(v_toApplicative_1207_);
lean_dec_ref(v_inst_1195_);
v_toPure_1208_ = lean_ctor_get(v_toApplicative_1207_, 1);
lean_inc(v_toPure_1208_);
lean_dec_ref(v_toApplicative_1207_);
v___x_1209_ = lean_apply_2(v_toPure_1208_, lean_box(0), v___x_1200_);
return v___x_1209_;
}
else
{
size_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = ((size_t)0ULL);
v___x_1211_ = lean_usize_of_nat(v___x_1199_);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1195_, v___f_1205_, v_xs_1196_, v___x_1210_, v___x_1211_, v___x_1200_);
return v___x_1212_;
}
}
else
{
size_t v___x_1213_; size_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = ((size_t)0ULL);
v___x_1214_ = lean_usize_of_nat(v___x_1199_);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1195_, v___f_1205_, v_xs_1196_, v___x_1213_, v___x_1214_, v___x_1200_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM(lean_object* v_m_1216_, lean_object* v_00_u03b1_1217_, lean_object* v_n_1218_, lean_object* v_inst_1219_, lean_object* v_xs_1220_, lean_object* v_f_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1222_ = lean_unsigned_to_nat(0u);
v___x_1223_ = lean_array_get_size(v_xs_1220_);
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_nat_dec_lt(v___x_1222_, v___x_1223_);
if (v___x_1225_ == 0)
{
lean_object* v_toApplicative_1226_; lean_object* v_toPure_1227_; lean_object* v___x_1228_; 
lean_dec(v_f_1221_);
lean_dec_ref(v_xs_1220_);
v_toApplicative_1226_ = lean_ctor_get(v_inst_1219_, 0);
lean_inc_ref(v_toApplicative_1226_);
lean_dec_ref(v_inst_1219_);
v_toPure_1227_ = lean_ctor_get(v_toApplicative_1226_, 1);
lean_inc(v_toPure_1227_);
lean_dec_ref(v_toApplicative_1226_);
v___x_1228_ = lean_apply_2(v_toPure_1227_, lean_box(0), v___x_1224_);
return v___x_1228_;
}
else
{
lean_object* v___f_1229_; uint8_t v___x_1230_; 
v___f_1229_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1229_, 0, v_f_1221_);
v___x_1230_ = lean_nat_dec_le(v___x_1223_, v___x_1223_);
if (v___x_1230_ == 0)
{
if (v___x_1225_ == 0)
{
lean_object* v_toApplicative_1231_; lean_object* v_toPure_1232_; lean_object* v___x_1233_; 
lean_dec_ref(v___f_1229_);
lean_dec_ref(v_xs_1220_);
v_toApplicative_1231_ = lean_ctor_get(v_inst_1219_, 0);
lean_inc_ref(v_toApplicative_1231_);
lean_dec_ref(v_inst_1219_);
v_toPure_1232_ = lean_ctor_get(v_toApplicative_1231_, 1);
lean_inc(v_toPure_1232_);
lean_dec_ref(v_toApplicative_1231_);
v___x_1233_ = lean_apply_2(v_toPure_1232_, lean_box(0), v___x_1224_);
return v___x_1233_;
}
else
{
size_t v___x_1234_; size_t v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = ((size_t)0ULL);
v___x_1235_ = lean_usize_of_nat(v___x_1223_);
v___x_1236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1219_, v___f_1229_, v_xs_1220_, v___x_1234_, v___x_1235_, v___x_1224_);
return v___x_1236_;
}
}
else
{
size_t v___x_1237_; size_t v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = ((size_t)0ULL);
v___x_1238_ = lean_usize_of_nat(v___x_1223_);
v___x_1239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1219_, v___f_1229_, v_xs_1220_, v___x_1237_, v___x_1238_, v___x_1224_);
return v___x_1239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM___boxed(lean_object* v_m_1240_, lean_object* v_00_u03b1_1241_, lean_object* v_n_1242_, lean_object* v_inst_1243_, lean_object* v_xs_1244_, lean_object* v_f_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Vector_forM(v_m_1240_, v_00_u03b1_1241_, v_n_1242_, v_inst_1243_, v_xs_1244_, v_f_1245_);
lean_dec(v_n_1242_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(lean_object* v_i_1247_, lean_object* v_acc_1248_, lean_object* v_n_1249_, lean_object* v_inst_1250_, lean_object* v_xs_1251_, lean_object* v_f_1252_, lean_object* v_____do__lift_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(v_i_1247_, v_acc_1248_, v_n_1249_, v_inst_1250_, v_xs_1251_, v_f_1252_, v_____do__lift_1253_);
lean_dec_ref(v_____do__lift_1253_);
lean_dec(v_i_1247_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(lean_object* v_n_1255_, lean_object* v_inst_1256_, lean_object* v_xs_1257_, lean_object* v_f_1258_, lean_object* v_i_1259_, lean_object* v_acc_1260_){
_start:
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_nat_dec_lt(v_i_1259_, v_n_1255_);
if (v___x_1261_ == 0)
{
lean_object* v_toApplicative_1262_; lean_object* v_toPure_1263_; lean_object* v___x_1264_; 
lean_dec(v_i_1259_);
lean_dec(v_f_1258_);
lean_dec_ref(v_xs_1257_);
lean_dec(v_n_1255_);
v_toApplicative_1262_ = lean_ctor_get(v_inst_1256_, 0);
lean_inc_ref(v_toApplicative_1262_);
lean_dec_ref(v_inst_1256_);
v_toPure_1263_ = lean_ctor_get(v_toApplicative_1262_, 1);
lean_inc(v_toPure_1263_);
lean_dec_ref(v_toApplicative_1262_);
v___x_1264_ = lean_apply_2(v_toPure_1263_, lean_box(0), v_acc_1260_);
return v___x_1264_;
}
else
{
lean_object* v_toBind_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_toBind_1265_ = lean_ctor_get(v_inst_1256_, 1);
lean_inc(v_toBind_1265_);
lean_inc(v_f_1258_);
lean_inc_ref(v_xs_1257_);
lean_inc(v_i_1259_);
v___f_1266_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1266_, 0, v_i_1259_);
lean_closure_set(v___f_1266_, 1, v_acc_1260_);
lean_closure_set(v___f_1266_, 2, v_n_1255_);
lean_closure_set(v___f_1266_, 3, v_inst_1256_);
lean_closure_set(v___f_1266_, 4, v_xs_1257_);
lean_closure_set(v___f_1266_, 5, v_f_1258_);
v___x_1267_ = lean_array_fget(v_xs_1257_, v_i_1259_);
lean_dec(v_i_1259_);
lean_dec_ref(v_xs_1257_);
v___x_1268_ = lean_apply_1(v_f_1258_, v___x_1267_);
v___x_1269_ = lean_apply_4(v_toBind_1265_, lean_box(0), lean_box(0), v___x_1268_, v___f_1266_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(lean_object* v_i_1270_, lean_object* v_acc_1271_, lean_object* v_n_1272_, lean_object* v_inst_1273_, lean_object* v_xs_1274_, lean_object* v_f_1275_, lean_object* v_____do__lift_1276_){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_nat_add(v_i_1270_, v___x_1277_);
v___x_1279_ = l_Array_append___redArg(v_acc_1271_, v_____do__lift_1276_);
v___x_1280_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1272_, v_inst_1273_, v_xs_1274_, v_f_1275_, v___x_1278_, v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(lean_object* v_m_1281_, lean_object* v_00_u03b1_1282_, lean_object* v_n_1283_, lean_object* v_00_u03b2_1284_, lean_object* v_k_1285_, lean_object* v_inst_1286_, lean_object* v_xs_1287_, lean_object* v_f_1288_, lean_object* v_i_1289_, lean_object* v_h_1290_, lean_object* v_acc_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1283_, v_inst_1286_, v_xs_1287_, v_f_1288_, v_i_1289_, v_acc_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(lean_object* v_m_1293_, lean_object* v_00_u03b1_1294_, lean_object* v_n_1295_, lean_object* v_00_u03b2_1296_, lean_object* v_k_1297_, lean_object* v_inst_1298_, lean_object* v_xs_1299_, lean_object* v_f_1300_, lean_object* v_i_1301_, lean_object* v_h_1302_, lean_object* v_acc_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(v_m_1293_, v_00_u03b1_1294_, v_n_1295_, v_00_u03b2_1296_, v_k_1297_, v_inst_1298_, v_xs_1299_, v_f_1300_, v_i_1301_, v_h_1302_, v_acc_1303_);
lean_dec(v_k_1297_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___redArg(lean_object* v_n_1305_, lean_object* v_inst_1306_, lean_object* v_xs_1307_, lean_object* v_f_1308_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1311_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1305_, v_inst_1306_, v_xs_1307_, v_f_1308_, v___x_1309_, v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM(lean_object* v_m_1312_, lean_object* v_00_u03b1_1313_, lean_object* v_n_1314_, lean_object* v_00_u03b2_1315_, lean_object* v_k_1316_, lean_object* v_inst_1317_, lean_object* v_xs_1318_, lean_object* v_f_1319_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1322_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1314_, v_inst_1317_, v_xs_1318_, v_f_1319_, v___x_1320_, v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___boxed(lean_object* v_m_1323_, lean_object* v_00_u03b1_1324_, lean_object* v_n_1325_, lean_object* v_00_u03b2_1326_, lean_object* v_k_1327_, lean_object* v_inst_1328_, lean_object* v_xs_1329_, lean_object* v_f_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Vector_flatMapM(v_m_1323_, v_00_u03b1_1324_, v_n_1325_, v_00_u03b2_1326_, v_k_1327_, v_inst_1328_, v_xs_1329_, v_f_1330_);
lean_dec(v_k_1327_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1332_, lean_object* v_ys_1333_, lean_object* v_inst_1334_, lean_object* v_xs_1335_, lean_object* v_f_1336_, lean_object* v_n_1337_, lean_object* v_____do__lift_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Vector_mapFinIdxM_map___redArg___lam__0(v_j_1332_, v_ys_1333_, v_inst_1334_, v_xs_1335_, v_f_1336_, v_n_1337_, v_____do__lift_1338_);
lean_dec(v_n_1337_);
lean_dec(v_j_1332_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg(lean_object* v_inst_1340_, lean_object* v_xs_1341_, lean_object* v_f_1342_, lean_object* v_i_1343_, lean_object* v_j_1344_, lean_object* v_ys_1345_){
_start:
{
lean_object* v_toApplicative_1346_; lean_object* v_toBind_1347_; lean_object* v_toPure_1348_; lean_object* v_zero_1349_; uint8_t v_isZero_1350_; 
v_toApplicative_1346_ = lean_ctor_get(v_inst_1340_, 0);
v_toBind_1347_ = lean_ctor_get(v_inst_1340_, 1);
lean_inc(v_toBind_1347_);
v_toPure_1348_ = lean_ctor_get(v_toApplicative_1346_, 1);
v_zero_1349_ = lean_unsigned_to_nat(0u);
v_isZero_1350_ = lean_nat_dec_eq(v_i_1343_, v_zero_1349_);
if (v_isZero_1350_ == 1)
{
lean_object* v___x_1351_; 
lean_inc(v_toPure_1348_);
lean_dec(v_toBind_1347_);
lean_dec(v_j_1344_);
lean_dec(v_f_1342_);
lean_dec_ref(v_xs_1341_);
lean_dec_ref(v_inst_1340_);
v___x_1351_ = lean_apply_2(v_toPure_1348_, lean_box(0), v_ys_1345_);
return v___x_1351_;
}
else
{
lean_object* v_one_1352_; lean_object* v_n_1353_; lean_object* v___f_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v_one_1352_ = lean_unsigned_to_nat(1u);
v_n_1353_ = lean_nat_sub(v_i_1343_, v_one_1352_);
lean_inc(v_f_1342_);
lean_inc_ref(v_xs_1341_);
lean_inc(v_j_1344_);
v___f_1354_ = lean_alloc_closure((void*)(l_Vector_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1354_, 0, v_j_1344_);
lean_closure_set(v___f_1354_, 1, v_ys_1345_);
lean_closure_set(v___f_1354_, 2, v_inst_1340_);
lean_closure_set(v___f_1354_, 3, v_xs_1341_);
lean_closure_set(v___f_1354_, 4, v_f_1342_);
lean_closure_set(v___f_1354_, 5, v_n_1353_);
v___x_1355_ = lean_array_fget(v_xs_1341_, v_j_1344_);
lean_dec_ref(v_xs_1341_);
v___x_1356_ = lean_apply_3(v_f_1342_, v_j_1344_, v___x_1355_, lean_box(0));
v___x_1357_ = lean_apply_4(v_toBind_1347_, lean_box(0), lean_box(0), v___x_1356_, v___f_1354_);
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1358_, lean_object* v_ys_1359_, lean_object* v_inst_1360_, lean_object* v_xs_1361_, lean_object* v_f_1362_, lean_object* v_n_1363_, lean_object* v_____do__lift_1364_){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1365_ = lean_unsigned_to_nat(1u);
v___x_1366_ = lean_nat_add(v_j_1358_, v___x_1365_);
v___x_1367_ = lean_array_push(v_ys_1359_, v_____do__lift_1364_);
v___x_1368_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1360_, v_xs_1361_, v_f_1362_, v_n_1363_, v___x_1366_, v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1369_, lean_object* v_xs_1370_, lean_object* v_f_1371_, lean_object* v_i_1372_, lean_object* v_j_1373_, lean_object* v_ys_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1369_, v_xs_1370_, v_f_1371_, v_i_1372_, v_j_1373_, v_ys_1374_);
lean_dec(v_i_1372_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map(lean_object* v_n_1376_, lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_m_1379_, lean_object* v_inst_1380_, lean_object* v_xs_1381_, lean_object* v_f_1382_, lean_object* v_i_1383_, lean_object* v_j_1384_, lean_object* v_inv_1385_, lean_object* v_ys_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1380_, v_xs_1381_, v_f_1382_, v_i_1383_, v_j_1384_, v_ys_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___boxed(lean_object* v_n_1388_, lean_object* v_00_u03b1_1389_, lean_object* v_00_u03b2_1390_, lean_object* v_m_1391_, lean_object* v_inst_1392_, lean_object* v_xs_1393_, lean_object* v_f_1394_, lean_object* v_i_1395_, lean_object* v_j_1396_, lean_object* v_inv_1397_, lean_object* v_ys_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Vector_mapFinIdxM_map(v_n_1388_, v_00_u03b1_1389_, v_00_u03b2_1390_, v_m_1391_, v_inst_1392_, v_xs_1393_, v_f_1394_, v_i_1395_, v_j_1396_, v_inv_1397_, v_ys_1398_);
lean_dec(v_i_1395_);
lean_dec(v_n_1388_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg(lean_object* v_n_1400_, lean_object* v_inst_1401_, lean_object* v_xs_1402_, lean_object* v_f_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1406_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1401_, v_xs_1402_, v_f_1403_, v_n_1400_, v___x_1404_, v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg___boxed(lean_object* v_n_1407_, lean_object* v_inst_1408_, lean_object* v_xs_1409_, lean_object* v_f_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Vector_mapFinIdxM___redArg(v_n_1407_, v_inst_1408_, v_xs_1409_, v_f_1410_);
lean_dec(v_n_1407_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM(lean_object* v_n_1412_, lean_object* v_00_u03b1_1413_, lean_object* v_00_u03b2_1414_, lean_object* v_m_1415_, lean_object* v_inst_1416_, lean_object* v_xs_1417_, lean_object* v_f_1418_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1421_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1416_, v_xs_1417_, v_f_1418_, v_n_1412_, v___x_1419_, v___x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___boxed(lean_object* v_n_1422_, lean_object* v_00_u03b1_1423_, lean_object* v_00_u03b2_1424_, lean_object* v_m_1425_, lean_object* v_inst_1426_, lean_object* v_xs_1427_, lean_object* v_f_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Vector_mapFinIdxM(v_n_1422_, v_00_u03b1_1423_, v_00_u03b2_1424_, v_m_1425_, v_inst_1426_, v_xs_1427_, v_f_1428_);
lean_dec(v_n_1422_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg(lean_object* v_n_1430_, lean_object* v_inst_1431_, lean_object* v_f_1432_, lean_object* v_xs_1433_){
_start:
{
lean_object* v___f_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___f_1434_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1434_, 0, v_f_1432_);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1437_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1431_, v_xs_1433_, v___f_1434_, v_n_1430_, v___x_1435_, v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg___boxed(lean_object* v_n_1438_, lean_object* v_inst_1439_, lean_object* v_f_1440_, lean_object* v_xs_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Vector_mapIdxM___redArg(v_n_1438_, v_inst_1439_, v_f_1440_, v_xs_1441_);
lean_dec(v_n_1438_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM(lean_object* v_n_1443_, lean_object* v_00_u03b1_1444_, lean_object* v_00_u03b2_1445_, lean_object* v_m_1446_, lean_object* v_inst_1447_, lean_object* v_f_1448_, lean_object* v_xs_1449_){
_start:
{
lean_object* v___f_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___f_1450_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1450_, 0, v_f_1448_);
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1453_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1447_, v_xs_1449_, v___f_1450_, v_n_1443_, v___x_1451_, v___x_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___boxed(lean_object* v_n_1454_, lean_object* v_00_u03b1_1455_, lean_object* v_00_u03b2_1456_, lean_object* v_m_1457_, lean_object* v_inst_1458_, lean_object* v_f_1459_, lean_object* v_xs_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Vector_mapIdxM(v_n_1454_, v_00_u03b1_1455_, v_00_u03b2_1456_, v_m_1457_, v_inst_1458_, v_f_1459_, v_xs_1460_);
lean_dec(v_n_1454_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___redArg(lean_object* v_inst_1462_, lean_object* v_f_1463_, lean_object* v_xs_1464_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1462_, v_f_1463_, v_xs_1464_, v___x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM(lean_object* v_00_u03b2_1467_, lean_object* v_n_1468_, lean_object* v_00_u03b1_1469_, lean_object* v_m_1470_, lean_object* v_inst_1471_, lean_object* v_f_1472_, lean_object* v_xs_1473_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1471_, v_f_1472_, v_xs_1473_, v___x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___boxed(lean_object* v_00_u03b2_1476_, lean_object* v_n_1477_, lean_object* v_00_u03b1_1478_, lean_object* v_m_1479_, lean_object* v_inst_1480_, lean_object* v_f_1481_, lean_object* v_xs_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Vector_firstM(v_00_u03b2_1476_, v_n_1477_, v_00_u03b1_1478_, v_m_1479_, v_inst_1480_, v_f_1481_, v_xs_1482_);
lean_dec(v_n_1477_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0(lean_object* v_x_1484_){
_start:
{
lean_inc_ref(v_x_1484_);
return v_x_1484_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0___boxed(lean_object* v_x_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Vector_flatten___redArg___lam__0(v_x_1485_);
lean_dec_ref(v_x_1485_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg(lean_object* v_xs_1491_){
_start:
{
lean_object* v___f_1492_; lean_object* v___x_1493_; size_t v_sz_1494_; size_t v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___f_1492_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1493_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1494_ = lean_array_size(v_xs_1491_);
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1493_, v___f_1492_, v_sz_1494_, v___x_1495_, v_xs_1491_);
v___x_1497_ = lean_unsigned_to_nat(0u);
v___x_1498_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1499_ = lean_array_get_size(v___x_1496_);
v___x_1500_ = lean_nat_dec_lt(v___x_1497_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_dec(v___x_1496_);
return v___x_1498_;
}
else
{
lean_object* v___f_1501_; uint8_t v___x_1502_; 
v___f_1501_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1502_ = lean_nat_dec_le(v___x_1499_, v___x_1499_);
if (v___x_1502_ == 0)
{
if (v___x_1500_ == 0)
{
lean_dec(v___x_1496_);
return v___x_1498_;
}
else
{
size_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_usize_of_nat(v___x_1499_);
v___x_1504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1493_, v___f_1501_, v___x_1496_, v___x_1495_, v___x_1503_, v___x_1498_);
return v___x_1504_;
}
}
else
{
size_t v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_usize_of_nat(v___x_1499_);
v___x_1506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1493_, v___f_1501_, v___x_1496_, v___x_1495_, v___x_1505_, v___x_1498_);
return v___x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten(lean_object* v_00_u03b1_1507_, lean_object* v_n_1508_, lean_object* v_m_1509_, lean_object* v_xs_1510_){
_start:
{
lean_object* v___f_1511_; lean_object* v___x_1512_; size_t v_sz_1513_; size_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___f_1511_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1512_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1513_ = lean_array_size(v_xs_1510_);
v___x_1514_ = ((size_t)0ULL);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1512_, v___f_1511_, v_sz_1513_, v___x_1514_, v_xs_1510_);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1518_ = lean_array_get_size(v___x_1515_);
v___x_1519_ = lean_nat_dec_lt(v___x_1516_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_dec(v___x_1515_);
return v___x_1517_;
}
else
{
lean_object* v___f_1520_; uint8_t v___x_1521_; 
v___f_1520_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1521_ = lean_nat_dec_le(v___x_1518_, v___x_1518_);
if (v___x_1521_ == 0)
{
if (v___x_1519_ == 0)
{
lean_dec(v___x_1515_);
return v___x_1517_;
}
else
{
size_t v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_usize_of_nat(v___x_1518_);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1512_, v___f_1520_, v___x_1515_, v___x_1514_, v___x_1522_, v___x_1517_);
return v___x_1523_;
}
}
else
{
size_t v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_usize_of_nat(v___x_1518_);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1512_, v___f_1520_, v___x_1515_, v___x_1514_, v___x_1524_, v___x_1517_);
return v___x_1525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___boxed(lean_object* v_00_u03b1_1526_, lean_object* v_n_1527_, lean_object* v_m_1528_, lean_object* v_xs_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Vector_flatten(v_00_u03b1_1526_, v_n_1527_, v_m_1528_, v_xs_1529_);
lean_dec(v_m_1528_);
lean_dec(v_n_1527_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg___lam__0(lean_object* v_f_1531_, lean_object* v_x1_1532_, lean_object* v_x2_1533_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_apply_1(v_f_1531_, v_x2_1533_);
v___x_1535_ = l_Array_append___redArg(v_x1_1532_, v___x_1534_);
lean_dec_ref(v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg(lean_object* v_xs_1536_, lean_object* v_f_1537_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1538_ = lean_unsigned_to_nat(0u);
v___x_1539_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1540_ = lean_array_get_size(v_xs_1536_);
v___x_1541_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1542_ = lean_nat_dec_lt(v___x_1538_, v___x_1540_);
if (v___x_1542_ == 0)
{
lean_dec_ref(v_f_1537_);
lean_dec_ref(v_xs_1536_);
return v___x_1539_;
}
else
{
lean_object* v___f_1543_; uint8_t v___x_1544_; 
v___f_1543_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1543_, 0, v_f_1537_);
v___x_1544_ = lean_nat_dec_le(v___x_1540_, v___x_1540_);
if (v___x_1544_ == 0)
{
if (v___x_1542_ == 0)
{
lean_dec_ref(v___f_1543_);
lean_dec_ref(v_xs_1536_);
return v___x_1539_;
}
else
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = ((size_t)0ULL);
v___x_1546_ = lean_usize_of_nat(v___x_1540_);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1541_, v___f_1543_, v_xs_1536_, v___x_1545_, v___x_1546_, v___x_1539_);
return v___x_1547_;
}
}
else
{
size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = lean_usize_of_nat(v___x_1540_);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1541_, v___f_1543_, v_xs_1536_, v___x_1548_, v___x_1549_, v___x_1539_);
return v___x_1550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap(lean_object* v_00_u03b1_1551_, lean_object* v_n_1552_, lean_object* v_00_u03b2_1553_, lean_object* v_m_1554_, lean_object* v_xs_1555_, lean_object* v_f_1556_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1557_ = lean_unsigned_to_nat(0u);
v___x_1558_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1559_ = lean_array_get_size(v_xs_1555_);
v___x_1560_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1561_ = lean_nat_dec_lt(v___x_1557_, v___x_1559_);
if (v___x_1561_ == 0)
{
lean_dec_ref(v_f_1556_);
lean_dec_ref(v_xs_1555_);
return v___x_1558_;
}
else
{
lean_object* v___f_1562_; uint8_t v___x_1563_; 
v___f_1562_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1562_, 0, v_f_1556_);
v___x_1563_ = lean_nat_dec_le(v___x_1559_, v___x_1559_);
if (v___x_1563_ == 0)
{
if (v___x_1561_ == 0)
{
lean_dec_ref(v___f_1562_);
lean_dec_ref(v_xs_1555_);
return v___x_1558_;
}
else
{
size_t v___x_1564_; size_t v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = ((size_t)0ULL);
v___x_1565_ = lean_usize_of_nat(v___x_1559_);
v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1560_, v___f_1562_, v_xs_1555_, v___x_1564_, v___x_1565_, v___x_1558_);
return v___x_1566_;
}
}
else
{
size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = ((size_t)0ULL);
v___x_1568_ = lean_usize_of_nat(v___x_1559_);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1560_, v___f_1562_, v_xs_1555_, v___x_1567_, v___x_1568_, v___x_1558_);
return v___x_1569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___boxed(lean_object* v_00_u03b1_1570_, lean_object* v_n_1571_, lean_object* v_00_u03b2_1572_, lean_object* v_m_1573_, lean_object* v_xs_1574_, lean_object* v_f_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Vector_flatMap(v_00_u03b1_1570_, v_n_1571_, v_00_u03b2_1572_, v_m_1573_, v_xs_1574_, v_f_1575_);
lean_dec(v_m_1573_);
lean_dec(v_n_1571_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg(lean_object* v_xs_1577_, lean_object* v_k_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Array_zipIdx___redArg(v_xs_1577_, v_k_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg___boxed(lean_object* v_xs_1580_, lean_object* v_k_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Vector_zipIdx___redArg(v_xs_1580_, v_k_1581_);
lean_dec(v_k_1581_);
lean_dec_ref(v_xs_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx(lean_object* v_00_u03b1_1583_, lean_object* v_n_1584_, lean_object* v_xs_1585_, lean_object* v_k_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Array_zipIdx___redArg(v_xs_1585_, v_k_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___boxed(lean_object* v_00_u03b1_1588_, lean_object* v_n_1589_, lean_object* v_xs_1590_, lean_object* v_k_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Vector_zipIdx(v_00_u03b1_1588_, v_n_1589_, v_xs_1590_, v_k_1591_);
lean_dec(v_k_1591_);
lean_dec_ref(v_xs_1590_);
lean_dec(v_n_1589_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg(lean_object* v_as_1593_, lean_object* v_bs_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Array_zip___redArg(v_as_1593_, v_bs_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg___boxed(lean_object* v_as_1596_, lean_object* v_bs_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Vector_zip___redArg(v_as_1596_, v_bs_1597_);
lean_dec_ref(v_bs_1597_);
lean_dec_ref(v_as_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip(lean_object* v_00_u03b1_1599_, lean_object* v_n_1600_, lean_object* v_00_u03b2_1601_, lean_object* v_as_1602_, lean_object* v_bs_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Array_zip___redArg(v_as_1602_, v_bs_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___boxed(lean_object* v_00_u03b1_1605_, lean_object* v_n_1606_, lean_object* v_00_u03b2_1607_, lean_object* v_as_1608_, lean_object* v_bs_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Vector_zip(v_00_u03b1_1605_, v_n_1606_, v_00_u03b2_1607_, v_as_1608_, v_bs_1609_);
lean_dec_ref(v_bs_1609_);
lean_dec_ref(v_as_1608_);
lean_dec(v_n_1606_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___redArg(lean_object* v_f_1611_, lean_object* v_as_1612_, lean_object* v_bs_1613_){
_start:
{
lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___f_1614_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1614_, 0, v_f_1611_);
v___x_1615_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1618_ = l_Array_zipWithMAux___redArg(v___x_1615_, v_as_1612_, v_bs_1613_, v___f_1614_, v___x_1616_, v___x_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith(lean_object* v_00_u03b1_1619_, lean_object* v_00_u03b2_1620_, lean_object* v_00_u03c6_1621_, lean_object* v_n_1622_, lean_object* v_f_1623_, lean_object* v_as_1624_, lean_object* v_bs_1625_){
_start:
{
lean_object* v___f_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___f_1626_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1626_, 0, v_f_1623_);
v___x_1627_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1630_ = l_Array_zipWithMAux___redArg(v___x_1627_, v_as_1624_, v_bs_1625_, v___f_1626_, v___x_1628_, v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___boxed(lean_object* v_00_u03b1_1631_, lean_object* v_00_u03b2_1632_, lean_object* v_00_u03c6_1633_, lean_object* v_n_1634_, lean_object* v_f_1635_, lean_object* v_as_1636_, lean_object* v_bs_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Vector_zipWith(v_00_u03b1_1631_, v_00_u03b2_1632_, v_00_u03c6_1633_, v_n_1634_, v_f_1635_, v_as_1636_, v_bs_1637_);
lean_dec(v_n_1634_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg(lean_object* v_xs_1639_){
_start:
{
lean_object* v___x_1640_; lean_object* v_fst_1641_; lean_object* v_snd_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v___x_1640_ = l_Array_unzip___redArg(v_xs_1639_);
v_fst_1641_ = lean_ctor_get(v___x_1640_, 0);
v_snd_1642_ = lean_ctor_get(v___x_1640_, 1);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1640_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_snd_1642_);
lean_inc(v_fst_1641_);
lean_dec(v___x_1640_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_fst_1641_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_snd_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg___boxed(lean_object* v_xs_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Vector_unzip___redArg(v_xs_1650_);
lean_dec_ref(v_xs_1650_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip(lean_object* v_00_u03b1_1652_, lean_object* v_00_u03b2_1653_, lean_object* v_n_1654_, lean_object* v_xs_1655_){
_start:
{
lean_object* v___x_1656_; lean_object* v_fst_1657_; lean_object* v_snd_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
v___x_1656_ = l_Array_unzip___redArg(v_xs_1655_);
v_fst_1657_ = lean_ctor_get(v___x_1656_, 0);
v_snd_1658_ = lean_ctor_get(v___x_1656_, 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1656_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_snd_1658_);
lean_inc(v_fst_1657_);
lean_dec(v___x_1656_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_fst_1657_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_snd_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___boxed(lean_object* v_00_u03b1_1666_, lean_object* v_00_u03b2_1667_, lean_object* v_n_1668_, lean_object* v_xs_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Vector_unzip(v_00_u03b1_1666_, v_00_u03b2_1667_, v_n_1668_, v_xs_1669_);
lean_dec_ref(v_xs_1669_);
lean_dec(v_n_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn___redArg(lean_object* v_n_1671_, lean_object* v_f_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Array_ofFn___redArg(v_n_1671_, v_f_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn(lean_object* v_n_1674_, lean_object* v_00_u03b1_1675_, lean_object* v_f_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Array_ofFn___redArg(v_n_1674_, v_f_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l_Vector_swap___auto__1(void){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1678_;
}
}
static lean_object* _init_l_Vector_swap___auto__3(void){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg(lean_object* v_xs_1680_, lean_object* v_i_1681_, lean_object* v_j_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_array_fswap(v_xs_1680_, v_i_1681_, v_j_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg___boxed(lean_object* v_xs_1684_, lean_object* v_i_1685_, lean_object* v_j_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Vector_swap___redArg(v_xs_1684_, v_i_1685_, v_j_1686_);
lean_dec(v_j_1686_);
lean_dec(v_i_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap(lean_object* v_00_u03b1_1688_, lean_object* v_n_1689_, lean_object* v_xs_1690_, lean_object* v_i_1691_, lean_object* v_j_1692_, lean_object* v_hi_1693_, lean_object* v_hj_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_array_fswap(v_xs_1690_, v_i_1691_, v_j_1692_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___boxed(lean_object* v_00_u03b1_1696_, lean_object* v_n_1697_, lean_object* v_xs_1698_, lean_object* v_i_1699_, lean_object* v_j_1700_, lean_object* v_hi_1701_, lean_object* v_hj_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Vector_swap(v_00_u03b1_1696_, v_n_1697_, v_xs_1698_, v_i_1699_, v_j_1700_, v_hi_1701_, v_hj_1702_);
lean_dec(v_j_1700_);
lean_dec(v_i_1699_);
lean_dec(v_n_1697_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg(lean_object* v_xs_1704_, lean_object* v_i_1705_, lean_object* v_j_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_array_swap(v_xs_1704_, v_i_1705_, v_j_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg___boxed(lean_object* v_xs_1708_, lean_object* v_i_1709_, lean_object* v_j_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Vector_swapIfInBounds___redArg(v_xs_1708_, v_i_1709_, v_j_1710_);
lean_dec(v_j_1710_);
lean_dec(v_i_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds(lean_object* v_00_u03b1_1712_, lean_object* v_n_1713_, lean_object* v_xs_1714_, lean_object* v_i_1715_, lean_object* v_j_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_array_swap(v_xs_1714_, v_i_1715_, v_j_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___boxed(lean_object* v_00_u03b1_1718_, lean_object* v_n_1719_, lean_object* v_xs_1720_, lean_object* v_i_1721_, lean_object* v_j_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Vector_swapIfInBounds(v_00_u03b1_1718_, v_n_1719_, v_xs_1720_, v_i_1721_, v_j_1722_);
lean_dec(v_j_1722_);
lean_dec(v_i_1721_);
lean_dec(v_n_1719_);
return v_res_1723_;
}
}
static lean_object* _init_l_Vector_swapAt___auto__1(void){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg(lean_object* v_xs_1725_, lean_object* v_i_1726_, lean_object* v_x_1727_){
_start:
{
lean_object* v_e_1728_; lean_object* v_xs_x27_1729_; lean_object* v___x_1730_; 
v_e_1728_ = lean_array_fget(v_xs_1725_, v_i_1726_);
v_xs_x27_1729_ = lean_array_fset(v_xs_1725_, v_i_1726_, v_x_1727_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_e_1728_);
lean_ctor_set(v___x_1730_, 1, v_xs_x27_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg___boxed(lean_object* v_xs_1731_, lean_object* v_i_1732_, lean_object* v_x_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Vector_swapAt___redArg(v_xs_1731_, v_i_1732_, v_x_1733_);
lean_dec(v_i_1732_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt(lean_object* v_00_u03b1_1735_, lean_object* v_n_1736_, lean_object* v_xs_1737_, lean_object* v_i_1738_, lean_object* v_x_1739_, lean_object* v_hi_1740_){
_start:
{
lean_object* v_e_1741_; lean_object* v_xs_x27_1742_; lean_object* v___x_1743_; 
v_e_1741_ = lean_array_fget(v_xs_1737_, v_i_1738_);
v_xs_x27_1742_ = lean_array_fset(v_xs_1737_, v_i_1738_, v_x_1739_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_e_1741_);
lean_ctor_set(v___x_1743_, 1, v_xs_x27_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___boxed(lean_object* v_00_u03b1_1744_, lean_object* v_n_1745_, lean_object* v_xs_1746_, lean_object* v_i_1747_, lean_object* v_x_1748_, lean_object* v_hi_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Vector_swapAt(v_00_u03b1_1744_, v_n_1745_, v_xs_1746_, v_i_1747_, v_x_1748_, v_hi_1749_);
lean_dec(v_i_1747_);
lean_dec(v_n_1745_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___redArg(lean_object* v_xs_1755_, lean_object* v_i_1756_, lean_object* v_x_1757_){
_start:
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = lean_array_get_size(v_xs_1755_);
v___x_1759_ = lean_nat_dec_lt(v_i_1756_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v_this_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v_fst_1772_; lean_object* v_snd_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_this_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1760_, 0, v_x_1757_);
lean_ctor_set(v_this_1760_, 1, v_xs_1755_);
v___x_1761_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1762_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1763_ = lean_unsigned_to_nat(438u);
v___x_1764_ = lean_unsigned_to_nat(4u);
v___x_1765_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1766_ = l_Nat_reprFast(v_i_1756_);
v___x_1767_ = lean_string_append(v___x_1765_, v___x_1766_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1769_ = lean_string_append(v___x_1767_, v___x_1768_);
v___x_1770_ = l_mkPanicMessageWithDecl(v___x_1761_, v___x_1762_, v___x_1763_, v___x_1764_, v___x_1769_);
lean_dec_ref(v___x_1769_);
v___x_1771_ = l_panic___redArg(v_this_1760_, v___x_1770_);
v_fst_1772_ = lean_ctor_get(v___x_1771_, 0);
v_snd_1773_ = lean_ctor_get(v___x_1771_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1771_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_snd_1773_);
lean_inc(v_fst_1772_);
lean_dec(v___x_1771_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_fst_1772_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_snd_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
else
{
lean_object* v_e_1781_; lean_object* v_xs_x27_1782_; lean_object* v___x_1783_; 
v_e_1781_ = lean_array_fget(v_xs_1755_, v_i_1756_);
v_xs_x27_1782_ = lean_array_fset(v_xs_1755_, v_i_1756_, v_x_1757_);
lean_dec(v_i_1756_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v_e_1781_);
lean_ctor_set(v___x_1783_, 1, v_xs_x27_1782_);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21(lean_object* v_00_u03b1_1784_, lean_object* v_n_1785_, lean_object* v_xs_1786_, lean_object* v_i_1787_, lean_object* v_x_1788_){
_start:
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = lean_array_get_size(v_xs_1786_);
v___x_1790_ = lean_nat_dec_lt(v_i_1787_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v_this_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v_fst_1803_; lean_object* v_snd_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
v_this_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1791_, 0, v_x_1788_);
lean_ctor_set(v_this_1791_, 1, v_xs_1786_);
v___x_1792_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1793_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1794_ = lean_unsigned_to_nat(438u);
v___x_1795_ = lean_unsigned_to_nat(4u);
v___x_1796_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1797_ = l_Nat_reprFast(v_i_1787_);
v___x_1798_ = lean_string_append(v___x_1796_, v___x_1797_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1800_ = lean_string_append(v___x_1798_, v___x_1799_);
v___x_1801_ = l_mkPanicMessageWithDecl(v___x_1792_, v___x_1793_, v___x_1794_, v___x_1795_, v___x_1800_);
lean_dec_ref(v___x_1800_);
v___x_1802_ = l_panic___redArg(v_this_1791_, v___x_1801_);
v_fst_1803_ = lean_ctor_get(v___x_1802_, 0);
v_snd_1804_ = lean_ctor_get(v___x_1802_, 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1802_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snd_1804_);
lean_inc(v_fst_1803_);
lean_dec(v___x_1802_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_fst_1803_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_snd_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
else
{
lean_object* v_e_1812_; lean_object* v_xs_x27_1813_; lean_object* v___x_1814_; 
v_e_1812_ = lean_array_fget(v_xs_1786_, v_i_1787_);
v_xs_x27_1813_ = lean_array_fset(v_xs_1786_, v_i_1787_, v_x_1788_);
lean_dec(v_i_1787_);
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_e_1812_);
lean_ctor_set(v___x_1814_, 1, v_xs_x27_1813_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___boxed(lean_object* v_00_u03b1_1815_, lean_object* v_n_1816_, lean_object* v_xs_1817_, lean_object* v_i_1818_, lean_object* v_x_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Vector_swapAt_x21(v_00_u03b1_1815_, v_n_1816_, v_xs_1817_, v_i_1818_, v_x_1819_);
lean_dec(v_n_1816_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Vector_range(lean_object* v_n_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Array_range(v_n_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Vector_range_x27(lean_object* v_start_1823_, lean_object* v_size_1824_, lean_object* v_step_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Array_range_x27(v_start_1823_, v_size_1824_, v_step_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv___redArg(lean_object* v_n_1827_, lean_object* v_xs_1828_, lean_object* v_ys_1829_, lean_object* v_r_1830_){
_start:
{
uint8_t v___x_1831_; 
v___x_1831_ = l_Array_isEqvAux___redArg(v_xs_1828_, v_ys_1829_, v_r_1830_, v_n_1827_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___redArg___boxed(lean_object* v_n_1832_, lean_object* v_xs_1833_, lean_object* v_ys_1834_, lean_object* v_r_1835_){
_start:
{
uint8_t v_res_1836_; lean_object* v_r_1837_; 
v_res_1836_ = l_Vector_isEqv___redArg(v_n_1832_, v_xs_1833_, v_ys_1834_, v_r_1835_);
lean_dec_ref(v_ys_1834_);
lean_dec_ref(v_xs_1833_);
v_r_1837_ = lean_box(v_res_1836_);
return v_r_1837_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv(lean_object* v_00_u03b1_1838_, lean_object* v_n_1839_, lean_object* v_xs_1840_, lean_object* v_ys_1841_, lean_object* v_r_1842_){
_start:
{
uint8_t v___x_1843_; 
v___x_1843_ = l_Array_isEqvAux___redArg(v_xs_1840_, v_ys_1841_, v_r_1842_, v_n_1839_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___boxed(lean_object* v_00_u03b1_1844_, lean_object* v_n_1845_, lean_object* v_xs_1846_, lean_object* v_ys_1847_, lean_object* v_r_1848_){
_start:
{
uint8_t v_res_1849_; lean_object* v_r_1850_; 
v_res_1849_ = l_Vector_isEqv(v_00_u03b1_1844_, v_n_1845_, v_xs_1846_, v_ys_1847_, v_r_1848_);
lean_dec_ref(v_ys_1847_);
lean_dec_ref(v_xs_1846_);
v_r_1850_ = lean_box(v_res_1849_);
return v_r_1850_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__0(lean_object* v_inst_1851_, lean_object* v_x1_1852_, lean_object* v_x2_1853_){
_start:
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = lean_apply_2(v_inst_1851_, v_x1_1852_, v_x2_1853_);
v___x_1855_ = lean_unbox(v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__0___boxed(lean_object* v_inst_1856_, lean_object* v_x1_1857_, lean_object* v_x2_1858_){
_start:
{
uint8_t v_res_1859_; lean_object* v_r_1860_; 
v_res_1859_ = l_Vector_instBEq___redArg___lam__0(v_inst_1856_, v_x1_1857_, v_x2_1858_);
v_r_1860_ = lean_box(v_res_1859_);
return v_r_1860_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__1(lean_object* v___f_1861_, lean_object* v_n_1862_, lean_object* v_xs_1863_, lean_object* v_ys_1864_){
_start:
{
uint8_t v___x_1865_; 
v___x_1865_ = l_Array_isEqvAux___redArg(v_xs_1863_, v_ys_1864_, v___f_1861_, v_n_1862_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__1___boxed(lean_object* v___f_1866_, lean_object* v_n_1867_, lean_object* v_xs_1868_, lean_object* v_ys_1869_){
_start:
{
uint8_t v_res_1870_; lean_object* v_r_1871_; 
v_res_1870_ = l_Vector_instBEq___redArg___lam__1(v___f_1866_, v_n_1867_, v_xs_1868_, v_ys_1869_);
lean_dec_ref(v_ys_1869_);
lean_dec_ref(v_xs_1868_);
v_r_1871_ = lean_box(v_res_1870_);
return v_r_1871_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg(lean_object* v_n_1872_, lean_object* v_inst_1873_){
_start:
{
lean_object* v___f_1874_; lean_object* v___f_1875_; 
v___f_1874_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1874_, 0, v_inst_1873_);
v___f_1875_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1875_, 0, v___f_1874_);
lean_closure_set(v___f_1875_, 1, v_n_1872_);
return v___f_1875_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq(lean_object* v_00_u03b1_1876_, lean_object* v_n_1877_, lean_object* v_inst_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Vector_instBEq___redArg(v_n_1877_, v_inst_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___redArg(lean_object* v_xs_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Array_reverse___redArg(v_xs_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse(lean_object* v_00_u03b1_1882_, lean_object* v_n_1883_, lean_object* v_xs_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Array_reverse___redArg(v_xs_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___boxed(lean_object* v_00_u03b1_1886_, lean_object* v_n_1887_, lean_object* v_xs_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Vector_reverse(v_00_u03b1_1886_, v_n_1887_, v_xs_1888_);
lean_dec(v_n_1887_);
return v_res_1889_;
}
}
static lean_object* _init_l_Vector_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___redArg(lean_object* v_xs_1891_, lean_object* v_i_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Array_eraseIdx___redArg(v_xs_1891_, v_i_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx(lean_object* v_00_u03b1_1894_, lean_object* v_n_1895_, lean_object* v_xs_1896_, lean_object* v_i_1897_, lean_object* v_h_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Array_eraseIdx___redArg(v_xs_1896_, v_i_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___boxed(lean_object* v_00_u03b1_1900_, lean_object* v_n_1901_, lean_object* v_xs_1902_, lean_object* v_i_1903_, lean_object* v_h_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Vector_eraseIdx(v_00_u03b1_1900_, v_n_1901_, v_xs_1902_, v_i_1903_, v_h_1904_);
lean_dec(v_n_1901_);
return v_res_1905_;
}
}
static lean_object* _init_l_Vector_eraseIdx_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1909_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1910_ = lean_unsigned_to_nat(4u);
v___x_1911_ = lean_unsigned_to_nat(395u);
v___x_1912_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__1));
v___x_1913_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1914_ = l_mkPanicMessageWithDecl(v___x_1913_, v___x_1912_, v___x_1911_, v___x_1910_, v___x_1909_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg(lean_object* v_n_1915_, lean_object* v_xs_1916_, lean_object* v_i_1917_){
_start:
{
uint8_t v___x_1918_; 
v___x_1918_ = lean_nat_dec_lt(v_i_1917_, v_n_1915_);
if (v___x_1918_ == 0)
{
lean_object* v_this_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v_i_1917_);
v_this_1919_ = lean_array_pop(v_xs_1916_);
v___x_1920_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1921_ = l_panic___redArg(v_this_1919_, v___x_1920_);
return v___x_1921_;
}
else
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Array_eraseIdx___redArg(v_xs_1916_, v_i_1917_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg___boxed(lean_object* v_n_1923_, lean_object* v_xs_1924_, lean_object* v_i_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Vector_eraseIdx_x21___redArg(v_n_1923_, v_xs_1924_, v_i_1925_);
lean_dec(v_n_1923_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21(lean_object* v_00_u03b1_1927_, lean_object* v_n_1928_, lean_object* v_xs_1929_, lean_object* v_i_1930_){
_start:
{
uint8_t v___x_1931_; 
v___x_1931_ = lean_nat_dec_lt(v_i_1930_, v_n_1928_);
if (v___x_1931_ == 0)
{
lean_object* v_this_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_dec(v_i_1930_);
v_this_1932_ = lean_array_pop(v_xs_1929_);
v___x_1933_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1934_ = l_panic___redArg(v_this_1932_, v___x_1933_);
return v___x_1934_;
}
else
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Array_eraseIdx___redArg(v_xs_1929_, v_i_1930_);
return v___x_1935_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___boxed(lean_object* v_00_u03b1_1936_, lean_object* v_n_1937_, lean_object* v_xs_1938_, lean_object* v_i_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Vector_eraseIdx_x21(v_00_u03b1_1936_, v_n_1937_, v_xs_1938_, v_i_1939_);
lean_dec(v_n_1937_);
return v_res_1940_;
}
}
static lean_object* _init_l_Vector_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg(lean_object* v_xs_1942_, lean_object* v_i_1943_, lean_object* v_x_1944_){
_start:
{
lean_object* v_j_1945_; lean_object* v_as_1946_; lean_object* v___x_1947_; 
v_j_1945_ = lean_array_get_size(v_xs_1942_);
v_as_1946_ = lean_array_push(v_xs_1942_, v_x_1944_);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1943_, v_as_1946_, v_j_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg___boxed(lean_object* v_xs_1948_, lean_object* v_i_1949_, lean_object* v_x_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Vector_insertIdx___redArg(v_xs_1948_, v_i_1949_, v_x_1950_);
lean_dec(v_i_1949_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx(lean_object* v_00_u03b1_1952_, lean_object* v_n_1953_, lean_object* v_xs_1954_, lean_object* v_i_1955_, lean_object* v_x_1956_, lean_object* v_h_1957_){
_start:
{
lean_object* v_j_1958_; lean_object* v_as_1959_; lean_object* v___x_1960_; 
v_j_1958_ = lean_array_get_size(v_xs_1954_);
v_as_1959_ = lean_array_push(v_xs_1954_, v_x_1956_);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1955_, v_as_1959_, v_j_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___boxed(lean_object* v_00_u03b1_1961_, lean_object* v_n_1962_, lean_object* v_xs_1963_, lean_object* v_i_1964_, lean_object* v_x_1965_, lean_object* v_h_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Vector_insertIdx(v_00_u03b1_1961_, v_n_1962_, v_xs_1963_, v_i_1964_, v_x_1965_, v_h_1966_);
lean_dec(v_i_1964_);
lean_dec(v_n_1962_);
return v_res_1967_;
}
}
static lean_object* _init_l_Vector_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1969_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1970_ = lean_unsigned_to_nat(4u);
v___x_1971_ = lean_unsigned_to_nat(408u);
v___x_1972_ = ((lean_object*)(l_Vector_insertIdx_x21___redArg___closed__0));
v___x_1973_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1974_ = l_mkPanicMessageWithDecl(v___x_1973_, v___x_1972_, v___x_1971_, v___x_1970_, v___x_1969_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg(lean_object* v_n_1975_, lean_object* v_xs_1976_, lean_object* v_i_1977_, lean_object* v_x_1978_){
_start:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_nat_dec_le(v_i_1977_, v_n_1975_);
if (v___x_1979_ == 0)
{
lean_object* v_this_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_this_1980_ = lean_array_push(v_xs_1976_, v_x_1978_);
v___x_1981_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1982_ = l_panic___redArg(v_this_1980_, v___x_1981_);
return v___x_1982_;
}
else
{
lean_object* v_j_1983_; lean_object* v_as_1984_; lean_object* v___x_1985_; 
v_j_1983_ = lean_array_get_size(v_xs_1976_);
v_as_1984_ = lean_array_push(v_xs_1976_, v_x_1978_);
v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1977_, v_as_1984_, v_j_1983_);
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg___boxed(lean_object* v_n_1986_, lean_object* v_xs_1987_, lean_object* v_i_1988_, lean_object* v_x_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Vector_insertIdx_x21___redArg(v_n_1986_, v_xs_1987_, v_i_1988_, v_x_1989_);
lean_dec(v_i_1988_);
lean_dec(v_n_1986_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21(lean_object* v_00_u03b1_1991_, lean_object* v_n_1992_, lean_object* v_xs_1993_, lean_object* v_i_1994_, lean_object* v_x_1995_){
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
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___boxed(lean_object* v_00_u03b1_2003_, lean_object* v_n_2004_, lean_object* v_xs_2005_, lean_object* v_i_2006_, lean_object* v_x_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Vector_insertIdx_x21(v_00_u03b1_2003_, v_n_2004_, v_xs_2005_, v_i_2006_, v_x_2007_);
lean_dec(v_i_2006_);
lean_dec(v_n_2004_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg(lean_object* v_n_2009_, lean_object* v_xs_2010_){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_unsigned_to_nat(1u);
v___x_2012_ = l_Array_extract___redArg(v_xs_2010_, v___x_2011_, v_n_2009_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg___boxed(lean_object* v_n_2013_, lean_object* v_xs_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Vector_tail___redArg(v_n_2013_, v_xs_2014_);
lean_dec_ref(v_xs_2014_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail(lean_object* v_00_u03b1_2016_, lean_object* v_n_2017_, lean_object* v_xs_2018_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2020_ = l_Array_extract___redArg(v_xs_2018_, v___x_2019_, v_n_2017_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___boxed(lean_object* v_00_u03b1_2021_, lean_object* v_n_2022_, lean_object* v_xs_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Vector_tail(v_00_u03b1_2021_, v_n_2022_, v_xs_2023_);
lean_dec_ref(v_xs_2023_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg(lean_object* v_inst_2025_, lean_object* v_xs_2026_, lean_object* v_x_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Array_finIdxOf_x3f___redArg(v_inst_2025_, v_xs_2026_, v_x_2027_);
if (lean_obj_tag(v___x_2028_) == 0)
{
return v___x_2028_;
}
else
{
lean_object* v_val_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_val_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_val_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_val_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_2037_, lean_object* v_xs_2038_, lean_object* v_x_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Vector_finIdxOf_x3f___redArg(v_inst_2037_, v_xs_2038_, v_x_2039_);
lean_dec_ref(v_xs_2038_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f(lean_object* v_00_u03b1_2041_, lean_object* v_n_2042_, lean_object* v_inst_2043_, lean_object* v_xs_2044_, lean_object* v_x_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Array_finIdxOf_x3f___redArg(v_inst_2043_, v_xs_2044_, v_x_2045_);
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
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_2055_, lean_object* v_n_2056_, lean_object* v_inst_2057_, lean_object* v_xs_2058_, lean_object* v_x_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Vector_finIdxOf_x3f(v_00_u03b1_2055_, v_n_2056_, v_inst_2057_, v_xs_2058_, v_x_2059_);
lean_dec_ref(v_xs_2058_);
lean_dec(v_n_2056_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg(lean_object* v_p_2061_, lean_object* v_xs_2062_){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2061_, v_xs_2062_, v___x_2063_);
if (lean_obj_tag(v___x_2064_) == 0)
{
return v___x_2064_;
}
else
{
lean_object* v_val_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
v_val_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_val_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_val_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2073_, lean_object* v_xs_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Vector_findFinIdx_x3f___redArg(v_p_2073_, v_xs_2074_);
lean_dec_ref(v_xs_2074_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f(lean_object* v_00_u03b1_2076_, lean_object* v_n_2077_, lean_object* v_p_2078_, lean_object* v_xs_2079_){
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
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2090_, lean_object* v_n_2091_, lean_object* v_p_2092_, lean_object* v_xs_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Vector_findFinIdx_x3f(v_00_u03b1_2090_, v_n_2091_, v_p_2092_, v_xs_2093_);
lean_dec_ref(v_xs_2093_);
lean_dec(v_n_2091_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__0(lean_object* v_toPure_2095_, lean_object* v_____s_2096_){
_start:
{
lean_object* v_fst_2097_; 
v_fst_2097_ = lean_ctor_get(v_____s_2096_, 0);
lean_inc(v_fst_2097_);
lean_dec_ref(v_____s_2096_);
if (lean_obj_tag(v_fst_2097_) == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_box(0);
v___x_2099_ = lean_apply_2(v_toPure_2095_, lean_box(0), v___x_2098_);
return v___x_2099_;
}
else
{
lean_object* v_val_2100_; lean_object* v___x_2101_; 
v_val_2100_ = lean_ctor_get(v_fst_2097_, 0);
lean_inc(v_val_2100_);
lean_dec_ref(v_fst_2097_);
v___x_2101_ = lean_apply_2(v_toPure_2095_, lean_box(0), v_val_2100_);
return v___x_2101_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1(lean_object* v___x_2102_, lean_object* v_toPure_2103_, lean_object* v_a_2104_, lean_object* v___x_2105_, uint8_t v_____do__lift_2106_){
_start:
{
if (v_____do__lift_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec(v_a_2104_);
v___x_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2102_);
v___x_2108_ = lean_apply_2(v_toPure_2103_, lean_box(0), v___x_2107_);
return v___x_2108_;
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec_ref(v___x_2102_);
v___x_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2109_, 0, v_a_2104_);
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
lean_ctor_set(v___x_2111_, 1, v___x_2105_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
v___x_2113_ = lean_apply_2(v_toPure_2103_, lean_box(0), v___x_2112_);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_2114_, lean_object* v_toPure_2115_, lean_object* v_a_2116_, lean_object* v___x_2117_, lean_object* v_____do__lift_2118_){
_start:
{
uint8_t v_____do__lift_124__boxed_2119_; lean_object* v_res_2120_; 
v_____do__lift_124__boxed_2119_ = lean_unbox(v_____do__lift_2118_);
v_res_2120_ = l_Vector_findM_x3f___redArg___lam__1(v___x_2114_, v_toPure_2115_, v_a_2116_, v___x_2117_, v_____do__lift_124__boxed_2119_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2(lean_object* v___x_2121_, lean_object* v_toPure_2122_, lean_object* v___x_2123_, lean_object* v_f_2124_, lean_object* v_toBind_2125_, lean_object* v_a_2126_, lean_object* v_x_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_inc(v_a_2126_);
v___f_2129_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2129_, 0, v___x_2121_);
lean_closure_set(v___f_2129_, 1, v_toPure_2122_);
lean_closure_set(v___f_2129_, 2, v_a_2126_);
lean_closure_set(v___f_2129_, 3, v___x_2123_);
v___x_2130_ = lean_apply_1(v_f_2124_, v_a_2126_);
v___x_2131_ = lean_apply_4(v_toBind_2125_, lean_box(0), lean_box(0), v___x_2130_, v___f_2129_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2___boxed(lean_object* v___x_2132_, lean_object* v_toPure_2133_, lean_object* v___x_2134_, lean_object* v_f_2135_, lean_object* v_toBind_2136_, lean_object* v_a_2137_, lean_object* v_x_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Vector_findM_x3f___redArg___lam__2(v___x_2132_, v_toPure_2133_, v___x_2134_, v_f_2135_, v_toBind_2136_, v_a_2137_, v_x_2138_, v___y_2139_);
lean_dec_ref(v___y_2139_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg(lean_object* v_inst_2144_, lean_object* v_f_2145_, lean_object* v_as_2146_){
_start:
{
lean_object* v_toApplicative_2147_; lean_object* v_toBind_2148_; lean_object* v_toPure_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___f_2152_; lean_object* v___f_2153_; size_t v_sz_2154_; size_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_toApplicative_2147_ = lean_ctor_get(v_inst_2144_, 0);
v_toBind_2148_ = lean_ctor_get(v_inst_2144_, 1);
lean_inc(v_toBind_2148_);
v_toPure_2149_ = lean_ctor_get(v_toApplicative_2147_, 1);
v___x_2150_ = lean_box(0);
v___x_2151_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc(v_toPure_2149_);
v___f_2152_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2152_, 0, v_toPure_2149_);
lean_inc(v_toBind_2148_);
lean_inc(v_toPure_2149_);
v___f_2153_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2153_, 0, v___x_2151_);
lean_closure_set(v___f_2153_, 1, v_toPure_2149_);
lean_closure_set(v___f_2153_, 2, v___x_2150_);
lean_closure_set(v___f_2153_, 3, v_f_2145_);
lean_closure_set(v___f_2153_, 4, v_toBind_2148_);
v_sz_2154_ = lean_array_size(v_as_2146_);
v___x_2155_ = ((size_t)0ULL);
v___x_2156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2144_, v_as_2146_, v___f_2153_, v_sz_2154_, v___x_2155_, v___x_2151_);
v___x_2157_ = lean_apply_4(v_toBind_2148_, lean_box(0), lean_box(0), v___x_2156_, v___f_2152_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f(lean_object* v_n_2158_, lean_object* v_00_u03b1_2159_, lean_object* v_m_2160_, lean_object* v_inst_2161_, lean_object* v_f_2162_, lean_object* v_as_2163_){
_start:
{
lean_object* v_toApplicative_2164_; lean_object* v_toBind_2165_; lean_object* v_toPure_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___f_2169_; lean_object* v___f_2170_; size_t v_sz_2171_; size_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_toApplicative_2164_ = lean_ctor_get(v_inst_2161_, 0);
v_toBind_2165_ = lean_ctor_get(v_inst_2161_, 1);
lean_inc(v_toBind_2165_);
v_toPure_2166_ = lean_ctor_get(v_toApplicative_2164_, 1);
v___x_2167_ = lean_box(0);
v___x_2168_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc(v_toPure_2166_);
v___f_2169_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2169_, 0, v_toPure_2166_);
lean_inc(v_toBind_2165_);
lean_inc(v_toPure_2166_);
v___f_2170_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2170_, 0, v___x_2168_);
lean_closure_set(v___f_2170_, 1, v_toPure_2166_);
lean_closure_set(v___f_2170_, 2, v___x_2167_);
lean_closure_set(v___f_2170_, 3, v_f_2162_);
lean_closure_set(v___f_2170_, 4, v_toBind_2165_);
v_sz_2171_ = lean_array_size(v_as_2163_);
v___x_2172_ = ((size_t)0ULL);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2161_, v_as_2163_, v___f_2170_, v_sz_2171_, v___x_2172_, v___x_2168_);
v___x_2174_ = lean_apply_4(v_toBind_2165_, lean_box(0), lean_box(0), v___x_2173_, v___f_2169_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___boxed(lean_object* v_n_2175_, lean_object* v_00_u03b1_2176_, lean_object* v_m_2177_, lean_object* v_inst_2178_, lean_object* v_f_2179_, lean_object* v_as_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Vector_findM_x3f(v_n_2175_, v_00_u03b1_2176_, v_m_2177_, v_inst_2178_, v_f_2179_, v_as_2180_);
lean_dec(v_n_2175_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__1(lean_object* v___x_2182_, lean_object* v_toPure_2183_, lean_object* v___x_2184_, lean_object* v_____do__lift_2185_){
_start:
{
if (lean_obj_tag(v_____do__lift_2185_) == 1)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec_ref(v___x_2184_);
v___x_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_____do__lift_2185_);
v___x_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
lean_ctor_set(v___x_2187_, 1, v___x_2182_);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
v___x_2189_ = lean_apply_2(v_toPure_2183_, lean_box(0), v___x_2188_);
return v___x_2189_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec(v_____do__lift_2185_);
v___x_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2184_);
v___x_2191_ = lean_apply_2(v_toPure_2183_, lean_box(0), v___x_2190_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0(lean_object* v_f_2192_, lean_object* v_toBind_2193_, lean_object* v___f_2194_, lean_object* v_a_2195_, lean_object* v_x_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = lean_apply_1(v_f_2192_, v_a_2195_);
v___x_2199_ = lean_apply_4(v_toBind_2193_, lean_box(0), lean_box(0), v___x_2198_, v___f_2194_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0___boxed(lean_object* v_f_2200_, lean_object* v_toBind_2201_, lean_object* v___f_2202_, lean_object* v_a_2203_, lean_object* v_x_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Vector_findSomeM_x3f___redArg___lam__0(v_f_2200_, v_toBind_2201_, v___f_2202_, v_a_2203_, v_x_2204_, v___y_2205_);
lean_dec_ref(v___y_2205_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg(lean_object* v_inst_2207_, lean_object* v_f_2208_, lean_object* v_as_2209_){
_start:
{
lean_object* v_toApplicative_2210_; lean_object* v_toBind_2211_; lean_object* v_toPure_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___f_2215_; lean_object* v___f_2216_; lean_object* v___f_2217_; size_t v_sz_2218_; size_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_toApplicative_2210_ = lean_ctor_get(v_inst_2207_, 0);
v_toBind_2211_ = lean_ctor_get(v_inst_2207_, 1);
lean_inc(v_toBind_2211_);
v_toPure_2212_ = lean_ctor_get(v_toApplicative_2210_, 1);
v___x_2213_ = lean_box(0);
v___x_2214_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc(v_toPure_2212_);
v___f_2215_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2215_, 0, v_toPure_2212_);
lean_inc(v_toPure_2212_);
v___f_2216_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2216_, 0, v___x_2213_);
lean_closure_set(v___f_2216_, 1, v_toPure_2212_);
lean_closure_set(v___f_2216_, 2, v___x_2214_);
lean_inc(v_toBind_2211_);
v___f_2217_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2217_, 0, v_f_2208_);
lean_closure_set(v___f_2217_, 1, v_toBind_2211_);
lean_closure_set(v___f_2217_, 2, v___f_2216_);
v_sz_2218_ = lean_array_size(v_as_2209_);
v___x_2219_ = ((size_t)0ULL);
v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2207_, v_as_2209_, v___f_2217_, v_sz_2218_, v___x_2219_, v___x_2214_);
v___x_2221_ = lean_apply_4(v_toBind_2211_, lean_box(0), lean_box(0), v___x_2220_, v___f_2215_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f(lean_object* v_m_2222_, lean_object* v_00_u03b1_2223_, lean_object* v_00_u03b2_2224_, lean_object* v_n_2225_, lean_object* v_inst_2226_, lean_object* v_f_2227_, lean_object* v_as_2228_){
_start:
{
lean_object* v_toApplicative_2229_; lean_object* v_toBind_2230_; lean_object* v_toPure_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___f_2234_; lean_object* v___f_2235_; lean_object* v___f_2236_; size_t v_sz_2237_; size_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_toApplicative_2229_ = lean_ctor_get(v_inst_2226_, 0);
v_toBind_2230_ = lean_ctor_get(v_inst_2226_, 1);
lean_inc(v_toBind_2230_);
v_toPure_2231_ = lean_ctor_get(v_toApplicative_2229_, 1);
v___x_2232_ = lean_box(0);
v___x_2233_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc(v_toPure_2231_);
v___f_2234_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2234_, 0, v_toPure_2231_);
lean_inc(v_toPure_2231_);
v___f_2235_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2235_, 0, v___x_2232_);
lean_closure_set(v___f_2235_, 1, v_toPure_2231_);
lean_closure_set(v___f_2235_, 2, v___x_2233_);
lean_inc(v_toBind_2230_);
v___f_2236_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2236_, 0, v_f_2227_);
lean_closure_set(v___f_2236_, 1, v_toBind_2230_);
lean_closure_set(v___f_2236_, 2, v___f_2235_);
v_sz_2237_ = lean_array_size(v_as_2228_);
v___x_2238_ = ((size_t)0ULL);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2226_, v_as_2228_, v___f_2236_, v_sz_2237_, v___x_2238_, v___x_2233_);
v___x_2240_ = lean_apply_4(v_toBind_2230_, lean_box(0), lean_box(0), v___x_2239_, v___f_2234_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___boxed(lean_object* v_m_2241_, lean_object* v_00_u03b1_2242_, lean_object* v_00_u03b2_2243_, lean_object* v_n_2244_, lean_object* v_inst_2245_, lean_object* v_f_2246_, lean_object* v_as_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Vector_findSomeM_x3f(v_m_2241_, v_00_u03b1_2242_, v_00_u03b2_2243_, v_n_2244_, v_inst_2245_, v_f_2246_, v_as_2247_);
lean_dec(v_n_2244_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2249_, lean_object* v_a_2250_, uint8_t v_____do__lift_2251_){
_start:
{
if (v_____do__lift_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec(v_a_2250_);
v___x_2252_ = lean_box(0);
v___x_2253_ = lean_apply_2(v_toPure_2249_, lean_box(0), v___x_2252_);
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_a_2250_);
v___x_2255_ = lean_apply_2(v_toPure_2249_, lean_box(0), v___x_2254_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2256_, lean_object* v_a_2257_, lean_object* v_____do__lift_2258_){
_start:
{
uint8_t v_____do__lift_50__boxed_2259_; lean_object* v_res_2260_; 
v_____do__lift_50__boxed_2259_ = lean_unbox(v_____do__lift_2258_);
v_res_2260_ = l_Vector_findRevM_x3f___redArg___lam__0(v_toPure_2256_, v_a_2257_, v_____do__lift_50__boxed_2259_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2261_, lean_object* v_f_2262_, lean_object* v_toBind_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v___f_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_inc(v_a_2264_);
v___f_2265_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2265_, 0, v_toPure_2261_);
lean_closure_set(v___f_2265_, 1, v_a_2264_);
v___x_2266_ = lean_apply_1(v_f_2262_, v_a_2264_);
v___x_2267_ = lean_apply_4(v_toBind_2263_, lean_box(0), lean_box(0), v___x_2266_, v___f_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg(lean_object* v_inst_2268_, lean_object* v_f_2269_, lean_object* v_as_2270_){
_start:
{
lean_object* v_toApplicative_2271_; lean_object* v_toBind_2272_; lean_object* v_toPure_2273_; lean_object* v___f_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v_toApplicative_2271_ = lean_ctor_get(v_inst_2268_, 0);
v_toBind_2272_ = lean_ctor_get(v_inst_2268_, 1);
v_toPure_2273_ = lean_ctor_get(v_toApplicative_2271_, 1);
lean_inc(v_toBind_2272_);
lean_inc(v_toPure_2273_);
v___f_2274_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2274_, 0, v_toPure_2273_);
lean_closure_set(v___f_2274_, 1, v_f_2269_);
lean_closure_set(v___f_2274_, 2, v_toBind_2272_);
v___x_2275_ = lean_array_get_size(v_as_2270_);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2268_, v___f_2274_, v_as_2270_, v___x_2275_, lean_box(0));
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f(lean_object* v_n_2277_, lean_object* v_00_u03b1_2278_, lean_object* v_m_2279_, lean_object* v_inst_2280_, lean_object* v_f_2281_, lean_object* v_as_2282_){
_start:
{
lean_object* v_toApplicative_2283_; lean_object* v_toBind_2284_; lean_object* v_toPure_2285_; lean_object* v___f_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_toApplicative_2283_ = lean_ctor_get(v_inst_2280_, 0);
v_toBind_2284_ = lean_ctor_get(v_inst_2280_, 1);
v_toPure_2285_ = lean_ctor_get(v_toApplicative_2283_, 1);
lean_inc(v_toBind_2284_);
lean_inc(v_toPure_2285_);
v___f_2286_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2286_, 0, v_toPure_2285_);
lean_closure_set(v___f_2286_, 1, v_f_2281_);
lean_closure_set(v___f_2286_, 2, v_toBind_2284_);
v___x_2287_ = lean_array_get_size(v_as_2282_);
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2280_, v___f_2286_, v_as_2282_, v___x_2287_, lean_box(0));
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___boxed(lean_object* v_n_2289_, lean_object* v_00_u03b1_2290_, lean_object* v_m_2291_, lean_object* v_inst_2292_, lean_object* v_f_2293_, lean_object* v_as_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Vector_findRevM_x3f(v_n_2289_, v_00_u03b1_2290_, v_m_2291_, v_inst_2292_, v_f_2293_, v_as_2294_);
lean_dec(v_n_2289_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___redArg(lean_object* v_inst_2296_, lean_object* v_f_2297_, lean_object* v_as_2298_){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = lean_array_get_size(v_as_2298_);
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2296_, v_f_2297_, v_as_2298_, v___x_2299_, lean_box(0));
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f(lean_object* v_m_2301_, lean_object* v_00_u03b1_2302_, lean_object* v_00_u03b2_2303_, lean_object* v_n_2304_, lean_object* v_inst_2305_, lean_object* v_f_2306_, lean_object* v_as_2307_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_array_get_size(v_as_2307_);
v___x_2309_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2305_, v_f_2306_, v_as_2307_, v___x_2308_, lean_box(0));
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___boxed(lean_object* v_m_2310_, lean_object* v_00_u03b1_2311_, lean_object* v_00_u03b2_2312_, lean_object* v_n_2313_, lean_object* v_inst_2314_, lean_object* v_f_2315_, lean_object* v_as_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Vector_findSomeRevM_x3f(v_m_2310_, v_00_u03b1_2311_, v_00_u03b2_2312_, v_n_2313_, v_inst_2314_, v_f_2315_, v_as_2316_);
lean_dec(v_n_2313_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0(lean_object* v_f_2318_, lean_object* v___x_2319_, lean_object* v___x_2320_, lean_object* v_a_2321_, lean_object* v_x_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
lean_inc(v_a_2321_);
v___x_2324_ = lean_apply_1(v_f_2318_, v_a_2321_);
v___x_2325_ = lean_unbox(v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; 
lean_dec(v_a_2321_);
v___x_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2319_);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
lean_dec_ref(v___x_2319_);
v___x_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_a_2321_);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___x_2320_);
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
return v___x_2330_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0___boxed(lean_object* v_f_2331_, lean_object* v___x_2332_, lean_object* v___x_2333_, lean_object* v_a_2334_, lean_object* v_x_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Vector_find_x3f___redArg___lam__0(v_f_2331_, v___x_2332_, v___x_2333_, v_a_2334_, v_x_2335_, v___y_2336_);
lean_dec_ref(v___y_2336_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg(lean_object* v_f_2338_, lean_object* v_as_2339_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___f_2344_; size_t v_sz_2345_; size_t v___x_2346_; lean_object* v___x_2347_; lean_object* v_fst_2348_; 
v___x_2340_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2341_ = lean_box(0);
v___x_2342_ = lean_box(0);
v___x_2343_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2344_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2344_, 0, v_f_2338_);
lean_closure_set(v___f_2344_, 1, v___x_2343_);
lean_closure_set(v___f_2344_, 2, v___x_2342_);
v_sz_2345_ = lean_array_size(v_as_2339_);
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2340_, v_as_2339_, v___f_2344_, v_sz_2345_, v___x_2346_, v___x_2343_);
v_fst_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_fst_2348_);
lean_dec(v___x_2347_);
if (lean_obj_tag(v_fst_2348_) == 0)
{
return v___x_2341_;
}
else
{
lean_object* v_val_2349_; 
v_val_2349_ = lean_ctor_get(v_fst_2348_, 0);
lean_inc(v_val_2349_);
lean_dec_ref(v_fst_2348_);
return v_val_2349_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f(lean_object* v_n_2350_, lean_object* v_00_u03b1_2351_, lean_object* v_f_2352_, lean_object* v_as_2353_){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___f_2358_; size_t v_sz_2359_; size_t v___x_2360_; lean_object* v___x_2361_; lean_object* v_fst_2362_; 
v___x_2354_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2355_ = lean_box(0);
v___x_2356_ = lean_box(0);
v___x_2357_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2358_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2358_, 0, v_f_2352_);
lean_closure_set(v___f_2358_, 1, v___x_2357_);
lean_closure_set(v___f_2358_, 2, v___x_2356_);
v_sz_2359_ = lean_array_size(v_as_2353_);
v___x_2360_ = ((size_t)0ULL);
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2354_, v_as_2353_, v___f_2358_, v_sz_2359_, v___x_2360_, v___x_2357_);
v_fst_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_fst_2362_);
lean_dec(v___x_2361_);
if (lean_obj_tag(v_fst_2362_) == 0)
{
return v___x_2355_;
}
else
{
lean_object* v_val_2363_; 
v_val_2363_ = lean_ctor_get(v_fst_2362_, 0);
lean_inc(v_val_2363_);
lean_dec_ref(v_fst_2362_);
return v_val_2363_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___boxed(lean_object* v_n_2364_, lean_object* v_00_u03b1_2365_, lean_object* v_f_2366_, lean_object* v_as_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Vector_find_x3f(v_n_2364_, v_00_u03b1_2365_, v_f_2366_, v_as_2367_);
lean_dec(v_n_2364_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg___lam__0(lean_object* v_f_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___x_2371_; uint8_t v___x_2372_; 
lean_inc(v_a_2370_);
v___x_2371_ = lean_apply_1(v_f_2369_, v_a_2370_);
v___x_2372_ = lean_unbox(v___x_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; 
lean_dec(v_a_2370_);
v___x_2373_ = lean_box(0);
return v___x_2373_;
}
else
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2374_, 0, v_a_2370_);
return v___x_2374_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg(lean_object* v_f_2375_, lean_object* v_as_2376_){
_start:
{
lean_object* v___f_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___f_2377_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2377_, 0, v_f_2375_);
v___x_2378_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2379_ = lean_array_get_size(v_as_2376_);
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2378_, v___f_2377_, v_as_2376_, v___x_2379_, lean_box(0));
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f(lean_object* v_n_2381_, lean_object* v_00_u03b1_2382_, lean_object* v_f_2383_, lean_object* v_as_2384_){
_start:
{
lean_object* v___f_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___f_2385_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2385_, 0, v_f_2383_);
v___x_2386_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2387_ = lean_array_get_size(v_as_2384_);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2386_, v___f_2385_, v_as_2384_, v___x_2387_, lean_box(0));
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___boxed(lean_object* v_n_2389_, lean_object* v_00_u03b1_2390_, lean_object* v_f_2391_, lean_object* v_as_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Vector_findRev_x3f(v_n_2389_, v_00_u03b1_2390_, v_f_2391_, v_as_2392_);
lean_dec(v_n_2389_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0(lean_object* v_f_2394_, lean_object* v___x_2395_, lean_object* v___x_2396_, lean_object* v_a_2397_, lean_object* v_x_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_apply_1(v_f_2394_, v_a_2397_);
if (lean_obj_tag(v___x_2400_) == 1)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_dec_ref(v___x_2396_);
v___x_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v___x_2395_);
v___x_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
return v___x_2403_;
}
else
{
lean_object* v___x_2404_; 
lean_dec(v___x_2400_);
v___x_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2396_);
return v___x_2404_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2405_, lean_object* v___x_2406_, lean_object* v___x_2407_, lean_object* v_a_2408_, lean_object* v_x_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Vector_findSome_x3f___redArg___lam__0(v_f_2405_, v___x_2406_, v___x_2407_, v_a_2408_, v_x_2409_, v___y_2410_);
lean_dec_ref(v___y_2410_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg(lean_object* v_f_2412_, lean_object* v_as_2413_){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___f_2418_; size_t v_sz_2419_; size_t v___x_2420_; lean_object* v___x_2421_; lean_object* v_fst_2422_; 
v___x_2414_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2415_ = lean_box(0);
v___x_2416_ = lean_box(0);
v___x_2417_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2418_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2418_, 0, v_f_2412_);
lean_closure_set(v___f_2418_, 1, v___x_2416_);
lean_closure_set(v___f_2418_, 2, v___x_2417_);
v_sz_2419_ = lean_array_size(v_as_2413_);
v___x_2420_ = ((size_t)0ULL);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2414_, v_as_2413_, v___f_2418_, v_sz_2419_, v___x_2420_, v___x_2417_);
v_fst_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_fst_2422_);
lean_dec(v___x_2421_);
if (lean_obj_tag(v_fst_2422_) == 0)
{
return v___x_2415_;
}
else
{
lean_object* v_val_2423_; 
v_val_2423_ = lean_ctor_get(v_fst_2422_, 0);
lean_inc(v_val_2423_);
lean_dec_ref(v_fst_2422_);
return v_val_2423_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f(lean_object* v_00_u03b1_2424_, lean_object* v_00_u03b2_2425_, lean_object* v_n_2426_, lean_object* v_f_2427_, lean_object* v_as_2428_){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___f_2433_; size_t v_sz_2434_; size_t v___x_2435_; lean_object* v___x_2436_; lean_object* v_fst_2437_; 
v___x_2429_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_box(0);
v___x_2432_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2433_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2433_, 0, v_f_2427_);
lean_closure_set(v___f_2433_, 1, v___x_2431_);
lean_closure_set(v___f_2433_, 2, v___x_2432_);
v_sz_2434_ = lean_array_size(v_as_2428_);
v___x_2435_ = ((size_t)0ULL);
v___x_2436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2429_, v_as_2428_, v___f_2433_, v_sz_2434_, v___x_2435_, v___x_2432_);
v_fst_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_fst_2437_);
lean_dec(v___x_2436_);
if (lean_obj_tag(v_fst_2437_) == 0)
{
return v___x_2430_;
}
else
{
lean_object* v_val_2438_; 
v_val_2438_ = lean_ctor_get(v_fst_2437_, 0);
lean_inc(v_val_2438_);
lean_dec_ref(v_fst_2437_);
return v_val_2438_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___boxed(lean_object* v_00_u03b1_2439_, lean_object* v_00_u03b2_2440_, lean_object* v_n_2441_, lean_object* v_f_2442_, lean_object* v_as_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Vector_findSome_x3f(v_00_u03b1_2439_, v_00_u03b2_2440_, v_n_2441_, v_f_2442_, v_as_2443_);
lean_dec(v_n_2441_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2445_, lean_object* v_x_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_apply_1(v_f_2445_, v_x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg(lean_object* v_f_2448_, lean_object* v_as_2449_){
_start:
{
lean_object* v___f_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___f_2450_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2450_, 0, v_f_2448_);
v___x_2451_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2452_ = lean_array_get_size(v_as_2449_);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2451_, v___f_2450_, v_as_2449_, v___x_2452_, lean_box(0));
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f(lean_object* v_00_u03b1_2454_, lean_object* v_00_u03b2_2455_, lean_object* v_n_2456_, lean_object* v_f_2457_, lean_object* v_as_2458_){
_start:
{
lean_object* v___f_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___f_2459_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2459_, 0, v_f_2457_);
v___x_2460_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2461_ = lean_array_get_size(v_as_2458_);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2460_, v___f_2459_, v_as_2458_, v___x_2461_, lean_box(0));
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___boxed(lean_object* v_00_u03b1_2463_, lean_object* v_00_u03b2_2464_, lean_object* v_n_2465_, lean_object* v_f_2466_, lean_object* v_as_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Vector_findSomeRev_x3f(v_00_u03b1_2463_, v_00_u03b2_2464_, v_n_2465_, v_f_2466_, v_as_2467_);
lean_dec(v_n_2465_);
return v_res_2468_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf___redArg(lean_object* v_inst_2469_, lean_object* v_xs_2470_, lean_object* v_ys_2471_){
_start:
{
uint8_t v___x_2472_; 
v___x_2472_ = l_Array_isPrefixOf___redArg(v_inst_2469_, v_xs_2470_, v_ys_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___redArg___boxed(lean_object* v_inst_2473_, lean_object* v_xs_2474_, lean_object* v_ys_2475_){
_start:
{
uint8_t v_res_2476_; lean_object* v_r_2477_; 
v_res_2476_ = l_Vector_isPrefixOf___redArg(v_inst_2473_, v_xs_2474_, v_ys_2475_);
lean_dec_ref(v_ys_2475_);
lean_dec_ref(v_xs_2474_);
v_r_2477_ = lean_box(v_res_2476_);
return v_r_2477_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf(lean_object* v_00_u03b1_2478_, lean_object* v_m_2479_, lean_object* v_n_2480_, lean_object* v_inst_2481_, lean_object* v_xs_2482_, lean_object* v_ys_2483_){
_start:
{
uint8_t v___x_2484_; 
v___x_2484_ = l_Array_isPrefixOf___redArg(v_inst_2481_, v_xs_2482_, v_ys_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___boxed(lean_object* v_00_u03b1_2485_, lean_object* v_m_2486_, lean_object* v_n_2487_, lean_object* v_inst_2488_, lean_object* v_xs_2489_, lean_object* v_ys_2490_){
_start:
{
uint8_t v_res_2491_; lean_object* v_r_2492_; 
v_res_2491_ = l_Vector_isPrefixOf(v_00_u03b1_2485_, v_m_2486_, v_n_2487_, v_inst_2488_, v_xs_2489_, v_ys_2490_);
lean_dec_ref(v_ys_2490_);
lean_dec_ref(v_xs_2489_);
lean_dec(v_n_2487_);
lean_dec(v_m_2486_);
v_r_2492_ = lean_box(v_res_2491_);
return v_r_2492_;
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___redArg(lean_object* v_inst_2493_, lean_object* v_p_2494_, lean_object* v_xs_2495_){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2496_ = lean_unsigned_to_nat(0u);
v___x_2497_ = lean_array_get_size(v_xs_2495_);
v___x_2498_ = lean_nat_dec_lt(v___x_2496_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_object* v_toApplicative_2499_; lean_object* v_toPure_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_dec_ref(v_xs_2495_);
lean_dec(v_p_2494_);
v_toApplicative_2499_ = lean_ctor_get(v_inst_2493_, 0);
lean_inc_ref(v_toApplicative_2499_);
lean_dec_ref(v_inst_2493_);
v_toPure_2500_ = lean_ctor_get(v_toApplicative_2499_, 1);
lean_inc(v_toPure_2500_);
lean_dec_ref(v_toApplicative_2499_);
v___x_2501_ = lean_box(v___x_2498_);
v___x_2502_ = lean_apply_2(v_toPure_2500_, lean_box(0), v___x_2501_);
return v___x_2502_;
}
else
{
if (v___x_2498_ == 0)
{
lean_object* v_toApplicative_2503_; lean_object* v_toPure_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec_ref(v_xs_2495_);
lean_dec(v_p_2494_);
v_toApplicative_2503_ = lean_ctor_get(v_inst_2493_, 0);
lean_inc_ref(v_toApplicative_2503_);
lean_dec_ref(v_inst_2493_);
v_toPure_2504_ = lean_ctor_get(v_toApplicative_2503_, 1);
lean_inc(v_toPure_2504_);
lean_dec_ref(v_toApplicative_2503_);
v___x_2505_ = lean_box(v___x_2498_);
v___x_2506_ = lean_apply_2(v_toPure_2504_, lean_box(0), v___x_2505_);
return v___x_2506_;
}
else
{
size_t v___x_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = ((size_t)0ULL);
v___x_2508_ = lean_usize_of_nat(v___x_2497_);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2493_, v_p_2494_, v_xs_2495_, v___x_2507_, v___x_2508_);
return v___x_2509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM(lean_object* v_m_2510_, lean_object* v_00_u03b1_2511_, lean_object* v_n_2512_, lean_object* v_inst_2513_, lean_object* v_p_2514_, lean_object* v_xs_2515_){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2516_ = lean_unsigned_to_nat(0u);
v___x_2517_ = lean_array_get_size(v_xs_2515_);
v___x_2518_ = lean_nat_dec_lt(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v_toApplicative_2519_; lean_object* v_toPure_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec_ref(v_xs_2515_);
lean_dec(v_p_2514_);
v_toApplicative_2519_ = lean_ctor_get(v_inst_2513_, 0);
lean_inc_ref(v_toApplicative_2519_);
lean_dec_ref(v_inst_2513_);
v_toPure_2520_ = lean_ctor_get(v_toApplicative_2519_, 1);
lean_inc(v_toPure_2520_);
lean_dec_ref(v_toApplicative_2519_);
v___x_2521_ = lean_box(v___x_2518_);
v___x_2522_ = lean_apply_2(v_toPure_2520_, lean_box(0), v___x_2521_);
return v___x_2522_;
}
else
{
if (v___x_2518_ == 0)
{
lean_object* v_toApplicative_2523_; lean_object* v_toPure_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec_ref(v_xs_2515_);
lean_dec(v_p_2514_);
v_toApplicative_2523_ = lean_ctor_get(v_inst_2513_, 0);
lean_inc_ref(v_toApplicative_2523_);
lean_dec_ref(v_inst_2513_);
v_toPure_2524_ = lean_ctor_get(v_toApplicative_2523_, 1);
lean_inc(v_toPure_2524_);
lean_dec_ref(v_toApplicative_2523_);
v___x_2525_ = lean_box(v___x_2518_);
v___x_2526_ = lean_apply_2(v_toPure_2524_, lean_box(0), v___x_2525_);
return v___x_2526_;
}
else
{
size_t v___x_2527_; size_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = lean_usize_of_nat(v___x_2517_);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2513_, v_p_2514_, v_xs_2515_, v___x_2527_, v___x_2528_);
return v___x_2529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___boxed(lean_object* v_m_2530_, lean_object* v_00_u03b1_2531_, lean_object* v_n_2532_, lean_object* v_inst_2533_, lean_object* v_p_2534_, lean_object* v_xs_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Vector_anyM(v_m_2530_, v_00_u03b1_2531_, v_n_2532_, v_inst_2533_, v_p_2534_, v_xs_2535_);
lean_dec(v_n_2532_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0(lean_object* v_toPure_2537_, uint8_t v_____do__lift_2538_){
_start:
{
if (v_____do__lift_2538_ == 0)
{
uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = 1;
v___x_2540_ = lean_box(v___x_2539_);
v___x_2541_ = lean_apply_2(v_toPure_2537_, lean_box(0), v___x_2540_);
return v___x_2541_;
}
else
{
uint8_t v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = 0;
v___x_2543_ = lean_box(v___x_2542_);
v___x_2544_ = lean_apply_2(v_toPure_2537_, lean_box(0), v___x_2543_);
return v___x_2544_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0___boxed(lean_object* v_toPure_2545_, lean_object* v_____do__lift_2546_){
_start:
{
uint8_t v_____do__lift_117__boxed_2547_; lean_object* v_res_2548_; 
v_____do__lift_117__boxed_2547_ = lean_unbox(v_____do__lift_2546_);
v_res_2548_ = l_Vector_allM___redArg___lam__0(v_toPure_2545_, v_____do__lift_117__boxed_2547_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1(lean_object* v_toPure_2549_, uint8_t v___x_2550_, uint8_t v_____do__lift_2551_){
_start:
{
if (v_____do__lift_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_box(v___x_2550_);
v___x_2553_ = lean_apply_2(v_toPure_2549_, lean_box(0), v___x_2552_);
return v___x_2553_;
}
else
{
uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = 0;
v___x_2555_ = lean_box(v___x_2554_);
v___x_2556_ = lean_apply_2(v_toPure_2549_, lean_box(0), v___x_2555_);
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1___boxed(lean_object* v_toPure_2557_, lean_object* v___x_2558_, lean_object* v_____do__lift_2559_){
_start:
{
uint8_t v___x_132__boxed_2560_; uint8_t v_____do__lift_133__boxed_2561_; lean_object* v_res_2562_; 
v___x_132__boxed_2560_ = lean_unbox(v___x_2558_);
v_____do__lift_133__boxed_2561_ = lean_unbox(v_____do__lift_2559_);
v_res_2562_ = l_Vector_allM___redArg___lam__1(v_toPure_2557_, v___x_132__boxed_2560_, v_____do__lift_133__boxed_2561_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__2(lean_object* v_p_2563_, lean_object* v_toBind_2564_, lean_object* v___f_2565_, lean_object* v_v_2566_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_apply_1(v_p_2563_, v_v_2566_);
v___x_2568_ = lean_apply_4(v_toBind_2564_, lean_box(0), lean_box(0), v___x_2567_, v___f_2565_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg(lean_object* v_inst_2569_, lean_object* v_p_2570_, lean_object* v_xs_2571_){
_start:
{
lean_object* v_toApplicative_2572_; lean_object* v_toBind_2573_; lean_object* v_toPure_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; uint8_t v___x_2578_; 
v_toApplicative_2572_ = lean_ctor_get(v_inst_2569_, 0);
v_toBind_2573_ = lean_ctor_get(v_inst_2569_, 1);
lean_inc(v_toBind_2573_);
v_toPure_2574_ = lean_ctor_get(v_toApplicative_2572_, 1);
v___x_2575_ = lean_unsigned_to_nat(0u);
v___x_2576_ = lean_array_get_size(v_xs_2571_);
lean_inc(v_toPure_2574_);
v___f_2577_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2577_, 0, v_toPure_2574_);
v___x_2578_ = lean_nat_dec_lt(v___x_2575_, v___x_2576_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_inc(v_toPure_2574_);
lean_dec_ref(v_xs_2571_);
lean_dec(v_p_2570_);
lean_dec_ref(v_inst_2569_);
v___x_2579_ = lean_box(v___x_2578_);
v___x_2580_ = lean_apply_2(v_toPure_2574_, lean_box(0), v___x_2579_);
v___x_2581_ = lean_apply_4(v_toBind_2573_, lean_box(0), lean_box(0), v___x_2580_, v___f_2577_);
return v___x_2581_;
}
else
{
if (v___x_2578_ == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_inc(v_toPure_2574_);
lean_dec_ref(v_xs_2571_);
lean_dec(v_p_2570_);
lean_dec_ref(v_inst_2569_);
v___x_2582_ = lean_box(v___x_2578_);
v___x_2583_ = lean_apply_2(v_toPure_2574_, lean_box(0), v___x_2582_);
v___x_2584_ = lean_apply_4(v_toBind_2573_, lean_box(0), lean_box(0), v___x_2583_, v___f_2577_);
return v___x_2584_;
}
else
{
lean_object* v___x_2585_; lean_object* v___f_2586_; lean_object* v___f_2587_; size_t v___x_2588_; size_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2585_ = lean_box(v___x_2578_);
lean_inc(v_toPure_2574_);
v___f_2586_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2586_, 0, v_toPure_2574_);
lean_closure_set(v___f_2586_, 1, v___x_2585_);
lean_inc(v_toBind_2573_);
v___f_2587_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2587_, 0, v_p_2570_);
lean_closure_set(v___f_2587_, 1, v_toBind_2573_);
lean_closure_set(v___f_2587_, 2, v___f_2586_);
v___x_2588_ = ((size_t)0ULL);
v___x_2589_ = lean_usize_of_nat(v___x_2576_);
v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2569_, v___f_2587_, v_xs_2571_, v___x_2588_, v___x_2589_);
v___x_2591_ = lean_apply_4(v_toBind_2573_, lean_box(0), lean_box(0), v___x_2590_, v___f_2577_);
return v___x_2591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM(lean_object* v_m_2592_, lean_object* v_00_u03b1_2593_, lean_object* v_n_2594_, lean_object* v_inst_2595_, lean_object* v_p_2596_, lean_object* v_xs_2597_){
_start:
{
lean_object* v_toApplicative_2598_; lean_object* v_toBind_2599_; lean_object* v_toPure_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___f_2603_; uint8_t v___x_2604_; 
v_toApplicative_2598_ = lean_ctor_get(v_inst_2595_, 0);
v_toBind_2599_ = lean_ctor_get(v_inst_2595_, 1);
lean_inc(v_toBind_2599_);
v_toPure_2600_ = lean_ctor_get(v_toApplicative_2598_, 1);
v___x_2601_ = lean_unsigned_to_nat(0u);
v___x_2602_ = lean_array_get_size(v_xs_2597_);
lean_inc(v_toPure_2600_);
v___f_2603_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2603_, 0, v_toPure_2600_);
v___x_2604_ = lean_nat_dec_lt(v___x_2601_, v___x_2602_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_inc(v_toPure_2600_);
lean_dec_ref(v_xs_2597_);
lean_dec(v_p_2596_);
lean_dec_ref(v_inst_2595_);
v___x_2605_ = lean_box(v___x_2604_);
v___x_2606_ = lean_apply_2(v_toPure_2600_, lean_box(0), v___x_2605_);
v___x_2607_ = lean_apply_4(v_toBind_2599_, lean_box(0), lean_box(0), v___x_2606_, v___f_2603_);
return v___x_2607_;
}
else
{
if (v___x_2604_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_inc(v_toPure_2600_);
lean_dec_ref(v_xs_2597_);
lean_dec(v_p_2596_);
lean_dec_ref(v_inst_2595_);
v___x_2608_ = lean_box(v___x_2604_);
v___x_2609_ = lean_apply_2(v_toPure_2600_, lean_box(0), v___x_2608_);
v___x_2610_ = lean_apply_4(v_toBind_2599_, lean_box(0), lean_box(0), v___x_2609_, v___f_2603_);
return v___x_2610_;
}
else
{
lean_object* v___x_2611_; lean_object* v___f_2612_; lean_object* v___f_2613_; size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2611_ = lean_box(v___x_2604_);
lean_inc(v_toPure_2600_);
v___f_2612_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2612_, 0, v_toPure_2600_);
lean_closure_set(v___f_2612_, 1, v___x_2611_);
lean_inc(v_toBind_2599_);
v___f_2613_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2613_, 0, v_p_2596_);
lean_closure_set(v___f_2613_, 1, v_toBind_2599_);
lean_closure_set(v___f_2613_, 2, v___f_2612_);
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = lean_usize_of_nat(v___x_2602_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2595_, v___f_2613_, v_xs_2597_, v___x_2614_, v___x_2615_);
v___x_2617_ = lean_apply_4(v_toBind_2599_, lean_box(0), lean_box(0), v___x_2616_, v___f_2603_);
return v___x_2617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___boxed(lean_object* v_m_2618_, lean_object* v_00_u03b1_2619_, lean_object* v_n_2620_, lean_object* v_inst_2621_, lean_object* v_p_2622_, lean_object* v_xs_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Vector_allM(v_m_2618_, v_00_u03b1_2619_, v_n_2620_, v_inst_2621_, v_p_2622_, v_xs_2623_);
lean_dec(v_n_2620_);
return v_res_2624_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg___lam__0(lean_object* v_p_2625_, lean_object* v_x_2626_){
_start:
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = lean_apply_1(v_p_2625_, v_x_2626_);
v___x_2628_ = lean_unbox(v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___lam__0___boxed(lean_object* v_p_2629_, lean_object* v_x_2630_){
_start:
{
uint8_t v_res_2631_; lean_object* v_r_2632_; 
v_res_2631_ = l_Vector_any___redArg___lam__0(v_p_2629_, v_x_2630_);
v_r_2632_ = lean_box(v_res_2631_);
return v_r_2632_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg(lean_object* v_xs_2633_, lean_object* v_p_2634_){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = lean_array_get_size(v_xs_2633_);
v___x_2637_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2638_ = lean_nat_dec_lt(v___x_2635_, v___x_2636_);
if (v___x_2638_ == 0)
{
lean_dec_ref(v_p_2634_);
lean_dec_ref(v_xs_2633_);
return v___x_2638_;
}
else
{
if (v___x_2638_ == 0)
{
lean_dec_ref(v_p_2634_);
lean_dec_ref(v_xs_2633_);
return v___x_2638_;
}
else
{
lean_object* v___f_2639_; size_t v___x_2640_; size_t v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___f_2639_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2639_, 0, v_p_2634_);
v___x_2640_ = ((size_t)0ULL);
v___x_2641_ = lean_usize_of_nat(v___x_2636_);
v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2637_, v___f_2639_, v_xs_2633_, v___x_2640_, v___x_2641_);
v___x_2643_ = lean_unbox(v___x_2642_);
lean_dec(v___x_2642_);
return v___x_2643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___boxed(lean_object* v_xs_2644_, lean_object* v_p_2645_){
_start:
{
uint8_t v_res_2646_; lean_object* v_r_2647_; 
v_res_2646_ = l_Vector_any___redArg(v_xs_2644_, v_p_2645_);
v_r_2647_ = lean_box(v_res_2646_);
return v_r_2647_;
}
}
LEAN_EXPORT uint8_t l_Vector_any(lean_object* v_00_u03b1_2648_, lean_object* v_n_2649_, lean_object* v_xs_2650_, lean_object* v_p_2651_){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2652_ = lean_unsigned_to_nat(0u);
v___x_2653_ = lean_array_get_size(v_xs_2650_);
v___x_2654_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2655_ = lean_nat_dec_lt(v___x_2652_, v___x_2653_);
if (v___x_2655_ == 0)
{
lean_dec_ref(v_p_2651_);
lean_dec_ref(v_xs_2650_);
return v___x_2655_;
}
else
{
if (v___x_2655_ == 0)
{
lean_dec_ref(v_p_2651_);
lean_dec_ref(v_xs_2650_);
return v___x_2655_;
}
else
{
lean_object* v___f_2656_; size_t v___x_2657_; size_t v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___f_2656_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2656_, 0, v_p_2651_);
v___x_2657_ = ((size_t)0ULL);
v___x_2658_ = lean_usize_of_nat(v___x_2653_);
v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2654_, v___f_2656_, v_xs_2650_, v___x_2657_, v___x_2658_);
v___x_2660_ = lean_unbox(v___x_2659_);
lean_dec(v___x_2659_);
return v___x_2660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___boxed(lean_object* v_00_u03b1_2661_, lean_object* v_n_2662_, lean_object* v_xs_2663_, lean_object* v_p_2664_){
_start:
{
uint8_t v_res_2665_; lean_object* v_r_2666_; 
v_res_2665_ = l_Vector_any(v_00_u03b1_2661_, v_n_2662_, v_xs_2663_, v_p_2664_);
lean_dec(v_n_2662_);
v_r_2666_ = lean_box(v_res_2665_);
return v_r_2666_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg___lam__0(lean_object* v_p_2667_, uint8_t v___x_2668_, lean_object* v_v_2669_){
_start:
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = lean_apply_1(v_p_2667_, v_v_2669_);
v___x_2671_ = lean_unbox(v___x_2670_);
if (v___x_2671_ == 0)
{
return v___x_2668_;
}
else
{
uint8_t v___x_2672_; 
v___x_2672_ = 0;
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___lam__0___boxed(lean_object* v_p_2673_, lean_object* v___x_2674_, lean_object* v_v_2675_){
_start:
{
uint8_t v___x_79__boxed_2676_; uint8_t v_res_2677_; lean_object* v_r_2678_; 
v___x_79__boxed_2676_ = lean_unbox(v___x_2674_);
v_res_2677_ = l_Vector_all___redArg___lam__0(v_p_2673_, v___x_79__boxed_2676_, v_v_2675_);
v_r_2678_ = lean_box(v_res_2677_);
return v_r_2678_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg(lean_object* v_xs_2679_, lean_object* v_p_2680_){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v___x_2681_ = lean_unsigned_to_nat(0u);
v___x_2682_ = lean_array_get_size(v_xs_2679_);
v___x_2683_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2684_ = lean_nat_dec_lt(v___x_2681_, v___x_2682_);
if (v___x_2684_ == 0)
{
uint8_t v___x_2685_; 
lean_dec_ref(v_p_2680_);
lean_dec_ref(v_xs_2679_);
v___x_2685_ = 1;
return v___x_2685_;
}
else
{
if (v___x_2684_ == 0)
{
lean_dec_ref(v_p_2680_);
lean_dec_ref(v_xs_2679_);
return v___x_2684_;
}
else
{
lean_object* v___x_2686_; lean_object* v___f_2687_; size_t v___x_2688_; size_t v___x_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2686_ = lean_box(v___x_2684_);
v___f_2687_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2687_, 0, v_p_2680_);
lean_closure_set(v___f_2687_, 1, v___x_2686_);
v___x_2688_ = ((size_t)0ULL);
v___x_2689_ = lean_usize_of_nat(v___x_2682_);
v___x_2690_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2683_, v___f_2687_, v_xs_2679_, v___x_2688_, v___x_2689_);
v___x_2691_ = lean_unbox(v___x_2690_);
lean_dec(v___x_2690_);
if (v___x_2691_ == 0)
{
return v___x_2684_;
}
else
{
uint8_t v___x_2692_; 
v___x_2692_ = 0;
return v___x_2692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___boxed(lean_object* v_xs_2693_, lean_object* v_p_2694_){
_start:
{
uint8_t v_res_2695_; lean_object* v_r_2696_; 
v_res_2695_ = l_Vector_all___redArg(v_xs_2693_, v_p_2694_);
v_r_2696_ = lean_box(v_res_2695_);
return v_r_2696_;
}
}
LEAN_EXPORT uint8_t l_Vector_all(lean_object* v_00_u03b1_2697_, lean_object* v_n_2698_, lean_object* v_xs_2699_, lean_object* v_p_2700_){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = lean_array_get_size(v_xs_2699_);
v___x_2703_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2704_ = lean_nat_dec_lt(v___x_2701_, v___x_2702_);
if (v___x_2704_ == 0)
{
uint8_t v___x_2705_; 
lean_dec_ref(v_p_2700_);
lean_dec_ref(v_xs_2699_);
v___x_2705_ = 1;
return v___x_2705_;
}
else
{
if (v___x_2704_ == 0)
{
lean_dec_ref(v_p_2700_);
lean_dec_ref(v_xs_2699_);
return v___x_2704_;
}
else
{
lean_object* v___x_2706_; lean_object* v___f_2707_; size_t v___x_2708_; size_t v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2706_ = lean_box(v___x_2704_);
v___f_2707_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2707_, 0, v_p_2700_);
lean_closure_set(v___f_2707_, 1, v___x_2706_);
v___x_2708_ = ((size_t)0ULL);
v___x_2709_ = lean_usize_of_nat(v___x_2702_);
v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2703_, v___f_2707_, v_xs_2699_, v___x_2708_, v___x_2709_);
v___x_2711_ = lean_unbox(v___x_2710_);
lean_dec(v___x_2710_);
if (v___x_2711_ == 0)
{
return v___x_2704_;
}
else
{
uint8_t v___x_2712_; 
v___x_2712_ = 0;
return v___x_2712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___boxed(lean_object* v_00_u03b1_2713_, lean_object* v_n_2714_, lean_object* v_xs_2715_, lean_object* v_p_2716_){
_start:
{
uint8_t v_res_2717_; lean_object* v_r_2718_; 
v_res_2717_ = l_Vector_all(v_00_u03b1_2713_, v_n_2714_, v_xs_2715_, v_p_2716_);
lean_dec(v_n_2714_);
v_r_2718_ = lean_box(v_res_2717_);
return v_r_2718_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0(lean_object* v_p_2719_, lean_object* v_x1_2720_, lean_object* v_x2_2721_){
_start:
{
lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2722_ = lean_apply_1(v_p_2719_, v_x1_2720_);
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
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0___boxed(lean_object* v_p_2726_, lean_object* v_x1_2727_, lean_object* v_x2_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Vector_countP___redArg___lam__0(v_p_2726_, v_x1_2727_, v_x2_2728_);
lean_dec(v_x2_2728_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg(lean_object* v_p_2730_, lean_object* v_xs_2731_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2732_ = lean_unsigned_to_nat(0u);
v___x_2733_ = lean_array_get_size(v_xs_2731_);
v___x_2734_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2735_ = lean_nat_dec_lt(v___x_2732_, v___x_2733_);
if (v___x_2735_ == 0)
{
lean_dec_ref(v_xs_2731_);
lean_dec_ref(v_p_2730_);
return v___x_2732_;
}
else
{
lean_object* v___f_2736_; size_t v___x_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
v___f_2736_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2736_, 0, v_p_2730_);
v___x_2737_ = lean_usize_of_nat(v___x_2733_);
v___x_2738_ = ((size_t)0ULL);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2734_, v___f_2736_, v_xs_2731_, v___x_2737_, v___x_2738_, v___x_2732_);
return v___x_2739_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP(lean_object* v_00_u03b1_2740_, lean_object* v_n_2741_, lean_object* v_p_2742_, lean_object* v_xs_2743_){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2744_ = lean_unsigned_to_nat(0u);
v___x_2745_ = lean_array_get_size(v_xs_2743_);
v___x_2746_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2747_ = lean_nat_dec_lt(v___x_2744_, v___x_2745_);
if (v___x_2747_ == 0)
{
lean_dec_ref(v_xs_2743_);
lean_dec_ref(v_p_2742_);
return v___x_2744_;
}
else
{
lean_object* v___f_2748_; size_t v___x_2749_; size_t v___x_2750_; lean_object* v___x_2751_; 
v___f_2748_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2748_, 0, v_p_2742_);
v___x_2749_ = lean_usize_of_nat(v___x_2745_);
v___x_2750_ = ((size_t)0ULL);
v___x_2751_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2746_, v___f_2748_, v_xs_2743_, v___x_2749_, v___x_2750_, v___x_2744_);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___boxed(lean_object* v_00_u03b1_2752_, lean_object* v_n_2753_, lean_object* v_p_2754_, lean_object* v_xs_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Vector_countP(v_00_u03b1_2752_, v_n_2753_, v_p_2754_, v_xs_2755_);
lean_dec(v_n_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0(lean_object* v_inst_2757_, lean_object* v_a_2758_, lean_object* v_x1_2759_, lean_object* v_x2_2760_){
_start:
{
lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = lean_apply_2(v_inst_2757_, v_x1_2759_, v_a_2758_);
v___x_2762_ = lean_unbox(v___x_2761_);
if (v___x_2762_ == 0)
{
lean_inc(v_x2_2760_);
return v_x2_2760_;
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = lean_unsigned_to_nat(1u);
v___x_2764_ = lean_nat_add(v_x2_2760_, v___x_2763_);
return v___x_2764_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0___boxed(lean_object* v_inst_2765_, lean_object* v_a_2766_, lean_object* v_x1_2767_, lean_object* v_x2_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Vector_count___redArg___lam__0(v_inst_2765_, v_a_2766_, v_x1_2767_, v_x2_2768_);
lean_dec(v_x2_2768_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg(lean_object* v_inst_2770_, lean_object* v_a_2771_, lean_object* v_xs_2772_){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v___x_2773_ = lean_unsigned_to_nat(0u);
v___x_2774_ = lean_array_get_size(v_xs_2772_);
v___x_2775_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2776_ = lean_nat_dec_lt(v___x_2773_, v___x_2774_);
if (v___x_2776_ == 0)
{
lean_dec_ref(v_xs_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_inst_2770_);
return v___x_2773_;
}
else
{
lean_object* v___f_2777_; size_t v___x_2778_; size_t v___x_2779_; lean_object* v___x_2780_; 
v___f_2777_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2777_, 0, v_inst_2770_);
lean_closure_set(v___f_2777_, 1, v_a_2771_);
v___x_2778_ = lean_usize_of_nat(v___x_2774_);
v___x_2779_ = ((size_t)0ULL);
v___x_2780_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2775_, v___f_2777_, v_xs_2772_, v___x_2778_, v___x_2779_, v___x_2773_);
return v___x_2780_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count(lean_object* v_00_u03b1_2781_, lean_object* v_n_2782_, lean_object* v_inst_2783_, lean_object* v_a_2784_, lean_object* v_xs_2785_){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2786_ = lean_unsigned_to_nat(0u);
v___x_2787_ = lean_array_get_size(v_xs_2785_);
v___x_2788_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2789_ = lean_nat_dec_lt(v___x_2786_, v___x_2787_);
if (v___x_2789_ == 0)
{
lean_dec_ref(v_xs_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_inst_2783_);
return v___x_2786_;
}
else
{
lean_object* v___f_2790_; size_t v___x_2791_; size_t v___x_2792_; lean_object* v___x_2793_; 
v___f_2790_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2790_, 0, v_inst_2783_);
lean_closure_set(v___f_2790_, 1, v_a_2784_);
v___x_2791_ = lean_usize_of_nat(v___x_2787_);
v___x_2792_ = ((size_t)0ULL);
v___x_2793_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2788_, v___f_2790_, v_xs_2785_, v___x_2791_, v___x_2792_, v___x_2786_);
return v___x_2793_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___boxed(lean_object* v_00_u03b1_2794_, lean_object* v_n_2795_, lean_object* v_inst_2796_, lean_object* v_a_2797_, lean_object* v_xs_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Vector_count(v_00_u03b1_2794_, v_n_2795_, v_inst_2796_, v_a_2797_, v_xs_2798_);
lean_dec(v_n_2795_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___redArg(lean_object* v_inst_2800_, lean_object* v_xs_2801_, lean_object* v_a_2802_, lean_object* v_b_2803_){
_start:
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Array_replace___redArg(v_inst_2800_, v_xs_2801_, v_a_2802_, v_b_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace(lean_object* v_00_u03b1_2805_, lean_object* v_n_2806_, lean_object* v_inst_2807_, lean_object* v_xs_2808_, lean_object* v_a_2809_, lean_object* v_b_2810_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Array_replace___redArg(v_inst_2807_, v_xs_2808_, v_a_2809_, v_b_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___boxed(lean_object* v_00_u03b1_2812_, lean_object* v_n_2813_, lean_object* v_inst_2814_, lean_object* v_xs_2815_, lean_object* v_a_2816_, lean_object* v_b_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Vector_replace(v_00_u03b1_2812_, v_n_2813_, v_inst_2814_, v_xs_2815_, v_a_2816_, v_b_2817_);
lean_dec(v_n_2813_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg___lam__0(lean_object* v_inst_2819_, lean_object* v_x1_2820_, lean_object* v_x2_2821_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = lean_apply_2(v_inst_2819_, v_x1_2820_, v_x2_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg(lean_object* v_inst_2823_, lean_object* v_inst_2824_, lean_object* v_xs_2825_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; 
v___x_2826_ = lean_array_get_size(v_xs_2825_);
v___x_2827_ = lean_unsigned_to_nat(0u);
v___x_2828_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2829_ = lean_nat_dec_lt(v___x_2827_, v___x_2826_);
if (v___x_2829_ == 0)
{
lean_dec_ref(v_xs_2825_);
lean_dec(v_inst_2823_);
return v_inst_2824_;
}
else
{
lean_object* v___f_2830_; size_t v___x_2831_; size_t v___x_2832_; lean_object* v___x_2833_; 
v___f_2830_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2830_, 0, v_inst_2823_);
v___x_2831_ = lean_usize_of_nat(v___x_2826_);
v___x_2832_ = ((size_t)0ULL);
v___x_2833_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2828_, v___f_2830_, v_xs_2825_, v___x_2831_, v___x_2832_, v_inst_2824_);
return v___x_2833_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum(lean_object* v_00_u03b1_2834_, lean_object* v_n_2835_, lean_object* v_inst_2836_, lean_object* v_inst_2837_, lean_object* v_xs_2838_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2839_ = lean_array_get_size(v_xs_2838_);
v___x_2840_ = lean_unsigned_to_nat(0u);
v___x_2841_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2842_ = lean_nat_dec_lt(v___x_2840_, v___x_2839_);
if (v___x_2842_ == 0)
{
lean_dec_ref(v_xs_2838_);
lean_dec(v_inst_2836_);
return v_inst_2837_;
}
else
{
lean_object* v___f_2843_; size_t v___x_2844_; size_t v___x_2845_; lean_object* v___x_2846_; 
v___f_2843_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2843_, 0, v_inst_2836_);
v___x_2844_ = lean_usize_of_nat(v___x_2839_);
v___x_2845_ = ((size_t)0ULL);
v___x_2846_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2841_, v___f_2843_, v_xs_2838_, v___x_2844_, v___x_2845_, v_inst_2837_);
return v___x_2846_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum___boxed(lean_object* v_00_u03b1_2847_, lean_object* v_n_2848_, lean_object* v_inst_2849_, lean_object* v_inst_2850_, lean_object* v_xs_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Vector_sum(v_00_u03b1_2847_, v_n_2848_, v_inst_2849_, v_inst_2850_, v_xs_2851_);
lean_dec(v_n_2848_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg(lean_object* v_m_2853_, lean_object* v_n_2854_, lean_object* v_a_2855_, lean_object* v_xs_2856_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2857_ = lean_nat_sub(v_n_2854_, v_m_2853_);
v___x_2858_ = lean_mk_array(v___x_2857_, v_a_2855_);
v___x_2859_ = l_Array_append___redArg(v___x_2858_, v_xs_2856_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg___boxed(lean_object* v_m_2860_, lean_object* v_n_2861_, lean_object* v_a_2862_, lean_object* v_xs_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Vector_leftpad___redArg(v_m_2860_, v_n_2861_, v_a_2862_, v_xs_2863_);
lean_dec_ref(v_xs_2863_);
lean_dec(v_n_2861_);
lean_dec(v_m_2860_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad(lean_object* v_00_u03b1_2865_, lean_object* v_m_2866_, lean_object* v_n_2867_, lean_object* v_a_2868_, lean_object* v_xs_2869_){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2870_ = lean_nat_sub(v_n_2867_, v_m_2866_);
v___x_2871_ = lean_mk_array(v___x_2870_, v_a_2868_);
v___x_2872_ = l_Array_append___redArg(v___x_2871_, v_xs_2869_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___boxed(lean_object* v_00_u03b1_2873_, lean_object* v_m_2874_, lean_object* v_n_2875_, lean_object* v_a_2876_, lean_object* v_xs_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Vector_leftpad(v_00_u03b1_2873_, v_m_2874_, v_n_2875_, v_a_2876_, v_xs_2877_);
lean_dec_ref(v_xs_2877_);
lean_dec(v_n_2875_);
lean_dec(v_m_2874_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg(lean_object* v_m_2879_, lean_object* v_n_2880_, lean_object* v_a_2881_, lean_object* v_xs_2882_){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2883_ = lean_nat_sub(v_n_2880_, v_m_2879_);
v___x_2884_ = lean_mk_array(v___x_2883_, v_a_2881_);
v___x_2885_ = l_Array_append___redArg(v_xs_2882_, v___x_2884_);
lean_dec_ref(v___x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg___boxed(lean_object* v_m_2886_, lean_object* v_n_2887_, lean_object* v_a_2888_, lean_object* v_xs_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Vector_rightpad___redArg(v_m_2886_, v_n_2887_, v_a_2888_, v_xs_2889_);
lean_dec(v_n_2887_);
lean_dec(v_m_2886_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad(lean_object* v_00_u03b1_2891_, lean_object* v_m_2892_, lean_object* v_n_2893_, lean_object* v_a_2894_, lean_object* v_xs_2895_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = lean_nat_sub(v_n_2893_, v_m_2892_);
v___x_2897_ = lean_mk_array(v___x_2896_, v_a_2894_);
v___x_2898_ = l_Array_append___redArg(v_xs_2895_, v___x_2897_);
lean_dec_ref(v___x_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___boxed(lean_object* v_00_u03b1_2899_, lean_object* v_m_2900_, lean_object* v_n_2901_, lean_object* v_a_2902_, lean_object* v_xs_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Vector_rightpad(v_00_u03b1_2899_, v_m_2900_, v_n_2901_, v_a_2902_, v_xs_2903_);
lean_dec(v_n_2901_);
lean_dec(v_m_2900_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_f_2905_, lean_object* v_a_2906_, lean_object* v_h_2907_, lean_object* v_b_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_apply_3(v_f_2905_, v_a_2906_, lean_box(0), v_b_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_inst_2910_, lean_object* v_00_u03b2_2911_, lean_object* v_xs_2912_, lean_object* v_b_2913_, lean_object* v_f_2914_){
_start:
{
lean_object* v___f_2915_; size_t v_sz_2916_; size_t v___x_2917_; lean_object* v___x_2918_; 
v___f_2915_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2915_, 0, v_f_2914_);
v_sz_2916_ = lean_array_size(v_xs_2912_);
v___x_2917_ = ((size_t)0ULL);
v___x_2918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2910_, v_xs_2912_, v___f_2915_, v_sz_2916_, v___x_2917_, v_b_2913_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_2919_){
_start:
{
lean_object* v___f_2920_; 
v___f_2920_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2920_, 0, v_inst_2919_);
return v___f_2920_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_2921_, lean_object* v_00_u03b1_2922_, lean_object* v_n_2923_, lean_object* v_inst_2924_){
_start:
{
lean_object* v___f_2925_; 
v___f_2925_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2925_, 0, v_inst_2924_);
return v___f_2925_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(lean_object* v_m_2926_, lean_object* v_00_u03b1_2927_, lean_object* v_n_2928_, lean_object* v_inst_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Vector_instForIn_x27InferInstanceMembershipOfMonad(v_m_2926_, v_00_u03b1_2927_, v_n_2928_, v_inst_2929_);
lean_dec(v_n_2928_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad___redArg(lean_object* v_n_2931_, lean_object* v_inst_2932_){
_start:
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2933_, 0, lean_box(0));
lean_closure_set(v___x_2933_, 1, lean_box(0));
lean_closure_set(v___x_2933_, 2, v_n_2931_);
lean_closure_set(v___x_2933_, 3, v_inst_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad(lean_object* v_m_2934_, lean_object* v_00_u03b1_2935_, lean_object* v_n_2936_, lean_object* v_inst_2937_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2938_, 0, lean_box(0));
lean_closure_set(v___x_2938_, 1, lean_box(0));
lean_closure_set(v___x_2938_, 2, v_n_2936_);
lean_closure_set(v___x_2938_, 3, v_inst_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object* v_00_u03b1_2939_, lean_object* v_n_2940_, lean_object* v_inst_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_box(0);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object* v_00_u03b1_2943_, lean_object* v_n_2944_, lean_object* v_inst_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Vector_instLT(v_00_u03b1_2943_, v_n_2944_, v_inst_2945_);
lean_dec(v_n_2944_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE(lean_object* v_00_u03b1_2947_, lean_object* v_n_2948_, lean_object* v_inst_2949_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_box(0);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___boxed(lean_object* v_00_u03b1_2951_, lean_object* v_n_2952_, lean_object* v_inst_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Vector_instLE(v_00_u03b1_2951_, v_n_2952_, v_inst_2953_);
lean_dec(v_n_2952_);
return v_res_2954_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__2(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = ((lean_object*)(l_Vector_lex___auto__1___closed__0));
v___x_2962_ = l_Lean_mkAtom(v___x_2961_);
return v___x_2962_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__3(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_obj_once(&l_Vector_lex___auto__1___closed__2, &l_Vector_lex___auto__1___closed__2_once, _init_l_Vector_lex___auto__1___closed__2);
v___x_2964_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_2965_ = lean_array_push(v___x_2964_, v___x_2963_);
return v___x_2965_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_2979_ = l_Lean_mkAtom(v___x_2978_);
return v___x_2979_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2980_ = lean_obj_once(&l_Vector_lex___auto__1___closed__8, &l_Vector_lex___auto__1___closed__8_once, _init_l_Vector_lex___auto__1___closed__8);
v___x_2981_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_2982_ = lean_array_push(v___x_2981_, v___x_2980_);
return v___x_2982_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_2988_ = lean_string_utf8_byte_size(v___x_2987_);
return v___x_2988_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2989_ = lean_obj_once(&l_Vector_lex___auto__1___closed__13, &l_Vector_lex___auto__1___closed__13_once, _init_l_Vector_lex___auto__1___closed__13);
v___x_2990_ = lean_unsigned_to_nat(0u);
v___x_2991_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_2992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
lean_ctor_set(v___x_2992_, 1, v___x_2990_);
lean_ctor_set(v___x_2992_, 2, v___x_2989_);
return v___x_2992_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_box(0);
v___x_2995_ = lean_obj_once(&l_Vector_lex___auto__1___closed__14, &l_Vector_lex___auto__1___closed__14_once, _init_l_Vector_lex___auto__1___closed__14);
v___x_2996_ = lean_box(2);
v___x_2997_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
lean_ctor_set(v___x_2997_, 1, v___x_2995_);
lean_ctor_set(v___x_2997_, 2, v___x_2994_);
lean_ctor_set(v___x_2997_, 3, v___x_2993_);
return v___x_2997_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2998_ = lean_obj_once(&l_Vector_lex___auto__1___closed__15, &l_Vector_lex___auto__1___closed__15_once, _init_l_Vector_lex___auto__1___closed__15);
v___x_2999_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3000_ = lean_array_push(v___x_2999_, v___x_2998_);
return v___x_3000_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3001_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_3002_ = ((lean_object*)(l_Vector_lex___auto__1___closed__11));
v___x_3003_ = lean_box(2);
v___x_3004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
lean_ctor_set(v___x_3004_, 1, v___x_3002_);
lean_ctor_set(v___x_3004_, 2, v___x_3001_);
return v___x_3004_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3006_ = lean_obj_once(&l_Vector_lex___auto__1___closed__9, &l_Vector_lex___auto__1___closed__9_once, _init_l_Vector_lex___auto__1___closed__9);
v___x_3007_ = lean_array_push(v___x_3006_, v___x_3005_);
return v___x_3007_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3008_ = lean_obj_once(&l_Vector_lex___auto__1___closed__18, &l_Vector_lex___auto__1___closed__18_once, _init_l_Vector_lex___auto__1___closed__18);
v___x_3009_ = ((lean_object*)(l_Vector_lex___auto__1___closed__7));
v___x_3010_ = lean_box(2);
v___x_3011_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___x_3009_);
lean_ctor_set(v___x_3011_, 2, v___x_3008_);
return v___x_3011_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_obj_once(&l_Vector_lex___auto__1___closed__19, &l_Vector_lex___auto__1___closed__19_once, _init_l_Vector_lex___auto__1___closed__19);
v___x_3013_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3014_ = lean_array_push(v___x_3013_, v___x_3012_);
return v___x_3014_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = ((lean_object*)(l_Vector_lex___auto__1___closed__25));
v___x_3026_ = l_Lean_mkAtom(v___x_3025_);
return v___x_3026_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = lean_obj_once(&l_Vector_lex___auto__1___closed__26, &l_Vector_lex___auto__1___closed__26_once, _init_l_Vector_lex___auto__1___closed__26);
v___x_3028_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3029_ = lean_array_push(v___x_3028_, v___x_3027_);
return v___x_3029_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3031_ = lean_obj_once(&l_Vector_lex___auto__1___closed__27, &l_Vector_lex___auto__1___closed__27_once, _init_l_Vector_lex___auto__1___closed__27);
v___x_3032_ = lean_array_push(v___x_3031_, v___x_3030_);
return v___x_3032_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3033_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3034_ = ((lean_object*)(l_Vector_lex___auto__1___closed__24));
v___x_3035_ = lean_box(2);
v___x_3036_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
lean_ctor_set(v___x_3036_, 1, v___x_3034_);
lean_ctor_set(v___x_3036_, 2, v___x_3033_);
return v___x_3036_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3037_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3038_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3039_ = lean_array_push(v___x_3038_, v___x_3037_);
return v___x_3039_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = ((lean_object*)(l_Vector_lex___auto__1___closed__31));
v___x_3042_ = l_Lean_mkAtom(v___x_3041_);
return v___x_3042_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__33(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = lean_obj_once(&l_Vector_lex___auto__1___closed__32, &l_Vector_lex___auto__1___closed__32_once, _init_l_Vector_lex___auto__1___closed__32);
v___x_3044_ = lean_obj_once(&l_Vector_lex___auto__1___closed__30, &l_Vector_lex___auto__1___closed__30_once, _init_l_Vector_lex___auto__1___closed__30);
v___x_3045_ = lean_array_push(v___x_3044_, v___x_3043_);
return v___x_3045_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__34(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3047_ = lean_obj_once(&l_Vector_lex___auto__1___closed__33, &l_Vector_lex___auto__1___closed__33_once, _init_l_Vector_lex___auto__1___closed__33);
v___x_3048_ = lean_array_push(v___x_3047_, v___x_3046_);
return v___x_3048_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__35(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3049_ = lean_obj_once(&l_Vector_lex___auto__1___closed__34, &l_Vector_lex___auto__1___closed__34_once, _init_l_Vector_lex___auto__1___closed__34);
v___x_3050_ = ((lean_object*)(l_Vector_lex___auto__1___closed__22));
v___x_3051_ = lean_box(2);
v___x_3052_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
lean_ctor_set(v___x_3052_, 1, v___x_3050_);
lean_ctor_set(v___x_3052_, 2, v___x_3049_);
return v___x_3052_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__36(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = lean_obj_once(&l_Vector_lex___auto__1___closed__35, &l_Vector_lex___auto__1___closed__35_once, _init_l_Vector_lex___auto__1___closed__35);
v___x_3054_ = lean_obj_once(&l_Vector_lex___auto__1___closed__20, &l_Vector_lex___auto__1___closed__20_once, _init_l_Vector_lex___auto__1___closed__20);
v___x_3055_ = lean_array_push(v___x_3054_, v___x_3053_);
return v___x_3055_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_3057_ = l_Lean_mkAtom(v___x_3056_);
return v___x_3057_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = lean_obj_once(&l_Vector_lex___auto__1___closed__37, &l_Vector_lex___auto__1___closed__37_once, _init_l_Vector_lex___auto__1___closed__37);
v___x_3059_ = lean_obj_once(&l_Vector_lex___auto__1___closed__36, &l_Vector_lex___auto__1___closed__36_once, _init_l_Vector_lex___auto__1___closed__36);
v___x_3060_ = lean_array_push(v___x_3059_, v___x_3058_);
return v___x_3060_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3061_ = lean_obj_once(&l_Vector_lex___auto__1___closed__38, &l_Vector_lex___auto__1___closed__38_once, _init_l_Vector_lex___auto__1___closed__38);
v___x_3062_ = ((lean_object*)(l_Vector_lex___auto__1___closed__5));
v___x_3063_ = lean_box(2);
v___x_3064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
lean_ctor_set(v___x_3064_, 1, v___x_3062_);
lean_ctor_set(v___x_3064_, 2, v___x_3061_);
return v___x_3064_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = lean_obj_once(&l_Vector_lex___auto__1___closed__39, &l_Vector_lex___auto__1___closed__39_once, _init_l_Vector_lex___auto__1___closed__39);
v___x_3066_ = lean_obj_once(&l_Vector_lex___auto__1___closed__3, &l_Vector_lex___auto__1___closed__3_once, _init_l_Vector_lex___auto__1___closed__3);
v___x_3067_ = lean_array_push(v___x_3066_, v___x_3065_);
return v___x_3067_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3068_ = lean_obj_once(&l_Vector_lex___auto__1___closed__40, &l_Vector_lex___auto__1___closed__40_once, _init_l_Vector_lex___auto__1___closed__40);
v___x_3069_ = ((lean_object*)(l_Vector_lex___auto__1___closed__1));
v___x_3070_ = lean_box(2);
v___x_3071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v___x_3069_);
lean_ctor_set(v___x_3071_, 2, v___x_3068_);
return v___x_3071_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = lean_obj_once(&l_Vector_lex___auto__1___closed__41, &l_Vector_lex___auto__1___closed__41_once, _init_l_Vector_lex___auto__1___closed__41);
v___x_3073_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3074_ = lean_array_push(v___x_3073_, v___x_3072_);
return v___x_3074_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3075_ = lean_obj_once(&l_Vector_lex___auto__1___closed__42, &l_Vector_lex___auto__1___closed__42_once, _init_l_Vector_lex___auto__1___closed__42);
v___x_3076_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_3077_ = lean_box(2);
v___x_3078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v___x_3076_);
lean_ctor_set(v___x_3078_, 2, v___x_3075_);
return v___x_3078_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = lean_obj_once(&l_Vector_lex___auto__1___closed__43, &l_Vector_lex___auto__1___closed__43_once, _init_l_Vector_lex___auto__1___closed__43);
v___x_3080_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3081_ = lean_array_push(v___x_3080_, v___x_3079_);
return v___x_3081_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3082_ = lean_obj_once(&l_Vector_lex___auto__1___closed__44, &l_Vector_lex___auto__1___closed__44_once, _init_l_Vector_lex___auto__1___closed__44);
v___x_3083_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_3084_ = lean_box(2);
v___x_3085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set(v___x_3085_, 1, v___x_3083_);
lean_ctor_set(v___x_3085_, 2, v___x_3082_);
return v___x_3085_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_obj_once(&l_Vector_lex___auto__1___closed__45, &l_Vector_lex___auto__1___closed__45_once, _init_l_Vector_lex___auto__1___closed__45);
v___x_3087_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3088_ = lean_array_push(v___x_3087_, v___x_3086_);
return v___x_3088_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3089_ = lean_obj_once(&l_Vector_lex___auto__1___closed__46, &l_Vector_lex___auto__1___closed__46_once, _init_l_Vector_lex___auto__1___closed__46);
v___x_3090_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_3091_ = lean_box(2);
v___x_3092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v___x_3090_);
lean_ctor_set(v___x_3092_, 2, v___x_3089_);
return v___x_3092_;
}
}
static lean_object* _init_l_Vector_lex___auto__1(void){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = lean_obj_once(&l_Vector_lex___auto__1___closed__47, &l_Vector_lex___auto__1___closed__47_once, _init_l_Vector_lex___auto__1___closed__47);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0(lean_object* v_n_3094_, lean_object* v_xs_3095_, lean_object* v_ys_3096_, lean_object* v_lt_3097_, lean_object* v_inst_3098_, lean_object* v___x_3099_, lean_object* v___x_3100_, lean_object* v_next_3101_, lean_object* v_acc_3102_, lean_object* v_h_3103_, lean_object* v_G_3104_){
_start:
{
uint8_t v___x_3105_; 
v___x_3105_ = lean_nat_dec_lt(v_next_3101_, v_n_3094_);
if (v___x_3105_ == 0)
{
lean_dec_ref(v_G_3104_);
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_inst_3098_);
lean_dec_ref(v_lt_3097_);
lean_inc_ref(v_acc_3102_);
return v_acc_3102_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3106_ = lean_array_fget_borrowed(v_xs_3095_, v_next_3101_);
v___x_3107_ = lean_array_fget_borrowed(v_ys_3096_, v_next_3101_);
lean_inc(v___x_3107_);
lean_inc(v___x_3106_);
v___x_3108_ = lean_apply_2(v_lt_3097_, v___x_3106_, v___x_3107_);
v___x_3109_ = lean_unbox(v___x_3108_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; uint8_t v___x_3111_; 
lean_inc(v___x_3107_);
lean_inc(v___x_3106_);
v___x_3110_ = lean_apply_2(v_inst_3098_, v___x_3106_, v___x_3107_);
v___x_3111_ = lean_unbox(v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_dec_ref(v_G_3104_);
lean_dec_ref(v___x_3100_);
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3108_);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
lean_ctor_set(v___x_3113_, 1, v___x_3099_);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = lean_unsigned_to_nat(1u);
v___x_3115_ = lean_nat_add(v_next_3101_, v___x_3114_);
v___x_3116_ = lean_apply_4(v_G_3104_, v___x_3115_, v___x_3100_, lean_box(0), lean_box(0));
return v___x_3116_;
}
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_dec_ref(v_G_3104_);
lean_dec_ref(v___x_3100_);
lean_dec_ref(v_inst_3098_);
v___x_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3108_);
v___x_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
lean_ctor_set(v___x_3118_, 1, v___x_3099_);
return v___x_3118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0___boxed(lean_object* v_n_3119_, lean_object* v_xs_3120_, lean_object* v_ys_3121_, lean_object* v_lt_3122_, lean_object* v_inst_3123_, lean_object* v___x_3124_, lean_object* v___x_3125_, lean_object* v_next_3126_, lean_object* v_acc_3127_, lean_object* v_h_3128_, lean_object* v_G_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Vector_lex___redArg___lam__0(v_n_3119_, v_xs_3120_, v_ys_3121_, v_lt_3122_, v_inst_3123_, v___x_3124_, v___x_3125_, v_next_3126_, v_acc_3127_, v_h_3128_, v_G_3129_);
lean_dec_ref(v_acc_3127_);
lean_dec(v_next_3126_);
lean_dec_ref(v_ys_3121_);
lean_dec_ref(v_xs_3120_);
lean_dec(v_n_3119_);
return v_res_3130_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object* v_n_3134_, lean_object* v_inst_3135_, lean_object* v_xs_3136_, lean_object* v_ys_3137_, lean_object* v_lt_3138_){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___f_3142_; lean_object* v___x_3143_; lean_object* v_fst_3144_; 
v___x_3139_ = lean_unsigned_to_nat(0u);
v___x_3140_ = lean_box(0);
v___x_3141_ = ((lean_object*)(l_Vector_lex___redArg___closed__0));
v___f_3142_ = lean_alloc_closure((void*)(l_Vector_lex___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_3142_, 0, v_n_3134_);
lean_closure_set(v___f_3142_, 1, v_xs_3136_);
lean_closure_set(v___f_3142_, 2, v_ys_3137_);
lean_closure_set(v___f_3142_, 3, v_lt_3138_);
lean_closure_set(v___f_3142_, 4, v_inst_3135_);
lean_closure_set(v___f_3142_, 5, v___x_3140_);
lean_closure_set(v___f_3142_, 6, v___x_3141_);
v___x_3143_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3142_, v___x_3139_, v___x_3141_, lean_box(0));
v_fst_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_fst_3144_);
lean_dec(v___x_3143_);
if (lean_obj_tag(v_fst_3144_) == 0)
{
uint8_t v___x_3145_; 
v___x_3145_ = 0;
return v___x_3145_;
}
else
{
lean_object* v_val_3146_; uint8_t v___x_3147_; 
v_val_3146_ = lean_ctor_get(v_fst_3144_, 0);
lean_inc(v_val_3146_);
lean_dec_ref(v_fst_3144_);
v___x_3147_ = lean_unbox(v_val_3146_);
lean_dec(v_val_3146_);
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object* v_n_3148_, lean_object* v_inst_3149_, lean_object* v_xs_3150_, lean_object* v_ys_3151_, lean_object* v_lt_3152_){
_start:
{
uint8_t v_res_3153_; lean_object* v_r_3154_; 
v_res_3153_ = l_Vector_lex___redArg(v_n_3148_, v_inst_3149_, v_xs_3150_, v_ys_3151_, v_lt_3152_);
v_r_3154_ = lean_box(v_res_3153_);
return v_r_3154_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex(lean_object* v_00_u03b1_3155_, lean_object* v_n_3156_, lean_object* v_inst_3157_, lean_object* v_xs_3158_, lean_object* v_ys_3159_, lean_object* v_lt_3160_){
_start:
{
uint8_t v___x_3161_; 
v___x_3161_ = l_Vector_lex___redArg(v_n_3156_, v_inst_3157_, v_xs_3158_, v_ys_3159_, v_lt_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object* v_00_u03b1_3162_, lean_object* v_n_3163_, lean_object* v_inst_3164_, lean_object* v_xs_3165_, lean_object* v_ys_3166_, lean_object* v_lt_3167_){
_start:
{
uint8_t v_res_3168_; lean_object* v_r_3169_; 
v_res_3168_ = l_Vector_lex(v_00_u03b1_3162_, v_n_3163_, v_inst_3164_, v_xs_3165_, v_ys_3166_, v_lt_3167_);
v_r_3169_ = lean_box(v_res_3168_);
return v_r_3169_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
