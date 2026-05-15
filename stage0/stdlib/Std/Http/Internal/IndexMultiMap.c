// Lean compiler output
// Module: Std.Http.Internal.IndexMultiMap
// Imports: public import Init.Grind public import Init.Data.Int.OfNat public import Std.Data.HashMap
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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l_instReprNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entries"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instRepr___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value)} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "indexes"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprTupleOfRepr___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17_value)} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashMap.ofList "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "validity"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36_value)} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37_value;
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Internal_instInhabitedIndexMultiMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_instInhabitedIndexMultiMap___closed__0 = (const lean_object*)&l_Std_Internal_instInhabitedIndexMultiMap___closed__0_value;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___closed__1;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___closed__2;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0_value;
static const lean_string_object l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1 = (const lean_object*)&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1_value;
static const lean_string_object l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2 = (const lean_object*)&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__0(lean_object* v_a_1_, lean_object* v_b_2_, lean_object* v_d_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_a_1_);
lean_ctor_set(v___x_4_, 1, v_b_2_);
v___x_5_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v_d_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__1(lean_object* v___x_6_, lean_object* v___f_7_, lean_object* v_l_8_, lean_object* v_acc_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_6_, v___f_7_, v_acc_9_, v_l_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(11u);
v___x_47_ = lean_nat_to_int(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18));
v___x_67_ = lean_string_length(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32, &l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32);
v___x_69_ = lean_nat_to_int(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg(lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_x_80_){
_start:
{
lean_object* v_entries_81_; lean_object* v_indexes_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_147_; 
v_entries_81_ = lean_ctor_get(v_x_80_, 0);
v_indexes_82_ = lean_ctor_get(v_x_80_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_147_ == 0)
{
v___x_84_ = v_x_80_;
v_isShared_85_ = v_isSharedCheck_147_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_indexes_82_);
lean_inc(v_entries_81_);
lean_dec(v_x_80_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_147_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v_buckets_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_145_; 
v___x_86_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_buckets_87_ = lean_ctor_get(v_indexes_82_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_indexes_82_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v_indexes_82_, 0);
lean_dec(v_unused_146_);
v___x_89_ = v_indexes_82_;
v_isShared_90_ = v_isSharedCheck_145_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_buckets_87_);
lean_dec(v_indexes_82_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_145_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_91_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14));
v___x_92_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15));
v___f_93_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_93_, 0, v_inst_79_);
lean_inc_ref(v_inst_78_);
v___x_94_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_94_, 0, lean_box(0));
lean_closure_set(v___x_94_, 1, lean_box(0));
lean_closure_set(v___x_94_, 2, v_inst_78_);
lean_closure_set(v___x_94_, 3, v___f_93_);
v___x_95_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19, &l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19);
v___x_96_ = l_Array_repr___redArg(v___x_94_, v_entries_81_);
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 4);
lean_ctor_set(v___x_89_, 1, v___x_96_);
lean_ctor_set(v___x_89_, 0, v___x_95_);
v___x_98_ = v___x_89_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_144_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_99_ = 0;
v___x_100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_99_);
if (v_isShared_85_ == 0)
{
lean_ctor_set_tag(v___x_84_, 5);
lean_ctor_set(v___x_84_, 1, v___x_100_);
lean_ctor_set(v___x_84_, 0, v___x_92_);
v___x_102_ = v___x_84_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_100_);
v___x_102_ = v_reuseFailAlloc_143_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___f_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___y_115_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_103_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21));
v___x_104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_box(1);
v___x_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23));
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_91_);
v___f_110_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24));
v___x_111_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_111_, 0, lean_box(0));
lean_closure_set(v___x_111_, 1, lean_box(0));
lean_closure_set(v___x_111_, 2, v_inst_78_);
lean_closure_set(v___x_111_, 3, v___f_110_);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26));
v___x_136_ = lean_box(0);
v___x_137_ = lean_array_get_size(v_buckets_87_);
v___x_138_ = lean_nat_dec_lt(v___x_112_, v___x_137_);
if (v___x_138_ == 0)
{
lean_dec_ref(v_buckets_87_);
v___y_115_ = v___x_136_;
goto v___jp_114_;
}
else
{
lean_object* v___f_139_; size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; 
v___f_139_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37));
v___x_140_ = lean_usize_of_nat(v___x_137_);
v___x_141_ = ((size_t)0ULL);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_86_, v___f_139_, v_buckets_87_, v___x_140_, v___x_141_, v___x_136_);
v___y_115_ = v___x_142_;
goto v___jp_114_;
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_116_ = l_List_repr___redArg(v___x_111_, v___y_115_);
v___x_117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_113_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = l_Repr_addAppParen(v___x_117_, v___x_112_);
v___x_119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_95_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_99_);
v___x_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_109_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_103_);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_105_);
v___x_124_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28));
v___x_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_91_);
v___x_127_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30));
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33, &l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33);
v___x_130_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34));
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_128_);
v___x_132_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35));
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_129_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v___x_99_);
return v___x_135_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_x_154_, lean_object* v_prec_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg(v_inst_152_, v_inst_153_, v_x_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___boxed(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_x_163_, lean_object* v_prec_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Std_Internal_instReprIndexMultiMap_repr(v_00_u03b1_157_, v_00_u03b2_158_, v_inst_159_, v_inst_160_, v_inst_161_, v_inst_162_, v_x_163_, v_prec_164_);
lean_dec(v_prec_164_);
lean_dec_ref(v_inst_160_);
lean_dec_ref(v_inst_159_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap___redArg(lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_alloc_closure((void*)(l_Std_Internal_instReprIndexMultiMap_repr___boxed), 8, 6);
lean_closure_set(v___x_170_, 0, lean_box(0));
lean_closure_set(v___x_170_, 1, lean_box(0));
lean_closure_set(v___x_170_, 2, v_inst_166_);
lean_closure_set(v___x_170_, 3, v_inst_167_);
lean_closure_set(v___x_170_, 4, v_inst_168_);
lean_closure_set(v___x_170_, 5, v_inst_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap(lean_object* v_00_u03b1_171_, lean_object* v_00_u03b2_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_closure((void*)(l_Std_Internal_instReprIndexMultiMap_repr___boxed), 8, 6);
lean_closure_set(v___x_177_, 0, lean_box(0));
lean_closure_set(v___x_177_, 1, lean_box(0));
lean_closure_set(v___x_177_, 2, v_inst_173_);
lean_closure_set(v___x_177_, 3, v_inst_174_);
lean_closure_set(v___x_177_, 4, v_inst_175_);
lean_closure_set(v___x_177_, 5, v_inst_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__1(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_unsigned_to_nat(16u);
v___x_182_ = lean_mk_array(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__2(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__1, &l_Std_Internal_instInhabitedIndexMultiMap___closed__1_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__1);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__2, &l_Std_Internal_instInhabitedIndexMultiMap___closed__2_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__2);
v___x_187_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___closed__0));
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap(lean_object* v_00_u03b1_189_, lean_object* v_00_u03b2_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_inst_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___boxed(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Internal_instInhabitedIndexMultiMap(v_00_u03b1_196_, v_00_u03b2_197_, v_inst_198_, v_inst_199_, v_inst_200_, v_inst_201_);
lean_dec(v_inst_201_);
lean_dec(v_inst_200_);
lean_dec_ref(v_inst_199_);
lean_dec_ref(v_inst_198_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_inst_205_, lean_object* v_inst_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(0);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___boxed(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_inst_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Std_Internal_IndexMultiMap_instMembership(v_00_u03b1_208_, v_00_u03b2_209_, v_inst_210_, v_inst_211_);
lean_dec_ref(v_inst_211_);
lean_dec_ref(v_inst_210_);
return v_res_212_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_key_215_, lean_object* v_map_216_){
_start:
{
lean_object* v_indexes_217_; uint8_t v___x_218_; 
v_indexes_217_ = lean_ctor_get(v_map_216_, 1);
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_213_, v_inst_214_, v_indexes_217_, v_key_215_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___redArg___boxed(lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_key_221_, lean_object* v_map_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_219_, v_inst_220_, v_key_221_, v_map_222_);
lean_dec_ref(v_map_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem(lean_object* v_00_u03b1_225_, lean_object* v_00_u03b2_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_key_229_, lean_object* v_map_230_){
_start:
{
uint8_t v___x_231_; 
v___x_231_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_227_, v_inst_228_, v_key_229_, v_map_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___boxed(lean_object* v_00_u03b1_232_, lean_object* v_00_u03b2_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_key_236_, lean_object* v_map_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Std_Internal_IndexMultiMap_instDecidableMem(v_00_u03b1_232_, v_00_u03b2_233_, v_inst_234_, v_inst_235_, v_key_236_, v_map_237_);
lean_dec_ref(v_map_237_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(lean_object* v___x_240_, lean_object* v_entries_241_, lean_object* v_x1_242_, lean_object* v_x2_243_, lean_object* v_x3_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_snd_247_; 
v___x_245_ = lean_array_fget_borrowed(v___x_240_, v_x1_242_);
v___x_246_ = lean_array_fget_borrowed(v_entries_241_, v___x_245_);
v_snd_247_ = lean_ctor_get(v___x_246_, 1);
lean_inc(v_snd_247_);
return v_snd_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed(lean_object* v___x_248_, lean_object* v_entries_249_, lean_object* v_x1_250_, lean_object* v_x2_251_, lean_object* v_x3_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(v___x_248_, v_entries_249_, v_x1_250_, v_x2_251_, v_x3_252_);
lean_dec(v_x2_251_);
lean_dec(v_x1_250_);
lean_dec_ref(v_entries_249_);
lean_dec_ref(v___x_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg(lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_map_256_, lean_object* v_key_257_){
_start:
{
lean_object* v_entries_258_; lean_object* v_indexes_259_; lean_object* v___x_260_; lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_entries_266_; 
v_entries_258_ = lean_ctor_get(v_map_256_, 0);
lean_inc_ref(v_entries_258_);
v_indexes_259_ = lean_ctor_get(v_map_256_, 1);
lean_inc_ref(v_indexes_259_);
lean_dec_ref(v_map_256_);
v___x_260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_254_, v_inst_255_, v_indexes_259_, v_key_257_);
lean_dec_ref(v_indexes_259_);
lean_inc(v___x_260_);
v___f_261_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_261_, 0, v___x_260_);
lean_closure_set(v___f_261_, 1, v_entries_258_);
v___x_262_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_263_ = lean_array_get_size(v___x_260_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_mk_empty_array_with_capacity(v___x_263_);
v_entries_266_ = l_Array_mapFinIdxM_map___redArg(v___x_262_, v___x_260_, v___f_261_, v___x_263_, v___x_264_, v___x_265_);
return v_entries_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll(lean_object* v_00_u03b1_267_, lean_object* v_00_u03b2_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_map_271_, lean_object* v_key_272_, lean_object* v_h_273_){
_start:
{
lean_object* v_entries_274_; lean_object* v_indexes_275_; lean_object* v___x_276_; lean_object* v___f_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_entries_282_; 
v_entries_274_ = lean_ctor_get(v_map_271_, 0);
lean_inc_ref(v_entries_274_);
v_indexes_275_ = lean_ctor_get(v_map_271_, 1);
lean_inc_ref(v_indexes_275_);
lean_dec_ref(v_map_271_);
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_269_, v_inst_270_, v_indexes_275_, v_key_272_);
lean_dec_ref(v_indexes_275_);
lean_inc(v___x_276_);
v___f_277_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_277_, 0, v___x_276_);
lean_closure_set(v___f_277_, 1, v_entries_274_);
v___x_278_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_279_ = lean_array_get_size(v___x_276_);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_mk_empty_array_with_capacity(v___x_279_);
v_entries_282_ = l_Array_mapFinIdxM_map___redArg(v___x_278_, v___x_276_, v___f_277_, v___x_279_, v___x_280_, v___x_281_);
return v_entries_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg(lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_map_285_, lean_object* v_key_286_){
_start:
{
lean_object* v_entries_287_; lean_object* v_indexes_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_entry_291_; lean_object* v___x_292_; lean_object* v_snd_293_; 
v_entries_287_ = lean_ctor_get(v_map_285_, 0);
v_indexes_288_ = lean_ctor_get(v_map_285_, 1);
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_283_, v_inst_284_, v_indexes_288_, v_key_286_);
v___x_290_ = lean_unsigned_to_nat(0u);
v_entry_291_ = lean_array_fget(v___x_289_, v___x_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_array_fget_borrowed(v_entries_287_, v_entry_291_);
lean_dec(v_entry_291_);
v_snd_293_ = lean_ctor_get(v___x_292_, 1);
lean_inc(v_snd_293_);
return v_snd_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg___boxed(lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_map_296_, lean_object* v_key_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Internal_IndexMultiMap_get___redArg(v_inst_294_, v_inst_295_, v_map_296_, v_key_297_);
lean_dec_ref(v_map_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get(lean_object* v_00_u03b1_299_, lean_object* v_00_u03b2_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_map_303_, lean_object* v_key_304_, lean_object* v_h_305_){
_start:
{
lean_object* v_entries_306_; lean_object* v_indexes_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_entry_310_; lean_object* v___x_311_; lean_object* v_snd_312_; 
v_entries_306_ = lean_ctor_get(v_map_303_, 0);
v_indexes_307_ = lean_ctor_get(v_map_303_, 1);
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_301_, v_inst_302_, v_indexes_307_, v_key_304_);
v___x_309_ = lean_unsigned_to_nat(0u);
v_entry_310_ = lean_array_fget(v___x_308_, v___x_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_array_fget_borrowed(v_entries_306_, v_entry_310_);
lean_dec(v_entry_310_);
v_snd_312_ = lean_ctor_get(v___x_311_, 1);
lean_inc(v_snd_312_);
return v_snd_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___boxed(lean_object* v_00_u03b1_313_, lean_object* v_00_u03b2_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_map_317_, lean_object* v_key_318_, lean_object* v_h_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_Internal_IndexMultiMap_get(v_00_u03b1_313_, v_00_u03b2_314_, v_inst_315_, v_inst_316_, v_map_317_, v_key_318_, v_h_319_);
lean_dec_ref(v_map_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f___redArg(lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_map_323_, lean_object* v_key_324_){
_start:
{
uint8_t v___x_325_; 
lean_inc(v_key_324_);
lean_inc_ref(v_inst_322_);
lean_inc_ref(v_inst_321_);
v___x_325_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_321_, v_inst_322_, v_key_324_, v_map_323_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v_key_324_);
lean_dec_ref(v_map_323_);
lean_dec_ref(v_inst_322_);
lean_dec_ref(v_inst_321_);
v___x_326_ = lean_box(0);
return v___x_326_;
}
else
{
lean_object* v_entries_327_; lean_object* v_indexes_328_; lean_object* v___x_329_; lean_object* v___f_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v_entries_335_; lean_object* v___x_336_; 
v_entries_327_ = lean_ctor_get(v_map_323_, 0);
lean_inc_ref(v_entries_327_);
v_indexes_328_ = lean_ctor_get(v_map_323_, 1);
lean_inc_ref(v_indexes_328_);
lean_dec_ref(v_map_323_);
v___x_329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_321_, v_inst_322_, v_indexes_328_, v_key_324_);
lean_dec_ref(v_indexes_328_);
lean_inc(v___x_329_);
v___f_330_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_330_, 0, v___x_329_);
lean_closure_set(v___f_330_, 1, v_entries_327_);
v___x_331_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_332_ = lean_array_get_size(v___x_329_);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_mk_empty_array_with_capacity(v___x_332_);
v_entries_335_ = l_Array_mapFinIdxM_map___redArg(v___x_331_, v___x_329_, v___f_330_, v___x_332_, v___x_333_, v___x_334_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v_entries_335_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f(lean_object* v_00_u03b1_337_, lean_object* v_00_u03b2_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_map_341_, lean_object* v_key_342_){
_start:
{
uint8_t v___x_343_; 
lean_inc(v_key_342_);
lean_inc_ref(v_inst_340_);
lean_inc_ref(v_inst_339_);
v___x_343_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_339_, v_inst_340_, v_key_342_, v_map_341_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_dec(v_key_342_);
lean_dec_ref(v_map_341_);
lean_dec_ref(v_inst_340_);
lean_dec_ref(v_inst_339_);
v___x_344_ = lean_box(0);
return v___x_344_;
}
else
{
lean_object* v_entries_345_; lean_object* v_indexes_346_; lean_object* v___x_347_; lean_object* v___f_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_entries_353_; lean_object* v___x_354_; 
v_entries_345_ = lean_ctor_get(v_map_341_, 0);
lean_inc_ref(v_entries_345_);
v_indexes_346_ = lean_ctor_get(v_map_341_, 1);
lean_inc_ref(v_indexes_346_);
lean_dec_ref(v_map_341_);
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_339_, v_inst_340_, v_indexes_346_, v_key_342_);
lean_dec_ref(v_indexes_346_);
lean_inc(v___x_347_);
v___f_348_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_348_, 0, v___x_347_);
lean_closure_set(v___f_348_, 1, v_entries_345_);
v___x_349_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_350_ = lean_array_get_size(v___x_347_);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_mk_empty_array_with_capacity(v___x_350_);
v_entries_353_ = l_Array_mapFinIdxM_map___redArg(v___x_349_, v___x_347_, v___f_348_, v___x_350_, v___x_351_, v___x_352_);
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v_entries_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg(lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_map_357_, lean_object* v_key_358_){
_start:
{
uint8_t v___x_359_; 
lean_inc(v_key_358_);
lean_inc_ref(v_inst_356_);
lean_inc_ref(v_inst_355_);
v___x_359_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_355_, v_inst_356_, v_key_358_, v_map_357_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
lean_dec(v_key_358_);
lean_dec_ref(v_inst_356_);
lean_dec_ref(v_inst_355_);
v___x_360_ = lean_box(0);
return v___x_360_;
}
else
{
lean_object* v_entries_361_; lean_object* v_indexes_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_entry_365_; lean_object* v___x_366_; lean_object* v_snd_367_; lean_object* v___x_368_; 
v_entries_361_ = lean_ctor_get(v_map_357_, 0);
v_indexes_362_ = lean_ctor_get(v_map_357_, 1);
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_355_, v_inst_356_, v_indexes_362_, v_key_358_);
v___x_364_ = lean_unsigned_to_nat(0u);
v_entry_365_ = lean_array_fget(v___x_363_, v___x_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_array_fget_borrowed(v_entries_361_, v_entry_365_);
lean_dec(v_entry_365_);
v_snd_367_ = lean_ctor_get(v___x_366_, 1);
lean_inc(v_snd_367_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v_snd_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg___boxed(lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_map_371_, lean_object* v_key_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_Internal_IndexMultiMap_get_x3f___redArg(v_inst_369_, v_inst_370_, v_map_371_, v_key_372_);
lean_dec_ref(v_map_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_map_378_, lean_object* v_key_379_){
_start:
{
uint8_t v___x_380_; 
lean_inc(v_key_379_);
lean_inc_ref(v_inst_377_);
lean_inc_ref(v_inst_376_);
v___x_380_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_376_, v_inst_377_, v_key_379_, v_map_378_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec(v_key_379_);
lean_dec_ref(v_inst_377_);
lean_dec_ref(v_inst_376_);
v___x_381_ = lean_box(0);
return v___x_381_;
}
else
{
lean_object* v_entries_382_; lean_object* v_indexes_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_entry_386_; lean_object* v___x_387_; lean_object* v_snd_388_; lean_object* v___x_389_; 
v_entries_382_ = lean_ctor_get(v_map_378_, 0);
v_indexes_383_ = lean_ctor_get(v_map_378_, 1);
v___x_384_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_376_, v_inst_377_, v_indexes_383_, v_key_379_);
v___x_385_ = lean_unsigned_to_nat(0u);
v_entry_386_ = lean_array_fget(v___x_384_, v___x_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_array_fget_borrowed(v_entries_382_, v_entry_386_);
lean_dec(v_entry_386_);
v_snd_388_ = lean_ctor_get(v___x_387_, 1);
lean_inc(v_snd_388_);
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v_snd_388_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___boxed(lean_object* v_00_u03b1_390_, lean_object* v_00_u03b2_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_map_394_, lean_object* v_key_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_Internal_IndexMultiMap_get_x3f(v_00_u03b1_390_, v_00_u03b2_391_, v_inst_392_, v_inst_393_, v_map_394_, v_key_395_);
lean_dec_ref(v_map_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(lean_object* v_inst_397_, lean_object* v_value_398_, lean_object* v___x_399_, lean_object* v___x_400_, lean_object* v_a_401_, lean_object* v_x_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
lean_inc(v_a_401_);
v___x_404_ = lean_apply_2(v_inst_397_, v_a_401_, v_value_398_);
v___x_405_ = lean_unbox(v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v_a_401_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_399_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec_ref(v___x_399_);
v___x_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_407_, 0, v_a_401_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_400_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed(lean_object* v_inst_411_, lean_object* v_value_412_, lean_object* v___x_413_, lean_object* v___x_414_, lean_object* v_a_415_, lean_object* v_x_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(v_inst_411_, v_value_412_, v___x_413_, v___x_414_, v_a_415_, v_x_416_, v___y_417_);
lean_dec_ref(v___y_417_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry___redArg(lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_map_424_, lean_object* v_inst_425_, lean_object* v_key_426_, lean_object* v_value_427_){
_start:
{
uint8_t v___x_428_; 
lean_inc(v_key_426_);
lean_inc_ref(v_inst_423_);
lean_inc_ref(v_inst_422_);
v___x_428_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_422_, v_inst_423_, v_key_426_, v_map_424_);
if (v___x_428_ == 0)
{
lean_dec(v_value_427_);
lean_dec(v_key_426_);
lean_dec_ref(v_inst_425_);
lean_dec_ref(v_map_424_);
lean_dec_ref(v_inst_423_);
lean_dec_ref(v_inst_422_);
return v___x_428_;
}
else
{
lean_object* v_entries_429_; lean_object* v_indexes_430_; lean_object* v___x_431_; lean_object* v___f_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_entries_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___f_440_; size_t v_sz_441_; size_t v___x_442_; lean_object* v___x_443_; lean_object* v_fst_444_; 
v_entries_429_ = lean_ctor_get(v_map_424_, 0);
lean_inc_ref(v_entries_429_);
v_indexes_430_ = lean_ctor_get(v_map_424_, 1);
lean_inc_ref(v_indexes_430_);
lean_dec_ref(v_map_424_);
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_422_, v_inst_423_, v_indexes_430_, v_key_426_);
lean_dec_ref(v_indexes_430_);
lean_inc(v___x_431_);
v___f_432_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_432_, 0, v___x_431_);
lean_closure_set(v___f_432_, 1, v_entries_429_);
v___x_433_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_434_ = lean_array_get_size(v___x_431_);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_mk_empty_array_with_capacity(v___x_434_);
v_entries_437_ = l_Array_mapFinIdxM_map___redArg(v___x_433_, v___x_431_, v___f_432_, v___x_434_, v___x_435_, v___x_436_);
v___x_438_ = lean_box(0);
v___x_439_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_440_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_440_, 0, v_inst_425_);
lean_closure_set(v___f_440_, 1, v_value_427_);
lean_closure_set(v___f_440_, 2, v___x_439_);
lean_closure_set(v___f_440_, 3, v___x_438_);
v_sz_441_ = lean_array_size(v_entries_437_);
v___x_442_ = ((size_t)0ULL);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_433_, v_entries_437_, v___f_440_, v_sz_441_, v___x_442_, v___x_439_);
v_fst_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_fst_444_);
lean_dec(v___x_443_);
if (lean_obj_tag(v_fst_444_) == 0)
{
uint8_t v___x_445_; 
v___x_445_ = 0;
return v___x_445_;
}
else
{
lean_object* v_val_446_; 
v_val_446_ = lean_ctor_get(v_fst_444_, 0);
lean_inc(v_val_446_);
lean_dec_ref(v_fst_444_);
if (lean_obj_tag(v_val_446_) == 0)
{
uint8_t v___x_447_; 
v___x_447_ = 0;
return v___x_447_;
}
else
{
lean_dec_ref(v_val_446_);
return v___x_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___boxed(lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_map_450_, lean_object* v_inst_451_, lean_object* v_key_452_, lean_object* v_value_453_){
_start:
{
uint8_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg(v_inst_448_, v_inst_449_, v_map_450_, v_inst_451_, v_key_452_, v_value_453_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry(lean_object* v_00_u03b1_456_, lean_object* v_00_u03b2_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_map_460_, lean_object* v_inst_461_, lean_object* v_key_462_, lean_object* v_value_463_){
_start:
{
uint8_t v___x_464_; 
lean_inc(v_key_462_);
lean_inc_ref(v_inst_459_);
lean_inc_ref(v_inst_458_);
v___x_464_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_458_, v_inst_459_, v_key_462_, v_map_460_);
if (v___x_464_ == 0)
{
lean_dec(v_value_463_);
lean_dec(v_key_462_);
lean_dec_ref(v_inst_461_);
lean_dec_ref(v_map_460_);
lean_dec_ref(v_inst_459_);
lean_dec_ref(v_inst_458_);
return v___x_464_;
}
else
{
lean_object* v_entries_465_; lean_object* v_indexes_466_; lean_object* v___x_467_; lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_entries_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___f_476_; size_t v_sz_477_; size_t v___x_478_; lean_object* v___x_479_; lean_object* v_fst_480_; 
v_entries_465_ = lean_ctor_get(v_map_460_, 0);
lean_inc_ref(v_entries_465_);
v_indexes_466_ = lean_ctor_get(v_map_460_, 1);
lean_inc_ref(v_indexes_466_);
lean_dec_ref(v_map_460_);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_458_, v_inst_459_, v_indexes_466_, v_key_462_);
lean_dec_ref(v_indexes_466_);
lean_inc(v___x_467_);
v___f_468_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_468_, 0, v___x_467_);
lean_closure_set(v___f_468_, 1, v_entries_465_);
v___x_469_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_470_ = lean_array_get_size(v___x_467_);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_mk_empty_array_with_capacity(v___x_470_);
v_entries_473_ = l_Array_mapFinIdxM_map___redArg(v___x_469_, v___x_467_, v___f_468_, v___x_470_, v___x_471_, v___x_472_);
v___x_474_ = lean_box(0);
v___x_475_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_476_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_476_, 0, v_inst_461_);
lean_closure_set(v___f_476_, 1, v_value_463_);
lean_closure_set(v___f_476_, 2, v___x_475_);
lean_closure_set(v___f_476_, 3, v___x_474_);
v_sz_477_ = lean_array_size(v_entries_473_);
v___x_478_ = ((size_t)0ULL);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_469_, v_entries_473_, v___f_476_, v_sz_477_, v___x_478_, v___x_475_);
v_fst_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_fst_480_);
lean_dec(v___x_479_);
if (lean_obj_tag(v_fst_480_) == 0)
{
uint8_t v___x_481_; 
v___x_481_ = 0;
return v___x_481_;
}
else
{
lean_object* v_val_482_; 
v_val_482_ = lean_ctor_get(v_fst_480_, 0);
lean_inc(v_val_482_);
lean_dec_ref(v_fst_480_);
if (lean_obj_tag(v_val_482_) == 0)
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
else
{
lean_dec_ref(v_val_482_);
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___boxed(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_map_488_, lean_object* v_inst_489_, lean_object* v_key_490_, lean_object* v_value_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Std_Internal_IndexMultiMap_hasEntry(v_00_u03b1_484_, v_00_u03b2_485_, v_inst_486_, v_inst_487_, v_map_488_, v_inst_489_, v_key_490_, v_value_491_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f___redArg(lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_map_496_, lean_object* v_key_497_){
_start:
{
uint8_t v___x_498_; 
lean_inc(v_key_497_);
lean_inc_ref(v_inst_495_);
lean_inc_ref(v_inst_494_);
v___x_498_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_494_, v_inst_495_, v_key_497_, v_map_496_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v_key_497_);
lean_dec_ref(v_map_496_);
lean_dec_ref(v_inst_495_);
lean_dec_ref(v_inst_494_);
v___x_499_ = lean_box(0);
return v___x_499_;
}
else
{
lean_object* v_entries_500_; lean_object* v_indexes_501_; lean_object* v___x_502_; lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_entries_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_entries_500_ = lean_ctor_get(v_map_496_, 0);
lean_inc_ref(v_entries_500_);
v_indexes_501_ = lean_ctor_get(v_map_496_, 1);
lean_inc_ref(v_indexes_501_);
lean_dec_ref(v_map_496_);
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_494_, v_inst_495_, v_indexes_501_, v_key_497_);
lean_dec_ref(v_indexes_501_);
lean_inc(v___x_502_);
v___f_503_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_503_, 0, v___x_502_);
lean_closure_set(v___f_503_, 1, v_entries_500_);
v___x_504_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_505_ = lean_array_get_size(v___x_502_);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_mk_empty_array_with_capacity(v___x_505_);
v_entries_508_ = l_Array_mapFinIdxM_map___redArg(v___x_504_, v___x_502_, v___f_503_, v___x_505_, v___x_506_, v___x_507_);
v___x_509_ = lean_array_get_size(v_entries_508_);
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_sub(v___x_509_, v___x_510_);
v___x_512_ = lean_nat_dec_lt(v___x_511_, v___x_509_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v___x_511_);
lean_dec(v_entries_508_);
v___x_513_ = lean_box(0);
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_array_fget(v_entries_508_, v___x_511_);
lean_dec(v___x_511_);
lean_dec(v_entries_508_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f(lean_object* v_00_u03b1_516_, lean_object* v_00_u03b2_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_map_520_, lean_object* v_key_521_){
_start:
{
uint8_t v___x_522_; 
lean_inc(v_key_521_);
lean_inc_ref(v_inst_519_);
lean_inc_ref(v_inst_518_);
v___x_522_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_518_, v_inst_519_, v_key_521_, v_map_520_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_dec(v_key_521_);
lean_dec_ref(v_map_520_);
lean_dec_ref(v_inst_519_);
lean_dec_ref(v_inst_518_);
v___x_523_ = lean_box(0);
return v___x_523_;
}
else
{
lean_object* v_entries_524_; lean_object* v_indexes_525_; lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_entries_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_entries_524_ = lean_ctor_get(v_map_520_, 0);
lean_inc_ref(v_entries_524_);
v_indexes_525_ = lean_ctor_get(v_map_520_, 1);
lean_inc_ref(v_indexes_525_);
lean_dec_ref(v_map_520_);
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_518_, v_inst_519_, v_indexes_525_, v_key_521_);
lean_dec_ref(v_indexes_525_);
lean_inc(v___x_526_);
v___f_527_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_527_, 0, v___x_526_);
lean_closure_set(v___f_527_, 1, v_entries_524_);
v___x_528_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_529_ = lean_array_get_size(v___x_526_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_mk_empty_array_with_capacity(v___x_529_);
v_entries_532_ = l_Array_mapFinIdxM_map___redArg(v___x_528_, v___x_526_, v___f_527_, v___x_529_, v___x_530_, v___x_531_);
v___x_533_ = lean_array_get_size(v_entries_532_);
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_sub(v___x_533_, v___x_534_);
v___x_536_ = lean_nat_dec_lt(v___x_535_, v___x_533_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_dec(v___x_535_);
lean_dec(v_entries_532_);
v___x_537_ = lean_box(0);
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_array_fget(v_entries_532_, v___x_535_);
lean_dec(v___x_535_);
lean_dec(v_entries_532_);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg(lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_map_542_, lean_object* v_key_543_, lean_object* v_d_544_){
_start:
{
uint8_t v___x_545_; 
lean_inc(v_key_543_);
lean_inc_ref(v_inst_541_);
lean_inc_ref(v_inst_540_);
v___x_545_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_540_, v_inst_541_, v_key_543_, v_map_542_);
if (v___x_545_ == 0)
{
lean_dec(v_key_543_);
lean_dec_ref(v_inst_541_);
lean_dec_ref(v_inst_540_);
lean_inc(v_d_544_);
return v_d_544_;
}
else
{
lean_object* v_entries_546_; lean_object* v_indexes_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v_entry_550_; lean_object* v___x_551_; lean_object* v_snd_552_; 
v_entries_546_ = lean_ctor_get(v_map_542_, 0);
v_indexes_547_ = lean_ctor_get(v_map_542_, 1);
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_540_, v_inst_541_, v_indexes_547_, v_key_543_);
v___x_549_ = lean_unsigned_to_nat(0u);
v_entry_550_ = lean_array_fget(v___x_548_, v___x_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_array_fget_borrowed(v_entries_546_, v_entry_550_);
lean_dec(v_entry_550_);
v_snd_552_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_snd_552_);
return v_snd_552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg___boxed(lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_map_555_, lean_object* v_key_556_, lean_object* v_d_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_Internal_IndexMultiMap_getD___redArg(v_inst_553_, v_inst_554_, v_map_555_, v_key_556_, v_d_557_);
lean_dec(v_d_557_);
lean_dec_ref(v_map_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD(lean_object* v_00_u03b1_559_, lean_object* v_00_u03b2_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_map_563_, lean_object* v_key_564_, lean_object* v_d_565_){
_start:
{
uint8_t v___x_566_; 
lean_inc(v_key_564_);
lean_inc_ref(v_inst_562_);
lean_inc_ref(v_inst_561_);
v___x_566_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_561_, v_inst_562_, v_key_564_, v_map_563_);
if (v___x_566_ == 0)
{
lean_dec(v_key_564_);
lean_dec_ref(v_inst_562_);
lean_dec_ref(v_inst_561_);
lean_inc(v_d_565_);
return v_d_565_;
}
else
{
lean_object* v_entries_567_; lean_object* v_indexes_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_entry_571_; lean_object* v___x_572_; lean_object* v_snd_573_; 
v_entries_567_ = lean_ctor_get(v_map_563_, 0);
v_indexes_568_ = lean_ctor_get(v_map_563_, 1);
v___x_569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_561_, v_inst_562_, v_indexes_568_, v_key_564_);
v___x_570_ = lean_unsigned_to_nat(0u);
v_entry_571_ = lean_array_fget(v___x_569_, v___x_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_array_fget_borrowed(v_entries_567_, v_entry_571_);
lean_dec(v_entry_571_);
v_snd_573_ = lean_ctor_get(v___x_572_, 1);
lean_inc(v_snd_573_);
return v_snd_573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___boxed(lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_map_578_, lean_object* v_key_579_, lean_object* v_d_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_Internal_IndexMultiMap_getD(v_00_u03b1_574_, v_00_u03b2_575_, v_inst_576_, v_inst_577_, v_map_578_, v_key_579_, v_d_580_);
lean_dec(v_d_580_);
lean_dec_ref(v_map_578_);
return v_res_581_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_585_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2));
v___x_586_ = lean_unsigned_to_nat(14u);
v___x_587_ = lean_unsigned_to_nat(22u);
v___x_588_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1));
v___x_589_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0));
v___x_590_ = l_mkPanicMessageWithDecl(v___x_589_, v___x_588_, v___x_587_, v___x_586_, v___x_585_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg(lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_map_594_, lean_object* v_key_595_){
_start:
{
uint8_t v___x_596_; 
lean_inc(v_key_595_);
lean_inc_ref(v_inst_592_);
lean_inc_ref(v_inst_591_);
v___x_596_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_591_, v_inst_592_, v_key_595_, v_map_594_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v_key_595_);
lean_dec_ref(v_inst_592_);
lean_dec_ref(v_inst_591_);
v___x_597_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_598_ = l_panic___redArg(v_inst_593_, v___x_597_);
return v___x_598_;
}
else
{
lean_object* v_entries_599_; lean_object* v_indexes_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v_entry_603_; lean_object* v___x_604_; lean_object* v_snd_605_; 
v_entries_599_ = lean_ctor_get(v_map_594_, 0);
v_indexes_600_ = lean_ctor_get(v_map_594_, 1);
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_591_, v_inst_592_, v_indexes_600_, v_key_595_);
v___x_602_ = lean_unsigned_to_nat(0u);
v_entry_603_ = lean_array_fget(v___x_601_, v___x_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_array_fget_borrowed(v_entries_599_, v_entry_603_);
lean_dec(v_entry_603_);
v_snd_605_ = lean_ctor_get(v___x_604_, 1);
lean_inc(v_snd_605_);
return v_snd_605_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___boxed(lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_map_609_, lean_object* v_key_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_Internal_IndexMultiMap_get_x21___redArg(v_inst_606_, v_inst_607_, v_inst_608_, v_map_609_, v_key_610_);
lean_dec_ref(v_map_609_);
lean_dec(v_inst_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21(lean_object* v_00_u03b1_612_, lean_object* v_00_u03b2_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_map_617_, lean_object* v_key_618_){
_start:
{
uint8_t v___x_619_; 
lean_inc(v_key_618_);
lean_inc_ref(v_inst_615_);
lean_inc_ref(v_inst_614_);
v___x_619_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_614_, v_inst_615_, v_key_618_, v_map_617_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_key_618_);
lean_dec_ref(v_inst_615_);
lean_dec_ref(v_inst_614_);
v___x_620_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_621_ = l_panic___redArg(v_inst_616_, v___x_620_);
return v___x_621_;
}
else
{
lean_object* v_entries_622_; lean_object* v_indexes_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_entry_626_; lean_object* v___x_627_; lean_object* v_snd_628_; 
v_entries_622_ = lean_ctor_get(v_map_617_, 0);
v_indexes_623_ = lean_ctor_get(v_map_617_, 1);
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_614_, v_inst_615_, v_indexes_623_, v_key_618_);
v___x_625_ = lean_unsigned_to_nat(0u);
v_entry_626_ = lean_array_fget(v___x_624_, v___x_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_array_fget_borrowed(v_entries_622_, v_entry_626_);
lean_dec(v_entry_626_);
v_snd_628_ = lean_ctor_get(v___x_627_, 1);
lean_inc(v_snd_628_);
return v_snd_628_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___boxed(lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_map_634_, lean_object* v_key_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_Internal_IndexMultiMap_get_x21(v_00_u03b1_629_, v_00_u03b2_630_, v_inst_631_, v_inst_632_, v_inst_633_, v_map_634_, v_key_635_);
lean_dec_ref(v_map_634_);
lean_dec(v_inst_633_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(lean_object* v_x_637_, lean_object* v_h__1_638_, lean_object* v_h__2_639_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v_h__1_638_);
v___x_640_ = lean_box(0);
v___x_641_ = lean_apply_1(v_h__2_639_, v___x_640_);
return v___x_641_;
}
else
{
lean_object* v_val_642_; lean_object* v___x_643_; 
lean_dec(v_h__2_639_);
v_val_642_ = lean_ctor_get(v_x_637_, 0);
lean_inc(v_val_642_);
lean_dec_ref(v_x_637_);
v___x_643_ = lean_apply_1(v_h__1_638_, v_val_642_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter(lean_object* v_motive_644_, lean_object* v_x_645_, lean_object* v_h__1_646_, lean_object* v_h__2_647_){
_start:
{
if (lean_obj_tag(v_x_645_) == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v_h__1_646_);
v___x_648_ = lean_box(0);
v___x_649_ = lean_apply_1(v_h__2_647_, v___x_648_);
return v___x_649_;
}
else
{
lean_object* v_val_650_; lean_object* v___x_651_; 
lean_dec(v_h__2_647_);
v_val_650_ = lean_ctor_get(v_x_645_, 0);
lean_inc(v_val_650_);
lean_dec_ref(v_x_645_);
v___x_651_ = lean_apply_1(v_h__1_646_, v_val_650_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(lean_object* v_i_652_, lean_object* v_x_653_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = lean_unsigned_to_nat(1u);
v___x_655_ = lean_mk_empty_array_with_capacity(v___x_654_);
v___x_656_ = lean_array_push(v___x_655_, v_i_652_);
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
else
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_666_; 
v_val_658_ = lean_ctor_get(v_x_653_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v_x_653_);
if (v_isSharedCheck_666_ == 0)
{
v___x_660_ = v_x_653_;
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v_x_653_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_array_push(v_val_658_, v_i_652_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg(lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_map_669_, lean_object* v_key_670_, lean_object* v_value_671_){
_start:
{
lean_object* v_entries_672_; lean_object* v_indexes_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_685_; 
v_entries_672_ = lean_ctor_get(v_map_669_, 0);
v_indexes_673_ = lean_ctor_get(v_map_669_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v_map_669_);
if (v_isSharedCheck_685_ == 0)
{
v___x_675_ = v_map_669_;
v_isShared_676_ = v_isSharedCheck_685_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_indexes_673_);
lean_inc(v_entries_672_);
lean_dec(v_map_669_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_685_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v_i_677_; lean_object* v_f_678_; lean_object* v___x_679_; lean_object* v_entries_680_; lean_object* v_indexes_681_; lean_object* v___x_683_; 
v_i_677_ = lean_array_get_size(v_entries_672_);
v_f_678_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_678_, 0, v_i_677_);
lean_inc(v_key_670_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v_key_670_);
lean_ctor_set(v___x_679_, 1, v_value_671_);
v_entries_680_ = lean_array_push(v_entries_672_, v___x_679_);
v_indexes_681_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_667_, v_inst_668_, v_indexes_673_, v_key_670_, v_f_678_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v_indexes_681_);
lean_ctor_set(v___x_675_, 0, v_entries_680_);
v___x_683_ = v___x_675_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_entries_680_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_indexes_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert(lean_object* v_00_u03b1_686_, lean_object* v_00_u03b2_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_map_692_, lean_object* v_key_693_, lean_object* v_value_694_){
_start:
{
lean_object* v_entries_695_; lean_object* v_indexes_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_708_; 
v_entries_695_ = lean_ctor_get(v_map_692_, 0);
v_indexes_696_ = lean_ctor_get(v_map_692_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_map_692_);
if (v_isSharedCheck_708_ == 0)
{
v___x_698_ = v_map_692_;
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_indexes_696_);
lean_inc(v_entries_695_);
lean_dec(v_map_692_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_708_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_i_700_; lean_object* v_f_701_; lean_object* v___x_702_; lean_object* v_entries_703_; lean_object* v_indexes_704_; lean_object* v___x_706_; 
v_i_700_ = lean_array_get_size(v_entries_695_);
v_f_701_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_701_, 0, v_i_700_);
lean_inc(v_key_693_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_key_693_);
lean_ctor_set(v___x_702_, 1, v_value_694_);
v_entries_703_ = lean_array_push(v_entries_695_, v___x_702_);
v_indexes_704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_688_, v_inst_689_, v_indexes_696_, v_key_693_, v_f_701_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_indexes_704_);
lean_ctor_set(v___x_698_, 0, v_entries_703_);
v___x_706_ = v___x_698_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_entries_703_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_indexes_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1(lean_object* v_key_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_x1_712_, lean_object* v_x2_713_){
_start:
{
lean_object* v_entries_714_; lean_object* v_indexes_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_727_; 
v_entries_714_ = lean_ctor_get(v_x1_712_, 0);
v_indexes_715_ = lean_ctor_get(v_x1_712_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_x1_712_);
if (v_isSharedCheck_727_ == 0)
{
v___x_717_ = v_x1_712_;
v_isShared_718_ = v_isSharedCheck_727_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_indexes_715_);
lean_inc(v_entries_714_);
lean_dec(v_x1_712_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_727_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_i_719_; lean_object* v_f_720_; lean_object* v___x_721_; lean_object* v_entries_722_; lean_object* v_indexes_723_; lean_object* v___x_725_; 
v_i_719_ = lean_array_get_size(v_entries_714_);
v_f_720_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_720_, 0, v_i_719_);
lean_inc(v_key_709_);
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v_key_709_);
lean_ctor_set(v___x_721_, 1, v_x2_713_);
v_entries_722_ = lean_array_push(v_entries_714_, v___x_721_);
v_indexes_723_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_710_, v_inst_711_, v_indexes_715_, v_key_709_, v_f_720_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v_indexes_723_);
lean_ctor_set(v___x_717_, 0, v_entries_722_);
v___x_725_ = v___x_717_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_entries_722_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_indexes_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg(lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_map_730_, lean_object* v_key_731_, lean_object* v_values_732_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_array_get_size(v_values_732_);
v___x_735_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_736_ = lean_nat_dec_lt(v___x_733_, v___x_734_);
if (v___x_736_ == 0)
{
lean_dec_ref(v_values_732_);
lean_dec(v_key_731_);
lean_dec_ref(v_inst_729_);
lean_dec_ref(v_inst_728_);
return v_map_730_;
}
else
{
lean_object* v___f_737_; uint8_t v___x_738_; 
v___f_737_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_737_, 0, v_key_731_);
lean_closure_set(v___f_737_, 1, v_inst_728_);
lean_closure_set(v___f_737_, 2, v_inst_729_);
v___x_738_ = lean_nat_dec_le(v___x_734_, v___x_734_);
if (v___x_738_ == 0)
{
if (v___x_736_ == 0)
{
lean_dec_ref(v___f_737_);
lean_dec_ref(v_values_732_);
return v_map_730_;
}
else
{
size_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; 
v___x_739_ = ((size_t)0ULL);
v___x_740_ = lean_usize_of_nat(v___x_734_);
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_735_, v___f_737_, v_values_732_, v___x_739_, v___x_740_, v_map_730_);
return v___x_741_;
}
}
else
{
size_t v___x_742_; size_t v___x_743_; lean_object* v___x_744_; 
v___x_742_ = ((size_t)0ULL);
v___x_743_ = lean_usize_of_nat(v___x_734_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_735_, v___f_737_, v_values_732_, v___x_742_, v___x_743_, v_map_730_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany(lean_object* v_00_u03b1_745_, lean_object* v_00_u03b2_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_map_751_, lean_object* v_key_752_, lean_object* v_values_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_array_get_size(v_values_753_);
v___x_756_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_757_ = lean_nat_dec_lt(v___x_754_, v___x_755_);
if (v___x_757_ == 0)
{
lean_dec_ref(v_values_753_);
lean_dec(v_key_752_);
lean_dec_ref(v_inst_748_);
lean_dec_ref(v_inst_747_);
return v_map_751_;
}
else
{
lean_object* v___f_758_; uint8_t v___x_759_; 
v___f_758_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_758_, 0, v_key_752_);
lean_closure_set(v___f_758_, 1, v_inst_747_);
lean_closure_set(v___f_758_, 2, v_inst_748_);
v___x_759_ = lean_nat_dec_le(v___x_755_, v___x_755_);
if (v___x_759_ == 0)
{
if (v___x_757_ == 0)
{
lean_dec_ref(v___f_758_);
lean_dec_ref(v_values_753_);
return v_map_751_;
}
else
{
size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
v___x_760_ = ((size_t)0ULL);
v___x_761_ = lean_usize_of_nat(v___x_755_);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_756_, v___f_758_, v_values_753_, v___x_760_, v___x_761_, v_map_751_);
return v___x_762_;
}
}
else
{
size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; 
v___x_763_ = ((size_t)0ULL);
v___x_764_ = lean_usize_of_nat(v___x_755_);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_756_, v___f_758_, v_values_753_, v___x_763_, v___x_764_, v_map_751_);
return v___x_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object* v_00_u03b1_766_, lean_object* v_00_u03b2_767_, lean_object* v_inst_768_, lean_object* v_inst_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___boxed(lean_object* v_00_u03b1_771_, lean_object* v_00_u03b2_772_, lean_object* v_inst_773_, lean_object* v_inst_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_Internal_IndexMultiMap_empty(v_00_u03b1_771_, v_00_u03b2_772_, v_inst_773_, v_inst_774_);
lean_dec_ref(v_inst_774_);
lean_dec_ref(v_inst_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1(lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_acc_778_, lean_object* v_x_779_){
_start:
{
lean_object* v_fst_780_; lean_object* v_entries_781_; lean_object* v_indexes_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_793_; 
v_fst_780_ = lean_ctor_get(v_x_779_, 0);
lean_inc(v_fst_780_);
v_entries_781_ = lean_ctor_get(v_acc_778_, 0);
v_indexes_782_ = lean_ctor_get(v_acc_778_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_acc_778_);
if (v_isSharedCheck_793_ == 0)
{
v___x_784_ = v_acc_778_;
v_isShared_785_ = v_isSharedCheck_793_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_indexes_782_);
lean_inc(v_entries_781_);
lean_dec(v_acc_778_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_793_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_i_786_; lean_object* v_f_787_; lean_object* v_entries_788_; lean_object* v_indexes_789_; lean_object* v___x_791_; 
v_i_786_ = lean_array_get_size(v_entries_781_);
v_f_787_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_787_, 0, v_i_786_);
v_entries_788_ = lean_array_push(v_entries_781_, v_x_779_);
v_indexes_789_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_776_, v_inst_777_, v_indexes_782_, v_fst_780_, v_f_787_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v_indexes_789_);
lean_ctor_set(v___x_784_, 0, v_entries_788_);
v___x_791_ = v___x_784_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_entries_788_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_indexes_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg(lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_pairs_796_){
_start:
{
lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_inc_ref(v_inst_795_);
lean_inc_ref(v_inst_794_);
v___f_797_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_797_, 0, v_inst_794_);
lean_closure_set(v___f_797_, 1, v_inst_795_);
v___x_798_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_794_, v_inst_795_);
lean_dec_ref(v_inst_795_);
lean_dec_ref(v_inst_794_);
v___x_799_ = l_List_foldl___redArg(v___f_797_, v___x_798_, v_pairs_796_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList(lean_object* v_00_u03b1_800_, lean_object* v_00_u03b2_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_pairs_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_Internal_IndexMultiMap_ofList___redArg(v_inst_802_, v_inst_803_, v_pairs_806_);
return v___x_807_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains___redArg(lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_map_810_, lean_object* v_key_811_){
_start:
{
lean_object* v_indexes_812_; uint8_t v___x_813_; 
v_indexes_812_ = lean_ctor_get(v_map_810_, 1);
v___x_813_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_808_, v_inst_809_, v_indexes_812_, v_key_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___redArg___boxed(lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_map_816_, lean_object* v_key_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l_Std_Internal_IndexMultiMap_contains___redArg(v_inst_814_, v_inst_815_, v_map_816_, v_key_817_);
lean_dec_ref(v_map_816_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains(lean_object* v_00_u03b1_820_, lean_object* v_00_u03b2_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_map_824_, lean_object* v_key_825_){
_start:
{
lean_object* v_indexes_826_; uint8_t v___x_827_; 
v_indexes_826_ = lean_ctor_get(v_map_824_, 1);
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_822_, v_inst_823_, v_indexes_826_, v_key_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___boxed(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_map_832_, lean_object* v_key_833_){
_start:
{
uint8_t v_res_834_; lean_object* v_r_835_; 
v_res_834_ = l_Std_Internal_IndexMultiMap_contains(v_00_u03b1_828_, v_00_u03b2_829_, v_inst_830_, v_inst_831_, v_map_832_, v_key_833_);
lean_dec_ref(v_map_832_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg___lam__1(lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_key_838_, lean_object* v_f_839_, lean_object* v_x1_840_, lean_object* v_x2_841_){
_start:
{
lean_object* v_fst_842_; lean_object* v_snd_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_868_; 
v_fst_842_ = lean_ctor_get(v_x2_841_, 0);
v_snd_843_ = lean_ctor_get(v_x2_841_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_x2_841_);
if (v_isSharedCheck_868_ == 0)
{
v___x_845_ = v_x2_841_;
v_isShared_846_ = v_isSharedCheck_868_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_snd_843_);
lean_inc(v_fst_842_);
lean_dec(v_x2_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_868_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___y_848_; lean_object* v___x_865_; uint8_t v___x_866_; 
lean_inc_ref(v_inst_836_);
lean_inc(v_fst_842_);
v___x_865_ = lean_apply_2(v_inst_836_, v_fst_842_, v_key_838_);
v___x_866_ = lean_unbox(v___x_865_);
if (v___x_866_ == 0)
{
lean_dec(v_f_839_);
v___y_848_ = v_snd_843_;
goto v___jp_847_;
}
else
{
lean_object* v___x_867_; 
v___x_867_ = lean_apply_1(v_f_839_, v_snd_843_);
v___y_848_ = v___x_867_;
goto v___jp_847_;
}
v___jp_847_:
{
lean_object* v_entries_849_; lean_object* v_indexes_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_864_; 
v_entries_849_ = lean_ctor_get(v_x1_840_, 0);
v_indexes_850_ = lean_ctor_get(v_x1_840_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_x1_840_);
if (v_isSharedCheck_864_ == 0)
{
v___x_852_ = v_x1_840_;
v_isShared_853_ = v_isSharedCheck_864_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_indexes_850_);
lean_inc(v_entries_849_);
lean_dec(v_x1_840_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_864_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_i_854_; lean_object* v_f_855_; lean_object* v___x_857_; 
v_i_854_ = lean_array_get_size(v_entries_849_);
v_f_855_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_855_, 0, v_i_854_);
lean_inc(v_fst_842_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v___y_848_);
v___x_857_ = v___x_845_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_fst_842_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___y_848_);
v___x_857_ = v_reuseFailAlloc_863_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v_entries_858_; lean_object* v_indexes_859_; lean_object* v___x_861_; 
v_entries_858_ = lean_array_push(v_entries_849_, v___x_857_);
v_indexes_859_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_836_, v_inst_837_, v_indexes_850_, v_fst_842_, v_f_855_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v_indexes_859_);
lean_ctor_set(v___x_852_, 0, v_entries_858_);
v___x_861_ = v___x_852_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_entries_858_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_indexes_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg(lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_map_871_, lean_object* v_key_872_, lean_object* v_f_873_){
_start:
{
uint8_t v___x_874_; 
lean_inc(v_key_872_);
lean_inc_ref(v_inst_870_);
lean_inc_ref(v_inst_869_);
v___x_874_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_869_, v_inst_870_, v_key_872_, v_map_871_);
if (v___x_874_ == 0)
{
lean_dec(v_f_873_);
lean_dec(v_key_872_);
lean_dec_ref(v_inst_870_);
lean_dec_ref(v_inst_869_);
return v_map_871_;
}
else
{
lean_object* v_entries_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_entries_875_ = lean_ctor_get(v_map_871_, 0);
lean_inc_ref(v_entries_875_);
lean_dec_ref(v_map_871_);
v___x_876_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_869_, v_inst_870_);
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_array_get_size(v_entries_875_);
v___x_879_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_880_ = lean_nat_dec_lt(v___x_877_, v___x_878_);
if (v___x_880_ == 0)
{
lean_dec_ref(v_entries_875_);
lean_dec(v_f_873_);
lean_dec(v_key_872_);
lean_dec_ref(v_inst_870_);
lean_dec_ref(v_inst_869_);
return v___x_876_;
}
else
{
lean_object* v___f_881_; uint8_t v___x_882_; 
v___f_881_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_881_, 0, v_inst_869_);
lean_closure_set(v___f_881_, 1, v_inst_870_);
lean_closure_set(v___f_881_, 2, v_key_872_);
lean_closure_set(v___f_881_, 3, v_f_873_);
v___x_882_ = lean_nat_dec_le(v___x_878_, v___x_878_);
if (v___x_882_ == 0)
{
if (v___x_880_ == 0)
{
lean_dec_ref(v___f_881_);
lean_dec_ref(v_entries_875_);
return v___x_876_;
}
else
{
size_t v___x_883_; size_t v___x_884_; lean_object* v___x_885_; 
v___x_883_ = ((size_t)0ULL);
v___x_884_ = lean_usize_of_nat(v___x_878_);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_879_, v___f_881_, v_entries_875_, v___x_883_, v___x_884_, v___x_876_);
return v___x_885_;
}
}
else
{
size_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; 
v___x_886_ = ((size_t)0ULL);
v___x_887_ = lean_usize_of_nat(v___x_878_);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_879_, v___f_881_, v_entries_875_, v___x_886_, v___x_887_, v___x_876_);
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update(lean_object* v_00_u03b1_889_, lean_object* v_00_u03b2_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_map_895_, lean_object* v_key_896_, lean_object* v_f_897_){
_start:
{
uint8_t v___x_898_; 
lean_inc(v_key_896_);
lean_inc_ref(v_inst_892_);
lean_inc_ref(v_inst_891_);
v___x_898_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_891_, v_inst_892_, v_key_896_, v_map_895_);
if (v___x_898_ == 0)
{
lean_dec(v_f_897_);
lean_dec(v_key_896_);
lean_dec_ref(v_inst_892_);
lean_dec_ref(v_inst_891_);
return v_map_895_;
}
else
{
lean_object* v_entries_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_entries_899_ = lean_ctor_get(v_map_895_, 0);
lean_inc_ref(v_entries_899_);
lean_dec_ref(v_map_895_);
v___x_900_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_891_, v_inst_892_);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_array_get_size(v_entries_899_);
v___x_903_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_904_ = lean_nat_dec_lt(v___x_901_, v___x_902_);
if (v___x_904_ == 0)
{
lean_dec_ref(v_entries_899_);
lean_dec(v_f_897_);
lean_dec(v_key_896_);
lean_dec_ref(v_inst_892_);
lean_dec_ref(v_inst_891_);
return v___x_900_;
}
else
{
lean_object* v___f_905_; uint8_t v___x_906_; 
v___f_905_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_905_, 0, v_inst_891_);
lean_closure_set(v___f_905_, 1, v_inst_892_);
lean_closure_set(v___f_905_, 2, v_key_896_);
lean_closure_set(v___f_905_, 3, v_f_897_);
v___x_906_ = lean_nat_dec_le(v___x_902_, v___x_902_);
if (v___x_906_ == 0)
{
if (v___x_904_ == 0)
{
lean_dec_ref(v___f_905_);
lean_dec_ref(v_entries_899_);
return v___x_900_;
}
else
{
size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; 
v___x_907_ = ((size_t)0ULL);
v___x_908_ = lean_usize_of_nat(v___x_902_);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_903_, v___f_905_, v_entries_899_, v___x_907_, v___x_908_, v___x_900_);
return v___x_909_;
}
}
else
{
size_t v___x_910_; size_t v___x_911_; lean_object* v___x_912_; 
v___x_910_ = ((size_t)0ULL);
v___x_911_ = lean_usize_of_nat(v___x_902_);
v___x_912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_903_, v___f_905_, v_entries_899_, v___x_910_, v___x_911_, v___x_900_);
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast___redArg(lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_map_915_, lean_object* v_key_916_, lean_object* v_value_917_){
_start:
{
uint8_t v___x_918_; 
lean_inc(v_key_916_);
lean_inc_ref(v_inst_914_);
lean_inc_ref(v_inst_913_);
v___x_918_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_913_, v_inst_914_, v_key_916_, v_map_915_);
if (v___x_918_ == 0)
{
lean_dec(v_value_917_);
lean_dec(v_key_916_);
lean_dec_ref(v_inst_914_);
lean_dec_ref(v_inst_913_);
return v_map_915_;
}
else
{
lean_object* v_entries_919_; lean_object* v_indexes_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_934_; 
v_entries_919_ = lean_ctor_get(v_map_915_, 0);
v_indexes_920_ = lean_ctor_get(v_map_915_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_map_915_);
if (v_isSharedCheck_934_ == 0)
{
v___x_922_ = v_map_915_;
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_indexes_920_);
lean_inc(v_entries_919_);
lean_dec(v_map_915_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_idxs_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_lastIdx_928_; lean_object* v___x_929_; lean_object* v_entries_930_; lean_object* v___x_932_; 
lean_inc(v_key_916_);
v_idxs_924_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_913_, v_inst_914_, v_indexes_920_, v_key_916_);
v___x_925_ = lean_array_get_size(v_idxs_924_);
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_sub(v___x_925_, v___x_926_);
v_lastIdx_928_ = lean_array_fget(v_idxs_924_, v___x_927_);
lean_dec(v___x_927_);
lean_dec(v_idxs_924_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_key_916_);
lean_ctor_set(v___x_929_, 1, v_value_917_);
v_entries_930_ = lean_array_fset(v_entries_919_, v_lastIdx_928_, v___x_929_);
lean_dec(v_lastIdx_928_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v_entries_930_);
v___x_932_ = v___x_922_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_entries_930_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_indexes_920_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_map_939_, lean_object* v_key_940_, lean_object* v_value_941_){
_start:
{
uint8_t v___x_942_; 
lean_inc(v_key_940_);
lean_inc_ref(v_inst_938_);
lean_inc_ref(v_inst_937_);
v___x_942_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_937_, v_inst_938_, v_key_940_, v_map_939_);
if (v___x_942_ == 0)
{
lean_dec(v_value_941_);
lean_dec(v_key_940_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_inst_937_);
return v_map_939_;
}
else
{
lean_object* v_entries_943_; lean_object* v_indexes_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_958_; 
v_entries_943_ = lean_ctor_get(v_map_939_, 0);
v_indexes_944_ = lean_ctor_get(v_map_939_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_map_939_);
if (v_isSharedCheck_958_ == 0)
{
v___x_946_ = v_map_939_;
v_isShared_947_ = v_isSharedCheck_958_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_indexes_944_);
lean_inc(v_entries_943_);
lean_dec(v_map_939_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_958_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_idxs_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_lastIdx_952_; lean_object* v___x_953_; lean_object* v_entries_954_; lean_object* v___x_956_; 
lean_inc(v_key_940_);
v_idxs_948_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_937_, v_inst_938_, v_indexes_944_, v_key_940_);
v___x_949_ = lean_array_get_size(v_idxs_948_);
v___x_950_ = lean_unsigned_to_nat(1u);
v___x_951_ = lean_nat_sub(v___x_949_, v___x_950_);
v_lastIdx_952_ = lean_array_fget(v_idxs_948_, v___x_951_);
lean_dec(v___x_951_);
lean_dec(v_idxs_948_);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_key_940_);
lean_ctor_set(v___x_953_, 1, v_value_941_);
v_entries_954_ = lean_array_fset(v_entries_943_, v_lastIdx_952_, v___x_953_);
lean_dec(v_lastIdx_952_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v_entries_954_);
v___x_956_ = v___x_946_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_entries_954_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_indexes_944_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_x1_961_, lean_object* v_x2_962_){
_start:
{
lean_object* v_fst_963_; lean_object* v_entries_964_; lean_object* v_indexes_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_976_; 
v_fst_963_ = lean_ctor_get(v_x2_962_, 0);
lean_inc(v_fst_963_);
v_entries_964_ = lean_ctor_get(v_x1_961_, 0);
v_indexes_965_ = lean_ctor_get(v_x1_961_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_x1_961_);
if (v_isSharedCheck_976_ == 0)
{
v___x_967_ = v_x1_961_;
v_isShared_968_ = v_isSharedCheck_976_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_indexes_965_);
lean_inc(v_entries_964_);
lean_dec(v_x1_961_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_976_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_i_969_; lean_object* v_f_970_; lean_object* v_entries_971_; lean_object* v_indexes_972_; lean_object* v___x_974_; 
v_i_969_ = lean_array_get_size(v_entries_964_);
v_f_970_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_970_, 0, v_i_969_);
v_entries_971_ = lean_array_push(v_entries_964_, v_x2_962_);
v_indexes_972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_959_, v_inst_960_, v_indexes_965_, v_fst_963_, v_f_970_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v_indexes_972_);
lean_ctor_set(v___x_967_, 0, v_entries_971_);
v___x_974_ = v___x_967_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_entries_971_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_indexes_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__0(lean_object* v_inst_977_, lean_object* v_key_978_, lean_object* v_x1_979_, lean_object* v_x2_980_){
_start:
{
lean_object* v_fst_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_fst_981_ = lean_ctor_get(v_x2_980_, 0);
lean_inc(v_fst_981_);
v___x_982_ = lean_apply_2(v_inst_977_, v_fst_981_, v_key_978_);
v___x_983_ = lean_unbox(v___x_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
v___x_984_ = lean_array_push(v_x1_979_, v_x2_980_);
return v___x_984_;
}
else
{
lean_dec_ref(v_x2_980_);
return v_x1_979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_map_987_, lean_object* v_key_988_){
_start:
{
uint8_t v___x_989_; 
lean_inc(v_key_988_);
lean_inc_ref(v_inst_986_);
lean_inc_ref(v_inst_985_);
v___x_989_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_985_, v_inst_986_, v_key_988_, v_map_987_);
if (v___x_989_ == 0)
{
lean_dec(v_key_988_);
lean_dec_ref(v_inst_986_);
lean_dec_ref(v_inst_985_);
return v_map_987_;
}
else
{
lean_object* v_entries_990_; lean_object* v___f_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___y_995_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_entries_990_ = lean_ctor_get(v_map_987_, 0);
lean_inc_ref(v_entries_990_);
lean_dec_ref(v_map_987_);
lean_inc_ref(v_inst_986_);
lean_inc_ref(v_inst_985_);
v___f_991_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_991_, 0, v_inst_985_);
lean_closure_set(v___f_991_, 1, v_inst_986_);
v___x_992_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_985_, v_inst_986_);
lean_dec_ref(v_inst_986_);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_1006_ = lean_array_get_size(v_entries_990_);
v___x_1007_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___closed__0));
v___x_1008_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1009_ = lean_nat_dec_lt(v___x_993_, v___x_1006_);
if (v___x_1009_ == 0)
{
lean_dec_ref(v_entries_990_);
lean_dec(v_key_988_);
lean_dec_ref(v_inst_985_);
v___y_995_ = v___x_1007_;
goto v___jp_994_;
}
else
{
lean_object* v___f_1010_; uint8_t v___x_1011_; 
v___f_1010_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1010_, 0, v_inst_985_);
lean_closure_set(v___f_1010_, 1, v_key_988_);
v___x_1011_ = lean_nat_dec_le(v___x_1006_, v___x_1006_);
if (v___x_1011_ == 0)
{
if (v___x_1009_ == 0)
{
lean_dec_ref(v___f_1010_);
lean_dec_ref(v_entries_990_);
v___y_995_ = v___x_1007_;
goto v___jp_994_;
}
else
{
size_t v___x_1012_; size_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = ((size_t)0ULL);
v___x_1013_ = lean_usize_of_nat(v___x_1006_);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1008_, v___f_1010_, v_entries_990_, v___x_1012_, v___x_1013_, v___x_1007_);
v___y_995_ = v___x_1014_;
goto v___jp_994_;
}
}
else
{
size_t v___x_1015_; size_t v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = ((size_t)0ULL);
v___x_1016_ = lean_usize_of_nat(v___x_1006_);
v___x_1017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1008_, v___f_1010_, v_entries_990_, v___x_1015_, v___x_1016_, v___x_1007_);
v___y_995_ = v___x_1017_;
goto v___jp_994_;
}
}
v___jp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_996_ = lean_array_get_size(v___y_995_);
v___x_997_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_998_ = lean_nat_dec_lt(v___x_993_, v___x_996_);
if (v___x_998_ == 0)
{
lean_dec_ref(v___y_995_);
lean_dec_ref(v___f_991_);
return v___x_992_;
}
else
{
uint8_t v___x_999_; 
v___x_999_ = lean_nat_dec_le(v___x_996_, v___x_996_);
if (v___x_999_ == 0)
{
if (v___x_998_ == 0)
{
lean_dec_ref(v___y_995_);
lean_dec_ref(v___f_991_);
return v___x_992_;
}
else
{
size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((size_t)0ULL);
v___x_1001_ = lean_usize_of_nat(v___x_996_);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_997_, v___f_991_, v___y_995_, v___x_1000_, v___x_1001_, v___x_992_);
return v___x_1002_;
}
}
else
{
size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = ((size_t)0ULL);
v___x_1004_ = lean_usize_of_nat(v___x_996_);
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_997_, v___f_991_, v___y_995_, v___x_1003_, v___x_1004_, v___x_992_);
return v___x_1005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object* v_00_u03b1_1018_, lean_object* v_00_u03b2_1019_, lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_inst_1022_, lean_object* v_inst_1023_, lean_object* v_map_1024_, lean_object* v_key_1025_){
_start:
{
uint8_t v___x_1026_; 
lean_inc(v_key_1025_);
lean_inc_ref(v_inst_1021_);
lean_inc_ref(v_inst_1020_);
v___x_1026_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_1020_, v_inst_1021_, v_key_1025_, v_map_1024_);
if (v___x_1026_ == 0)
{
lean_dec(v_key_1025_);
lean_dec_ref(v_inst_1021_);
lean_dec_ref(v_inst_1020_);
return v_map_1024_;
}
else
{
lean_object* v_entries_1027_; lean_object* v___f_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___y_1032_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_entries_1027_ = lean_ctor_get(v_map_1024_, 0);
lean_inc_ref(v_entries_1027_);
lean_dec_ref(v_map_1024_);
lean_inc_ref(v_inst_1021_);
lean_inc_ref(v_inst_1020_);
v___f_1028_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1028_, 0, v_inst_1020_);
lean_closure_set(v___f_1028_, 1, v_inst_1021_);
v___x_1029_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1020_, v_inst_1021_);
lean_dec_ref(v_inst_1021_);
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1043_ = lean_array_get_size(v_entries_1027_);
v___x_1044_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___closed__0));
v___x_1045_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1046_ = lean_nat_dec_lt(v___x_1030_, v___x_1043_);
if (v___x_1046_ == 0)
{
lean_dec_ref(v_entries_1027_);
lean_dec(v_key_1025_);
lean_dec_ref(v_inst_1020_);
v___y_1032_ = v___x_1044_;
goto v___jp_1031_;
}
else
{
lean_object* v___f_1047_; uint8_t v___x_1048_; 
v___f_1047_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1047_, 0, v_inst_1020_);
lean_closure_set(v___f_1047_, 1, v_key_1025_);
v___x_1048_ = lean_nat_dec_le(v___x_1043_, v___x_1043_);
if (v___x_1048_ == 0)
{
if (v___x_1046_ == 0)
{
lean_dec_ref(v___f_1047_);
lean_dec_ref(v_entries_1027_);
v___y_1032_ = v___x_1044_;
goto v___jp_1031_;
}
else
{
size_t v___x_1049_; size_t v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = ((size_t)0ULL);
v___x_1050_ = lean_usize_of_nat(v___x_1043_);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1045_, v___f_1047_, v_entries_1027_, v___x_1049_, v___x_1050_, v___x_1044_);
v___y_1032_ = v___x_1051_;
goto v___jp_1031_;
}
}
else
{
size_t v___x_1052_; size_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = ((size_t)0ULL);
v___x_1053_ = lean_usize_of_nat(v___x_1043_);
v___x_1054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1045_, v___f_1047_, v_entries_1027_, v___x_1052_, v___x_1053_, v___x_1044_);
v___y_1032_ = v___x_1054_;
goto v___jp_1031_;
}
}
v___jp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1033_ = lean_array_get_size(v___y_1032_);
v___x_1034_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1035_ = lean_nat_dec_lt(v___x_1030_, v___x_1033_);
if (v___x_1035_ == 0)
{
lean_dec_ref(v___y_1032_);
lean_dec_ref(v___f_1028_);
return v___x_1029_;
}
else
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_nat_dec_le(v___x_1033_, v___x_1033_);
if (v___x_1036_ == 0)
{
if (v___x_1035_ == 0)
{
lean_dec_ref(v___y_1032_);
lean_dec_ref(v___f_1028_);
return v___x_1029_;
}
else
{
size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = lean_usize_of_nat(v___x_1033_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1034_, v___f_1028_, v___y_1032_, v___x_1037_, v___x_1038_, v___x_1029_);
return v___x_1039_;
}
}
else
{
size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = ((size_t)0ULL);
v___x_1041_ = lean_usize_of_nat(v___x_1033_);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1034_, v___f_1028_, v___y_1032_, v___x_1040_, v___x_1041_, v___x_1029_);
return v___x_1042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg(lean_object* v_map_1055_){
_start:
{
lean_object* v_entries_1056_; lean_object* v___x_1057_; 
v_entries_1056_ = lean_ctor_get(v_map_1055_, 0);
v___x_1057_ = lean_array_get_size(v_entries_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg___boxed(lean_object* v_map_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_Internal_IndexMultiMap_size___redArg(v_map_1058_);
lean_dec_ref(v_map_1058_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size(lean_object* v_00_u03b1_1060_, lean_object* v_00_u03b2_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_map_1064_){
_start:
{
lean_object* v_entries_1065_; lean_object* v___x_1066_; 
v_entries_1065_ = lean_ctor_get(v_map_1064_, 0);
v___x_1066_ = lean_array_get_size(v_entries_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___boxed(lean_object* v_00_u03b1_1067_, lean_object* v_00_u03b2_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_map_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Std_Internal_IndexMultiMap_size(v_00_u03b1_1067_, v_00_u03b2_1068_, v_inst_1069_, v_inst_1070_, v_map_1071_);
lean_dec_ref(v_map_1071_);
lean_dec_ref(v_inst_1070_);
lean_dec_ref(v_inst_1069_);
return v_res_1072_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty___redArg(lean_object* v_map_1073_){
_start:
{
lean_object* v_entries_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_entries_1074_ = lean_ctor_get(v_map_1073_, 0);
v___x_1075_ = lean_array_get_size(v_entries_1074_);
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = lean_nat_dec_eq(v___x_1075_, v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___redArg___boxed(lean_object* v_map_1078_){
_start:
{
uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l_Std_Internal_IndexMultiMap_isEmpty___redArg(v_map_1078_);
lean_dec_ref(v_map_1078_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty(lean_object* v_00_u03b1_1081_, lean_object* v_00_u03b2_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v_map_1085_){
_start:
{
lean_object* v_entries_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_entries_1086_ = lean_ctor_get(v_map_1085_, 0);
v___x_1087_ = lean_array_get_size(v_entries_1086_);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = lean_nat_dec_eq(v___x_1087_, v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___boxed(lean_object* v_00_u03b1_1090_, lean_object* v_00_u03b2_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_map_1094_){
_start:
{
uint8_t v_res_1095_; lean_object* v_r_1096_; 
v_res_1095_ = l_Std_Internal_IndexMultiMap_isEmpty(v_00_u03b1_1090_, v_00_u03b2_1091_, v_inst_1092_, v_inst_1093_, v_map_1094_);
lean_dec_ref(v_map_1094_);
lean_dec_ref(v_inst_1093_);
lean_dec_ref(v_inst_1092_);
v_r_1096_ = lean_box(v_res_1095_);
return v_r_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg(lean_object* v_map_1097_){
_start:
{
lean_object* v_entries_1098_; 
v_entries_1098_ = lean_ctor_get(v_map_1097_, 0);
lean_inc_ref(v_entries_1098_);
return v_entries_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg___boxed(lean_object* v_map_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Std_Internal_IndexMultiMap_toArray___redArg(v_map_1099_);
lean_dec_ref(v_map_1099_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray(lean_object* v_00_u03b1_1101_, lean_object* v_00_u03b2_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_map_1105_){
_start:
{
lean_object* v_entries_1106_; 
v_entries_1106_ = lean_ctor_get(v_map_1105_, 0);
lean_inc_ref(v_entries_1106_);
return v_entries_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___boxed(lean_object* v_00_u03b1_1107_, lean_object* v_00_u03b2_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_map_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Std_Internal_IndexMultiMap_toArray(v_00_u03b1_1107_, v_00_u03b2_1108_, v_inst_1109_, v_inst_1110_, v_map_1111_);
lean_dec_ref(v_map_1111_);
lean_dec_ref(v_inst_1110_);
lean_dec_ref(v_inst_1109_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___redArg(lean_object* v_map_1113_){
_start:
{
lean_object* v_entries_1114_; lean_object* v___x_1115_; 
v_entries_1114_ = lean_ctor_get(v_map_1113_, 0);
lean_inc_ref(v_entries_1114_);
lean_dec_ref(v_map_1113_);
v___x_1115_ = lean_array_to_list(v_entries_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList(lean_object* v_00_u03b1_1116_, lean_object* v_00_u03b2_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_map_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Std_Internal_IndexMultiMap_toList___redArg(v_map_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___boxed(lean_object* v_00_u03b1_1122_, lean_object* v_00_u03b2_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_map_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_Internal_IndexMultiMap_toList(v_00_u03b1_1122_, v_00_u03b2_1123_, v_inst_1124_, v_inst_1125_, v_map_1126_);
lean_dec_ref(v_inst_1125_);
lean_dec_ref(v_inst_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_m1_1130_, lean_object* v_m2_1131_){
_start:
{
lean_object* v_entries_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v_entries_1132_ = lean_ctor_get(v_m2_1131_, 0);
lean_inc_ref(v_entries_1132_);
lean_dec_ref(v_m2_1131_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_array_get_size(v_entries_1132_);
v___x_1135_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1136_ = lean_nat_dec_lt(v___x_1133_, v___x_1134_);
if (v___x_1136_ == 0)
{
lean_dec_ref(v_entries_1132_);
lean_dec_ref(v_inst_1129_);
lean_dec_ref(v_inst_1128_);
return v_m1_1130_;
}
else
{
lean_object* v___f_1137_; uint8_t v___x_1138_; 
v___f_1137_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1137_, 0, v_inst_1128_);
lean_closure_set(v___f_1137_, 1, v_inst_1129_);
v___x_1138_ = lean_nat_dec_le(v___x_1134_, v___x_1134_);
if (v___x_1138_ == 0)
{
if (v___x_1136_ == 0)
{
lean_dec_ref(v___f_1137_);
lean_dec_ref(v_entries_1132_);
return v_m1_1130_;
}
else
{
size_t v___x_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = ((size_t)0ULL);
v___x_1140_ = lean_usize_of_nat(v___x_1134_);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1135_, v___f_1137_, v_entries_1132_, v___x_1139_, v___x_1140_, v_m1_1130_);
return v___x_1141_;
}
}
else
{
size_t v___x_1142_; size_t v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = ((size_t)0ULL);
v___x_1143_ = lean_usize_of_nat(v___x_1134_);
v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1135_, v___f_1137_, v_entries_1132_, v___x_1142_, v___x_1143_, v_m1_1130_);
return v___x_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object* v_00_u03b1_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_m1_1151_, lean_object* v_m2_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Std_Internal_IndexMultiMap_merge___redArg(v_inst_1147_, v_inst_1148_, v_m1_1151_, v_m2_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(lean_object* v_inst_1154_, lean_object* v_inst_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1154_, v_inst_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object* v_inst_1157_, lean_object* v_inst_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(v_inst_1157_, v_inst_1158_);
lean_dec_ref(v_inst_1158_);
lean_dec_ref(v_inst_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection(lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_inst_1162_, lean_object* v_inst_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1162_, v_inst_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_1165_, lean_object* v_00_u03b2_1166_, lean_object* v_inst_1167_, lean_object* v_inst_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_Internal_IndexMultiMap_instEmptyCollection(v_00_u03b1_1165_, v_00_u03b2_1166_, v_inst_1167_, v_inst_1168_);
lean_dec_ref(v_inst_1168_);
lean_dec_ref(v_inst_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_x_1172_){
_start:
{
lean_object* v_fst_1173_; lean_object* v___x_1174_; lean_object* v_entries_1175_; lean_object* v_indexes_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1187_; 
v_fst_1173_ = lean_ctor_get(v_x_1172_, 0);
lean_inc(v_fst_1173_);
v___x_1174_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1170_, v_inst_1171_);
v_entries_1175_ = lean_ctor_get(v___x_1174_, 0);
v_indexes_1176_ = lean_ctor_get(v___x_1174_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1178_ = v___x_1174_;
v_isShared_1179_ = v_isSharedCheck_1187_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_indexes_1176_);
lean_inc(v_entries_1175_);
lean_dec(v___x_1174_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1187_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_i_1180_; lean_object* v_f_1181_; lean_object* v_entries_1182_; lean_object* v_indexes_1183_; lean_object* v___x_1185_; 
v_i_1180_ = lean_array_get_size(v_entries_1175_);
v_f_1181_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1181_, 0, v_i_1180_);
v_entries_1182_ = lean_array_push(v_entries_1175_, v_x_1172_);
v_indexes_1183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1170_, v_inst_1171_, v_indexes_1176_, v_fst_1173_, v_f_1181_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v_indexes_1183_);
lean_ctor_set(v___x_1178_, 0, v_entries_1182_);
v___x_1185_ = v___x_1178_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_entries_1182_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_indexes_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1188_, lean_object* v_inst_1189_){
_start:
{
lean_object* v___f_1190_; 
v___f_1190_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1190_, 0, v_inst_1188_);
lean_closure_set(v___f_1190_, 1, v_inst_1189_);
return v___f_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1191_, lean_object* v_00_u03b2_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_){
_start:
{
lean_object* v___f_1197_; 
v___f_1197_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1197_, 0, v_inst_1193_);
lean_closure_set(v___f_1197_, 1, v_inst_1194_);
return v___f_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_x_1200_, lean_object* v_m_1201_){
_start:
{
lean_object* v_fst_1202_; lean_object* v_entries_1203_; lean_object* v_indexes_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1215_; 
v_fst_1202_ = lean_ctor_get(v_x_1200_, 0);
lean_inc(v_fst_1202_);
v_entries_1203_ = lean_ctor_get(v_m_1201_, 0);
v_indexes_1204_ = lean_ctor_get(v_m_1201_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_m_1201_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1206_ = v_m_1201_;
v_isShared_1207_ = v_isSharedCheck_1215_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_indexes_1204_);
lean_inc(v_entries_1203_);
lean_dec(v_m_1201_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1215_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_i_1208_; lean_object* v_f_1209_; lean_object* v_entries_1210_; lean_object* v_indexes_1211_; lean_object* v___x_1213_; 
v_i_1208_ = lean_array_get_size(v_entries_1203_);
v_f_1209_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1209_, 0, v_i_1208_);
v_entries_1210_ = lean_array_push(v_entries_1203_, v_x_1200_);
v_indexes_1211_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1198_, v_inst_1199_, v_indexes_1204_, v_fst_1202_, v_f_1209_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v_indexes_1211_);
lean_ctor_set(v___x_1206_, 0, v_entries_1210_);
v___x_1213_ = v___x_1206_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_entries_1210_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_indexes_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1216_, lean_object* v_inst_1217_){
_start:
{
lean_object* v___f_1218_; 
v___f_1218_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1218_, 0, v_inst_1216_);
lean_closure_set(v___f_1218_, 1, v_inst_1217_);
return v___f_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1219_, lean_object* v_00_u03b2_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_){
_start:
{
lean_object* v___f_1225_; 
v___f_1225_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1225_, 0, v_inst_1221_);
lean_closure_set(v___f_1225_, 1, v_inst_1222_);
return v___f_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1226_, lean_object* v_inst_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1228_, 0, lean_box(0));
lean_closure_set(v___x_1228_, 1, lean_box(0));
lean_closure_set(v___x_1228_, 2, v_inst_1226_);
lean_closure_set(v___x_1228_, 3, v_inst_1227_);
lean_closure_set(v___x_1228_, 4, lean_box(0));
lean_closure_set(v___x_1228_, 5, lean_box(0));
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1229_, lean_object* v_00_u03b2_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1235_, 0, lean_box(0));
lean_closure_set(v___x_1235_, 1, lean_box(0));
lean_closure_set(v___x_1235_, 2, v_inst_1231_);
lean_closure_set(v___x_1235_, 3, v_inst_1232_);
lean_closure_set(v___x_1235_, 4, lean_box(0));
lean_closure_set(v___x_1235_, 5, lean_box(0));
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1236_, lean_object* v_a_1237_, lean_object* v_x_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_apply_2(v_f_1236_, v_a_1237_, v___y_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1241_, lean_object* v_00_u03b2_1242_, lean_object* v_map_1243_, lean_object* v_b_1244_, lean_object* v_f_1245_){
_start:
{
lean_object* v_entries_1246_; lean_object* v___f_1247_; size_t v_sz_1248_; size_t v___x_1249_; lean_object* v___x_1250_; 
v_entries_1246_ = lean_ctor_get(v_map_1243_, 0);
lean_inc_ref(v_entries_1246_);
lean_dec_ref(v_map_1243_);
v___f_1247_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1247_, 0, v_f_1245_);
v_sz_1248_ = lean_array_size(v_entries_1246_);
v___x_1249_ = ((size_t)0ULL);
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1241_, v_entries_1246_, v___f_1247_, v_sz_1248_, v___x_1249_, v_b_1244_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg(lean_object* v_inst_1251_){
_start:
{
lean_object* v___f_1252_; 
v___f_1252_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1252_, 0, v_inst_1251_);
return v___f_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad(lean_object* v_00_u03b1_1253_, lean_object* v_00_u03b2_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_m_1257_, lean_object* v_inst_1258_){
_start:
{
lean_object* v___f_1259_; 
v___f_1259_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1259_, 0, v_inst_1258_);
return v___f_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_00_u03b2_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_m_1264_, lean_object* v_inst_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Std_Internal_IndexMultiMap_instForInProdOfMonad(v_00_u03b1_1260_, v_00_u03b2_1261_, v_inst_1262_, v_inst_1263_, v_m_1264_, v_inst_1265_);
lean_dec_ref(v_inst_1263_);
lean_dec_ref(v_inst_1262_);
return v_res_1266_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_IndexMultiMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Internal_IndexMultiMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Internal_IndexMultiMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal_IndexMultiMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Internal_IndexMultiMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Internal_IndexMultiMap(builtin);
}
#ifdef __cplusplus
}
#endif
