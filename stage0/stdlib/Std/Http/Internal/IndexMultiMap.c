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
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
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
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
static const lean_array_object l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__0 = (const lean_object*)&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__0_value;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___closed__0;
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
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object*);
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
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_unsigned_to_nat(16u);
v___x_182_ = lean_mk_array(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1, &l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2, &l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2);
v___x_187_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__0));
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg(){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___boxed(lean_object* v___dummy_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Internal_instInhabitedIndexMultiMap___redArg();
return v_res_192_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__0(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Std_Internal_instInhabitedIndexMultiMap___redArg();
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap(lean_object* v_00_u03b1_194_, lean_object* v_00_u03b2_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__0, &l_Std_Internal_instInhabitedIndexMultiMap___closed__0_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__0);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___boxed(lean_object* v_00_u03b1_201_, lean_object* v_00_u03b2_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_inst_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Internal_instInhabitedIndexMultiMap(v_00_u03b1_201_, v_00_u03b2_202_, v_inst_203_, v_inst_204_, v_inst_205_, v_inst_206_);
lean_dec(v_inst_206_);
lean_dec(v_inst_205_);
lean_dec_ref(v_inst_204_);
lean_dec_ref(v_inst_203_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___redArg(){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_box(0);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___redArg___boxed(lean_object* v___dummy_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Internal_IndexMultiMap_instMembership___redArg();
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership(lean_object* v_00_u03b1_212_, lean_object* v_00_u03b2_213_, lean_object* v_inst_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_box(0);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___boxed(lean_object* v_00_u03b1_217_, lean_object* v_00_u03b2_218_, lean_object* v_inst_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_Internal_IndexMultiMap_instMembership(v_00_u03b1_217_, v_00_u03b2_218_, v_inst_219_, v_inst_220_);
lean_dec_ref(v_inst_220_);
lean_dec_ref(v_inst_219_);
return v_res_221_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_key_224_, lean_object* v_map_225_){
_start:
{
lean_object* v_indexes_226_; uint8_t v___x_227_; 
v_indexes_226_ = lean_ctor_get(v_map_225_, 1);
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_222_, v_inst_223_, v_indexes_226_, v_key_224_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___redArg___boxed(lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_key_230_, lean_object* v_map_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_228_, v_inst_229_, v_key_230_, v_map_231_);
lean_dec_ref(v_map_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_key_238_, lean_object* v_map_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_236_, v_inst_237_, v_key_238_, v_map_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___boxed(lean_object* v_00_u03b1_241_, lean_object* v_00_u03b2_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_key_245_, lean_object* v_map_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Std_Internal_IndexMultiMap_instDecidableMem(v_00_u03b1_241_, v_00_u03b2_242_, v_inst_243_, v_inst_244_, v_key_245_, v_map_246_);
lean_dec_ref(v_map_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(lean_object* v___x_249_, lean_object* v_entries_250_, lean_object* v_x1_251_, lean_object* v_x2_252_, lean_object* v_x3_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_snd_256_; 
v___x_254_ = lean_array_fget_borrowed(v___x_249_, v_x1_251_);
v___x_255_ = lean_array_fget_borrowed(v_entries_250_, v___x_254_);
v_snd_256_ = lean_ctor_get(v___x_255_, 1);
lean_inc(v_snd_256_);
return v_snd_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed(lean_object* v___x_257_, lean_object* v_entries_258_, lean_object* v_x1_259_, lean_object* v_x2_260_, lean_object* v_x3_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(v___x_257_, v_entries_258_, v_x1_259_, v_x2_260_, v_x3_261_);
lean_dec(v_x2_260_);
lean_dec(v_x1_259_);
lean_dec_ref(v_entries_258_);
lean_dec(v___x_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg(lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_map_265_, lean_object* v_key_266_){
_start:
{
lean_object* v_entries_267_; lean_object* v_indexes_268_; lean_object* v___x_269_; lean_object* v___f_270_; lean_object* v___x_271_; size_t v_sz_272_; size_t v___x_273_; lean_object* v_entries_274_; 
v_entries_267_ = lean_ctor_get(v_map_265_, 0);
lean_inc_ref(v_entries_267_);
v_indexes_268_ = lean_ctor_get(v_map_265_, 1);
lean_inc_ref(v_indexes_268_);
lean_dec_ref(v_map_265_);
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_263_, v_inst_264_, v_indexes_268_, v_key_266_);
lean_dec_ref(v_indexes_268_);
lean_inc_n(v___x_269_, 2);
v___f_270_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_270_, 0, v___x_269_);
lean_closure_set(v___f_270_, 1, v_entries_267_);
v___x_271_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_272_ = lean_array_size(v___x_269_);
v___x_273_ = ((size_t)0ULL);
v_entries_274_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_271_, v___x_269_, v___f_270_, v_sz_272_, v___x_273_, v___x_269_);
lean_dec(v___x_269_);
return v_entries_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll(lean_object* v_00_u03b1_275_, lean_object* v_00_u03b2_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_map_279_, lean_object* v_key_280_, lean_object* v_h_281_){
_start:
{
lean_object* v_entries_282_; lean_object* v_indexes_283_; lean_object* v___x_284_; lean_object* v___f_285_; lean_object* v___x_286_; size_t v_sz_287_; size_t v___x_288_; lean_object* v_entries_289_; 
v_entries_282_ = lean_ctor_get(v_map_279_, 0);
lean_inc_ref(v_entries_282_);
v_indexes_283_ = lean_ctor_get(v_map_279_, 1);
lean_inc_ref(v_indexes_283_);
lean_dec_ref(v_map_279_);
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_277_, v_inst_278_, v_indexes_283_, v_key_280_);
lean_dec_ref(v_indexes_283_);
lean_inc_n(v___x_284_, 2);
v___f_285_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_285_, 0, v___x_284_);
lean_closure_set(v___f_285_, 1, v_entries_282_);
v___x_286_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_287_ = lean_array_size(v___x_284_);
v___x_288_ = ((size_t)0ULL);
v_entries_289_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_286_, v___x_284_, v___f_285_, v_sz_287_, v___x_288_, v___x_284_);
lean_dec(v___x_284_);
return v_entries_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_map_292_, lean_object* v_key_293_){
_start:
{
lean_object* v_entries_294_; lean_object* v_indexes_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v_entry_298_; lean_object* v___x_299_; lean_object* v_snd_300_; 
v_entries_294_ = lean_ctor_get(v_map_292_, 0);
v_indexes_295_ = lean_ctor_get(v_map_292_, 1);
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_290_, v_inst_291_, v_indexes_295_, v_key_293_);
v___x_297_ = lean_unsigned_to_nat(0u);
v_entry_298_ = lean_array_fget(v___x_296_, v___x_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_array_fget_borrowed(v_entries_294_, v_entry_298_);
lean_dec(v_entry_298_);
v_snd_300_ = lean_ctor_get(v___x_299_, 1);
lean_inc(v_snd_300_);
return v_snd_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg___boxed(lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_map_303_, lean_object* v_key_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_Internal_IndexMultiMap_get___redArg(v_inst_301_, v_inst_302_, v_map_303_, v_key_304_);
lean_dec_ref(v_map_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get(lean_object* v_00_u03b1_306_, lean_object* v_00_u03b2_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_map_310_, lean_object* v_key_311_, lean_object* v_h_312_){
_start:
{
lean_object* v_entries_313_; lean_object* v_indexes_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_entry_317_; lean_object* v___x_318_; lean_object* v_snd_319_; 
v_entries_313_ = lean_ctor_get(v_map_310_, 0);
v_indexes_314_ = lean_ctor_get(v_map_310_, 1);
v___x_315_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_308_, v_inst_309_, v_indexes_314_, v_key_311_);
v___x_316_ = lean_unsigned_to_nat(0u);
v_entry_317_ = lean_array_fget(v___x_315_, v___x_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_array_fget_borrowed(v_entries_313_, v_entry_317_);
lean_dec(v_entry_317_);
v_snd_319_ = lean_ctor_get(v___x_318_, 1);
lean_inc(v_snd_319_);
return v_snd_319_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___boxed(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_map_324_, lean_object* v_key_325_, lean_object* v_h_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_Internal_IndexMultiMap_get(v_00_u03b1_320_, v_00_u03b2_321_, v_inst_322_, v_inst_323_, v_map_324_, v_key_325_, v_h_326_);
lean_dec_ref(v_map_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f___redArg(lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_map_330_, lean_object* v_key_331_){
_start:
{
lean_object* v_entries_332_; lean_object* v_indexes_333_; uint8_t v___x_334_; 
v_entries_332_ = lean_ctor_get(v_map_330_, 0);
lean_inc_ref(v_entries_332_);
v_indexes_333_ = lean_ctor_get(v_map_330_, 1);
lean_inc_ref(v_indexes_333_);
lean_dec_ref(v_map_330_);
lean_inc(v_key_331_);
lean_inc_ref(v_inst_329_);
lean_inc_ref(v_inst_328_);
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_328_, v_inst_329_, v_indexes_333_, v_key_331_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec_ref(v_indexes_333_);
lean_dec_ref(v_entries_332_);
lean_dec(v_key_331_);
lean_dec_ref(v_inst_329_);
lean_dec_ref(v_inst_328_);
v___x_335_ = lean_box(0);
return v___x_335_;
}
else
{
lean_object* v___x_336_; lean_object* v___f_337_; lean_object* v___x_338_; size_t v_sz_339_; size_t v___x_340_; lean_object* v_entries_341_; lean_object* v___x_342_; 
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_328_, v_inst_329_, v_indexes_333_, v_key_331_);
lean_dec_ref(v_indexes_333_);
lean_inc_n(v___x_336_, 2);
v___f_337_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_337_, 0, v___x_336_);
lean_closure_set(v___f_337_, 1, v_entries_332_);
v___x_338_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_339_ = lean_array_size(v___x_336_);
v___x_340_ = ((size_t)0ULL);
v_entries_341_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_338_, v___x_336_, v___f_337_, v_sz_339_, v___x_340_, v___x_336_);
lean_dec(v___x_336_);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v_entries_341_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_map_347_, lean_object* v_key_348_){
_start:
{
lean_object* v_entries_349_; lean_object* v_indexes_350_; uint8_t v___x_351_; 
v_entries_349_ = lean_ctor_get(v_map_347_, 0);
lean_inc_ref(v_entries_349_);
v_indexes_350_ = lean_ctor_get(v_map_347_, 1);
lean_inc_ref(v_indexes_350_);
lean_dec_ref(v_map_347_);
lean_inc(v_key_348_);
lean_inc_ref(v_inst_346_);
lean_inc_ref(v_inst_345_);
v___x_351_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_345_, v_inst_346_, v_indexes_350_, v_key_348_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec_ref(v_indexes_350_);
lean_dec_ref(v_entries_349_);
lean_dec(v_key_348_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
v___x_352_ = lean_box(0);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v___f_354_; lean_object* v___x_355_; size_t v_sz_356_; size_t v___x_357_; lean_object* v_entries_358_; lean_object* v___x_359_; 
v___x_353_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_345_, v_inst_346_, v_indexes_350_, v_key_348_);
lean_dec_ref(v_indexes_350_);
lean_inc_n(v___x_353_, 2);
v___f_354_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_354_, 0, v___x_353_);
lean_closure_set(v___f_354_, 1, v_entries_349_);
v___x_355_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_356_ = lean_array_size(v___x_353_);
v___x_357_ = ((size_t)0ULL);
v_entries_358_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_355_, v___x_353_, v___f_354_, v_sz_356_, v___x_357_, v___x_353_);
lean_dec(v___x_353_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v_entries_358_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg(lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_map_362_, lean_object* v_key_363_){
_start:
{
lean_object* v_entries_364_; lean_object* v_indexes_365_; uint8_t v___x_366_; 
v_entries_364_ = lean_ctor_get(v_map_362_, 0);
v_indexes_365_ = lean_ctor_get(v_map_362_, 1);
lean_inc(v_key_363_);
lean_inc_ref(v_inst_361_);
lean_inc_ref(v_inst_360_);
v___x_366_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_360_, v_inst_361_, v_indexes_365_, v_key_363_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
lean_dec(v_key_363_);
lean_dec_ref(v_inst_361_);
lean_dec_ref(v_inst_360_);
v___x_367_ = lean_box(0);
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_entry_370_; lean_object* v___x_371_; lean_object* v_snd_372_; lean_object* v___x_373_; 
v___x_368_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_360_, v_inst_361_, v_indexes_365_, v_key_363_);
v___x_369_ = lean_unsigned_to_nat(0u);
v_entry_370_ = lean_array_fget(v___x_368_, v___x_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_array_fget_borrowed(v_entries_364_, v_entry_370_);
lean_dec(v_entry_370_);
v_snd_372_ = lean_ctor_get(v___x_371_, 1);
lean_inc(v_snd_372_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v_snd_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg___boxed(lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_map_376_, lean_object* v_key_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_Internal_IndexMultiMap_get_x3f___redArg(v_inst_374_, v_inst_375_, v_map_376_, v_key_377_);
lean_dec_ref(v_map_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_map_383_, lean_object* v_key_384_){
_start:
{
lean_object* v_entries_385_; lean_object* v_indexes_386_; uint8_t v___x_387_; 
v_entries_385_ = lean_ctor_get(v_map_383_, 0);
v_indexes_386_ = lean_ctor_get(v_map_383_, 1);
lean_inc(v_key_384_);
lean_inc_ref(v_inst_382_);
lean_inc_ref(v_inst_381_);
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_381_, v_inst_382_, v_indexes_386_, v_key_384_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec(v_key_384_);
lean_dec_ref(v_inst_382_);
lean_dec_ref(v_inst_381_);
v___x_388_ = lean_box(0);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_entry_391_; lean_object* v___x_392_; lean_object* v_snd_393_; lean_object* v___x_394_; 
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_381_, v_inst_382_, v_indexes_386_, v_key_384_);
v___x_390_ = lean_unsigned_to_nat(0u);
v_entry_391_ = lean_array_fget(v___x_389_, v___x_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_array_fget_borrowed(v_entries_385_, v_entry_391_);
lean_dec(v_entry_391_);
v_snd_393_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_snd_393_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v_snd_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___boxed(lean_object* v_00_u03b1_395_, lean_object* v_00_u03b2_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_map_399_, lean_object* v_key_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_Internal_IndexMultiMap_get_x3f(v_00_u03b1_395_, v_00_u03b2_396_, v_inst_397_, v_inst_398_, v_map_399_, v_key_400_);
lean_dec_ref(v_map_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(lean_object* v_inst_402_, lean_object* v_value_403_, lean_object* v___x_404_, lean_object* v___x_405_, lean_object* v_a_406_, lean_object* v_x_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
lean_inc(v_a_406_);
v___x_409_ = lean_apply_2(v_inst_402_, v_a_406_, v_value_403_);
v___x_410_ = lean_unbox(v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec(v_a_406_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_404_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v___x_404_);
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v_a_406_);
v___x_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_405_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed(lean_object* v_inst_416_, lean_object* v_value_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v_a_420_, lean_object* v_x_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(v_inst_416_, v_value_417_, v___x_418_, v___x_419_, v_a_420_, v_x_421_, v___y_422_);
lean_dec_ref(v___y_422_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry___redArg(lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_map_429_, lean_object* v_inst_430_, lean_object* v_key_431_, lean_object* v_value_432_){
_start:
{
lean_object* v_entries_433_; lean_object* v_indexes_434_; uint8_t v___x_435_; 
v_entries_433_ = lean_ctor_get(v_map_429_, 0);
lean_inc_ref(v_entries_433_);
v_indexes_434_ = lean_ctor_get(v_map_429_, 1);
lean_inc_ref(v_indexes_434_);
lean_dec_ref(v_map_429_);
lean_inc(v_key_431_);
lean_inc_ref(v_inst_428_);
lean_inc_ref(v_inst_427_);
v___x_435_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_427_, v_inst_428_, v_indexes_434_, v_key_431_);
if (v___x_435_ == 0)
{
lean_dec_ref(v_indexes_434_);
lean_dec_ref(v_entries_433_);
lean_dec(v_value_432_);
lean_dec(v_key_431_);
lean_dec_ref(v_inst_430_);
lean_dec_ref(v_inst_428_);
lean_dec_ref(v_inst_427_);
return v___x_435_;
}
else
{
lean_object* v___x_436_; lean_object* v___f_437_; lean_object* v___x_438_; size_t v_sz_439_; size_t v___x_440_; lean_object* v_entries_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___f_444_; size_t v_sz_445_; lean_object* v___x_446_; lean_object* v_fst_447_; 
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_427_, v_inst_428_, v_indexes_434_, v_key_431_);
lean_dec_ref(v_indexes_434_);
lean_inc_n(v___x_436_, 2);
v___f_437_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_437_, 0, v___x_436_);
lean_closure_set(v___f_437_, 1, v_entries_433_);
v___x_438_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_439_ = lean_array_size(v___x_436_);
v___x_440_ = ((size_t)0ULL);
v_entries_441_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_438_, v___x_436_, v___f_437_, v_sz_439_, v___x_440_, v___x_436_);
lean_dec(v___x_436_);
v___x_442_ = lean_box(0);
v___x_443_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_444_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_444_, 0, v_inst_430_);
lean_closure_set(v___f_444_, 1, v_value_432_);
lean_closure_set(v___f_444_, 2, v___x_443_);
lean_closure_set(v___f_444_, 3, v___x_442_);
v_sz_445_ = lean_array_size(v_entries_441_);
v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_438_, v_entries_441_, v___f_444_, v_sz_445_, v___x_440_, v___x_443_);
v_fst_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_fst_447_);
lean_dec(v___x_446_);
if (lean_obj_tag(v_fst_447_) == 0)
{
uint8_t v___x_448_; 
v___x_448_ = 0;
return v___x_448_;
}
else
{
lean_object* v_val_449_; 
v_val_449_ = lean_ctor_get(v_fst_447_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v_fst_447_, 1);
if (lean_obj_tag(v_val_449_) == 0)
{
uint8_t v___x_450_; 
v___x_450_ = 0;
return v___x_450_;
}
else
{
lean_dec_ref_known(v_val_449_, 1);
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___boxed(lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_map_453_, lean_object* v_inst_454_, lean_object* v_key_455_, lean_object* v_value_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg(v_inst_451_, v_inst_452_, v_map_453_, v_inst_454_, v_key_455_, v_value_456_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry(lean_object* v_00_u03b1_459_, lean_object* v_00_u03b2_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_map_463_, lean_object* v_inst_464_, lean_object* v_key_465_, lean_object* v_value_466_){
_start:
{
lean_object* v_entries_467_; lean_object* v_indexes_468_; uint8_t v___x_469_; 
v_entries_467_ = lean_ctor_get(v_map_463_, 0);
lean_inc_ref(v_entries_467_);
v_indexes_468_ = lean_ctor_get(v_map_463_, 1);
lean_inc_ref(v_indexes_468_);
lean_dec_ref(v_map_463_);
lean_inc(v_key_465_);
lean_inc_ref(v_inst_462_);
lean_inc_ref(v_inst_461_);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_461_, v_inst_462_, v_indexes_468_, v_key_465_);
if (v___x_469_ == 0)
{
lean_dec_ref(v_indexes_468_);
lean_dec_ref(v_entries_467_);
lean_dec(v_value_466_);
lean_dec(v_key_465_);
lean_dec_ref(v_inst_464_);
lean_dec_ref(v_inst_462_);
lean_dec_ref(v_inst_461_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; lean_object* v___f_471_; lean_object* v___x_472_; size_t v_sz_473_; size_t v___x_474_; lean_object* v_entries_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___f_478_; size_t v_sz_479_; lean_object* v___x_480_; lean_object* v_fst_481_; 
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_461_, v_inst_462_, v_indexes_468_, v_key_465_);
lean_dec_ref(v_indexes_468_);
lean_inc_n(v___x_470_, 2);
v___f_471_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_471_, 0, v___x_470_);
lean_closure_set(v___f_471_, 1, v_entries_467_);
v___x_472_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_473_ = lean_array_size(v___x_470_);
v___x_474_ = ((size_t)0ULL);
v_entries_475_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_472_, v___x_470_, v___f_471_, v_sz_473_, v___x_474_, v___x_470_);
lean_dec(v___x_470_);
v___x_476_ = lean_box(0);
v___x_477_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_478_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_478_, 0, v_inst_464_);
lean_closure_set(v___f_478_, 1, v_value_466_);
lean_closure_set(v___f_478_, 2, v___x_477_);
lean_closure_set(v___f_478_, 3, v___x_476_);
v_sz_479_ = lean_array_size(v_entries_475_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_472_, v_entries_475_, v___f_478_, v_sz_479_, v___x_474_, v___x_477_);
v_fst_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_fst_481_);
lean_dec(v___x_480_);
if (lean_obj_tag(v_fst_481_) == 0)
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
else
{
lean_object* v_val_483_; 
v_val_483_ = lean_ctor_get(v_fst_481_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v_fst_481_, 1);
if (lean_obj_tag(v_val_483_) == 0)
{
uint8_t v___x_484_; 
v___x_484_ = 0;
return v___x_484_;
}
else
{
lean_dec_ref_known(v_val_483_, 1);
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___boxed(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_map_489_, lean_object* v_inst_490_, lean_object* v_key_491_, lean_object* v_value_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Std_Internal_IndexMultiMap_hasEntry(v_00_u03b1_485_, v_00_u03b2_486_, v_inst_487_, v_inst_488_, v_map_489_, v_inst_490_, v_key_491_, v_value_492_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f___redArg(lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_map_497_, lean_object* v_key_498_){
_start:
{
lean_object* v_entries_499_; lean_object* v_indexes_500_; uint8_t v___x_501_; 
v_entries_499_ = lean_ctor_get(v_map_497_, 0);
lean_inc_ref(v_entries_499_);
v_indexes_500_ = lean_ctor_get(v_map_497_, 1);
lean_inc_ref(v_indexes_500_);
lean_dec_ref(v_map_497_);
lean_inc(v_key_498_);
lean_inc_ref(v_inst_496_);
lean_inc_ref(v_inst_495_);
v___x_501_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_495_, v_inst_496_, v_indexes_500_, v_key_498_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec_ref(v_indexes_500_);
lean_dec_ref(v_entries_499_);
lean_dec(v_key_498_);
lean_dec_ref(v_inst_496_);
lean_dec_ref(v_inst_495_);
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v___x_503_; lean_object* v___f_504_; lean_object* v___x_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v_entries_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_495_, v_inst_496_, v_indexes_500_, v_key_498_);
lean_dec_ref(v_indexes_500_);
lean_inc_n(v___x_503_, 2);
v___f_504_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_504_, 0, v___x_503_);
lean_closure_set(v___f_504_, 1, v_entries_499_);
v___x_505_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_506_ = lean_array_size(v___x_503_);
v___x_507_ = ((size_t)0ULL);
v_entries_508_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_505_, v___x_503_, v___f_504_, v_sz_506_, v___x_507_, v___x_503_);
lean_dec(v___x_503_);
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
lean_object* v_entries_522_; lean_object* v_indexes_523_; uint8_t v___x_524_; 
v_entries_522_ = lean_ctor_get(v_map_520_, 0);
lean_inc_ref(v_entries_522_);
v_indexes_523_ = lean_ctor_get(v_map_520_, 1);
lean_inc_ref(v_indexes_523_);
lean_dec_ref(v_map_520_);
lean_inc(v_key_521_);
lean_inc_ref(v_inst_519_);
lean_inc_ref(v_inst_518_);
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_518_, v_inst_519_, v_indexes_523_, v_key_521_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec_ref(v_indexes_523_);
lean_dec_ref(v_entries_522_);
lean_dec(v_key_521_);
lean_dec_ref(v_inst_519_);
lean_dec_ref(v_inst_518_);
v___x_525_ = lean_box(0);
return v___x_525_;
}
else
{
lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_528_; size_t v_sz_529_; size_t v___x_530_; lean_object* v_entries_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_518_, v_inst_519_, v_indexes_523_, v_key_521_);
lean_dec_ref(v_indexes_523_);
lean_inc_n(v___x_526_, 2);
v___f_527_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_527_, 0, v___x_526_);
lean_closure_set(v___f_527_, 1, v_entries_522_);
v___x_528_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_529_ = lean_array_size(v___x_526_);
v___x_530_ = ((size_t)0ULL);
v_entries_531_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_528_, v___x_526_, v___f_527_, v_sz_529_, v___x_530_, v___x_526_);
lean_dec(v___x_526_);
v___x_532_ = lean_array_get_size(v_entries_531_);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_sub(v___x_532_, v___x_533_);
v___x_535_ = lean_nat_dec_lt(v___x_534_, v___x_532_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
lean_dec(v___x_534_);
lean_dec(v_entries_531_);
v___x_536_ = lean_box(0);
return v___x_536_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_array_fget(v_entries_531_, v___x_534_);
lean_dec(v___x_534_);
lean_dec(v_entries_531_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg(lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_map_541_, lean_object* v_key_542_, lean_object* v_d_543_){
_start:
{
lean_object* v_entries_544_; lean_object* v_indexes_545_; uint8_t v___x_546_; 
v_entries_544_ = lean_ctor_get(v_map_541_, 0);
v_indexes_545_ = lean_ctor_get(v_map_541_, 1);
lean_inc(v_key_542_);
lean_inc_ref(v_inst_540_);
lean_inc_ref(v_inst_539_);
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_539_, v_inst_540_, v_indexes_545_, v_key_542_);
if (v___x_546_ == 0)
{
lean_dec(v_key_542_);
lean_dec_ref(v_inst_540_);
lean_dec_ref(v_inst_539_);
lean_inc(v_d_543_);
return v_d_543_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_entry_549_; lean_object* v___x_550_; lean_object* v_snd_551_; 
v___x_547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_539_, v_inst_540_, v_indexes_545_, v_key_542_);
v___x_548_ = lean_unsigned_to_nat(0u);
v_entry_549_ = lean_array_fget(v___x_547_, v___x_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_array_fget_borrowed(v_entries_544_, v_entry_549_);
lean_dec(v_entry_549_);
v_snd_551_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_snd_551_);
return v_snd_551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg___boxed(lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_map_554_, lean_object* v_key_555_, lean_object* v_d_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_Internal_IndexMultiMap_getD___redArg(v_inst_552_, v_inst_553_, v_map_554_, v_key_555_, v_d_556_);
lean_dec(v_d_556_);
lean_dec_ref(v_map_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD(lean_object* v_00_u03b1_558_, lean_object* v_00_u03b2_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_map_562_, lean_object* v_key_563_, lean_object* v_d_564_){
_start:
{
lean_object* v_entries_565_; lean_object* v_indexes_566_; uint8_t v___x_567_; 
v_entries_565_ = lean_ctor_get(v_map_562_, 0);
v_indexes_566_ = lean_ctor_get(v_map_562_, 1);
lean_inc(v_key_563_);
lean_inc_ref(v_inst_561_);
lean_inc_ref(v_inst_560_);
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_560_, v_inst_561_, v_indexes_566_, v_key_563_);
if (v___x_567_ == 0)
{
lean_dec(v_key_563_);
lean_dec_ref(v_inst_561_);
lean_dec_ref(v_inst_560_);
lean_inc(v_d_564_);
return v_d_564_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_entry_570_; lean_object* v___x_571_; lean_object* v_snd_572_; 
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_560_, v_inst_561_, v_indexes_566_, v_key_563_);
v___x_569_ = lean_unsigned_to_nat(0u);
v_entry_570_ = lean_array_fget(v___x_568_, v___x_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_array_fget_borrowed(v_entries_565_, v_entry_570_);
lean_dec(v_entry_570_);
v_snd_572_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_snd_572_);
return v_snd_572_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___boxed(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_map_577_, lean_object* v_key_578_, lean_object* v_d_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_Internal_IndexMultiMap_getD(v_00_u03b1_573_, v_00_u03b2_574_, v_inst_575_, v_inst_576_, v_map_577_, v_key_578_, v_d_579_);
lean_dec(v_d_579_);
lean_dec_ref(v_map_577_);
return v_res_580_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_584_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2));
v___x_585_ = lean_unsigned_to_nat(14u);
v___x_586_ = lean_unsigned_to_nat(22u);
v___x_587_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1));
v___x_588_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0));
v___x_589_ = l_mkPanicMessageWithDecl(v___x_588_, v___x_587_, v___x_586_, v___x_585_, v___x_584_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg(lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_map_593_, lean_object* v_key_594_){
_start:
{
lean_object* v_entries_595_; lean_object* v_indexes_596_; uint8_t v___x_597_; 
v_entries_595_ = lean_ctor_get(v_map_593_, 0);
v_indexes_596_ = lean_ctor_get(v_map_593_, 1);
lean_inc(v_key_594_);
lean_inc_ref(v_inst_591_);
lean_inc_ref(v_inst_590_);
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_590_, v_inst_591_, v_indexes_596_, v_key_594_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_key_594_);
lean_dec_ref(v_inst_591_);
lean_dec_ref(v_inst_590_);
v___x_598_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_599_ = l_panic___redArg(v_inst_592_, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_entry_602_; lean_object* v___x_603_; lean_object* v_snd_604_; 
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_590_, v_inst_591_, v_indexes_596_, v_key_594_);
v___x_601_ = lean_unsigned_to_nat(0u);
v_entry_602_ = lean_array_fget(v___x_600_, v___x_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_array_fget_borrowed(v_entries_595_, v_entry_602_);
lean_dec(v_entry_602_);
v_snd_604_ = lean_ctor_get(v___x_603_, 1);
lean_inc(v_snd_604_);
return v_snd_604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___boxed(lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_map_608_, lean_object* v_key_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_Internal_IndexMultiMap_get_x21___redArg(v_inst_605_, v_inst_606_, v_inst_607_, v_map_608_, v_key_609_);
lean_dec_ref(v_map_608_);
lean_dec(v_inst_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21(lean_object* v_00_u03b1_611_, lean_object* v_00_u03b2_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_map_616_, lean_object* v_key_617_){
_start:
{
lean_object* v_entries_618_; lean_object* v_indexes_619_; uint8_t v___x_620_; 
v_entries_618_ = lean_ctor_get(v_map_616_, 0);
v_indexes_619_ = lean_ctor_get(v_map_616_, 1);
lean_inc(v_key_617_);
lean_inc_ref(v_inst_614_);
lean_inc_ref(v_inst_613_);
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_613_, v_inst_614_, v_indexes_619_, v_key_617_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v_key_617_);
lean_dec_ref(v_inst_614_);
lean_dec_ref(v_inst_613_);
v___x_621_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_622_ = l_panic___redArg(v_inst_615_, v___x_621_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_entry_625_; lean_object* v___x_626_; lean_object* v_snd_627_; 
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_613_, v_inst_614_, v_indexes_619_, v_key_617_);
v___x_624_ = lean_unsigned_to_nat(0u);
v_entry_625_ = lean_array_fget(v___x_623_, v___x_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_array_fget_borrowed(v_entries_618_, v_entry_625_);
lean_dec(v_entry_625_);
v_snd_627_ = lean_ctor_get(v___x_626_, 1);
lean_inc(v_snd_627_);
return v_snd_627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___boxed(lean_object* v_00_u03b1_628_, lean_object* v_00_u03b2_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_map_633_, lean_object* v_key_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_Internal_IndexMultiMap_get_x21(v_00_u03b1_628_, v_00_u03b2_629_, v_inst_630_, v_inst_631_, v_inst_632_, v_map_633_, v_key_634_);
lean_dec_ref(v_map_633_);
lean_dec(v_inst_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(lean_object* v_x_636_, lean_object* v_h__1_637_, lean_object* v_h__2_638_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec(v_h__1_637_);
v___x_639_ = lean_box(0);
v___x_640_ = lean_apply_1(v_h__2_638_, v___x_639_);
return v___x_640_;
}
else
{
lean_object* v_val_641_; lean_object* v___x_642_; 
lean_dec(v_h__2_638_);
v_val_641_ = lean_ctor_get(v_x_636_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v_x_636_, 1);
v___x_642_ = lean_apply_1(v_h__1_637_, v_val_641_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter(lean_object* v_motive_643_, lean_object* v_x_644_, lean_object* v_h__1_645_, lean_object* v_h__2_646_){
_start:
{
if (lean_obj_tag(v_x_644_) == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v_h__1_645_);
v___x_647_ = lean_box(0);
v___x_648_ = lean_apply_1(v_h__2_646_, v___x_647_);
return v___x_648_;
}
else
{
lean_object* v_val_649_; lean_object* v___x_650_; 
lean_dec(v_h__2_646_);
v_val_649_ = lean_ctor_get(v_x_644_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v_x_644_, 1);
v___x_650_ = lean_apply_1(v_h__1_645_, v_val_649_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(lean_object* v_i_651_, lean_object* v_x_652_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_mk_empty_array_with_capacity(v___x_653_);
v___x_655_ = lean_array_push(v___x_654_, v_i_651_);
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
else
{
lean_object* v_val_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
v_val_657_ = lean_ctor_get(v_x_652_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_665_ == 0)
{
v___x_659_ = v_x_652_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_val_657_);
lean_dec(v_x_652_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_array_push(v_val_657_, v_i_651_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg(lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_map_668_, lean_object* v_key_669_, lean_object* v_value_670_){
_start:
{
lean_object* v_entries_671_; lean_object* v_indexes_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_684_; 
v_entries_671_ = lean_ctor_get(v_map_668_, 0);
v_indexes_672_ = lean_ctor_get(v_map_668_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_map_668_);
if (v_isSharedCheck_684_ == 0)
{
v___x_674_ = v_map_668_;
v_isShared_675_ = v_isSharedCheck_684_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_indexes_672_);
lean_inc(v_entries_671_);
lean_dec(v_map_668_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_684_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_i_676_; lean_object* v_f_677_; lean_object* v___x_678_; lean_object* v_entries_679_; lean_object* v_indexes_680_; lean_object* v___x_682_; 
v_i_676_ = lean_array_get_size(v_entries_671_);
v_f_677_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_677_, 0, v_i_676_);
lean_inc(v_key_669_);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v_key_669_);
lean_ctor_set(v___x_678_, 1, v_value_670_);
v_entries_679_ = lean_array_push(v_entries_671_, v___x_678_);
v_indexes_680_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_666_, v_inst_667_, v_indexes_672_, v_key_669_, v_f_677_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v_indexes_680_);
lean_ctor_set(v___x_674_, 0, v_entries_679_);
v___x_682_ = v___x_674_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_entries_679_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_indexes_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert(lean_object* v_00_u03b1_685_, lean_object* v_00_u03b2_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_map_691_, lean_object* v_key_692_, lean_object* v_value_693_){
_start:
{
lean_object* v_entries_694_; lean_object* v_indexes_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_707_; 
v_entries_694_ = lean_ctor_get(v_map_691_, 0);
v_indexes_695_ = lean_ctor_get(v_map_691_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_map_691_);
if (v_isSharedCheck_707_ == 0)
{
v___x_697_ = v_map_691_;
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_indexes_695_);
lean_inc(v_entries_694_);
lean_dec(v_map_691_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_i_699_; lean_object* v_f_700_; lean_object* v___x_701_; lean_object* v_entries_702_; lean_object* v_indexes_703_; lean_object* v___x_705_; 
v_i_699_ = lean_array_get_size(v_entries_694_);
v_f_700_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_700_, 0, v_i_699_);
lean_inc(v_key_692_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_key_692_);
lean_ctor_set(v___x_701_, 1, v_value_693_);
v_entries_702_ = lean_array_push(v_entries_694_, v___x_701_);
v_indexes_703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_687_, v_inst_688_, v_indexes_695_, v_key_692_, v_f_700_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v_indexes_703_);
lean_ctor_set(v___x_697_, 0, v_entries_702_);
v___x_705_ = v___x_697_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_entries_702_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_indexes_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1(lean_object* v_key_708_, lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v_x1_711_, lean_object* v_x2_712_){
_start:
{
lean_object* v_entries_713_; lean_object* v_indexes_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_726_; 
v_entries_713_ = lean_ctor_get(v_x1_711_, 0);
v_indexes_714_ = lean_ctor_get(v_x1_711_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x1_711_);
if (v_isSharedCheck_726_ == 0)
{
v___x_716_ = v_x1_711_;
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_indexes_714_);
lean_inc(v_entries_713_);
lean_dec(v_x1_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_i_718_; lean_object* v_f_719_; lean_object* v___x_720_; lean_object* v_entries_721_; lean_object* v_indexes_722_; lean_object* v___x_724_; 
v_i_718_ = lean_array_get_size(v_entries_713_);
v_f_719_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_719_, 0, v_i_718_);
lean_inc(v_key_708_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_key_708_);
lean_ctor_set(v___x_720_, 1, v_x2_712_);
v_entries_721_ = lean_array_push(v_entries_713_, v___x_720_);
v_indexes_722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_709_, v_inst_710_, v_indexes_714_, v_key_708_, v_f_719_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v_indexes_722_);
lean_ctor_set(v___x_716_, 0, v_entries_721_);
v___x_724_ = v___x_716_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_entries_721_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_indexes_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg(lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_map_729_, lean_object* v_key_730_, lean_object* v_values_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_array_get_size(v_values_731_);
v___x_734_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_735_ = lean_nat_dec_lt(v___x_732_, v___x_733_);
if (v___x_735_ == 0)
{
lean_dec_ref(v_values_731_);
lean_dec(v_key_730_);
lean_dec_ref(v_inst_728_);
lean_dec_ref(v_inst_727_);
return v_map_729_;
}
else
{
lean_object* v___f_736_; size_t v___x_737_; size_t v___x_738_; lean_object* v___x_739_; 
v___f_736_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_736_, 0, v_key_730_);
lean_closure_set(v___f_736_, 1, v_inst_727_);
lean_closure_set(v___f_736_, 2, v_inst_728_);
v___x_737_ = ((size_t)0ULL);
v___x_738_ = lean_usize_of_nat(v___x_733_);
v___x_739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_734_, v___f_736_, v_values_731_, v___x_737_, v___x_738_, v_map_729_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany(lean_object* v_00_u03b1_740_, lean_object* v_00_u03b2_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_map_746_, lean_object* v_key_747_, lean_object* v_values_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_array_get_size(v_values_748_);
v___x_751_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_752_ = lean_nat_dec_lt(v___x_749_, v___x_750_);
if (v___x_752_ == 0)
{
lean_dec_ref(v_values_748_);
lean_dec(v_key_747_);
lean_dec_ref(v_inst_743_);
lean_dec_ref(v_inst_742_);
return v_map_746_;
}
else
{
lean_object* v___f_753_; size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; 
v___f_753_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_753_, 0, v_key_747_);
lean_closure_set(v___f_753_, 1, v_inst_742_);
lean_closure_set(v___f_753_, 2, v_inst_743_);
v___x_754_ = ((size_t)0ULL);
v___x_755_ = lean_usize_of_nat(v___x_750_);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_751_, v___f_753_, v_values_748_, v___x_754_, v___x_755_, v_map_746_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___redArg(){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___redArg___boxed(lean_object* v___dummy_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v_res_760_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___closed__0(void){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_inst_764_, lean_object* v_inst_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___boxed(lean_object* v_00_u03b1_767_, lean_object* v_00_u03b2_768_, lean_object* v_inst_769_, lean_object* v_inst_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_Internal_IndexMultiMap_empty(v_00_u03b1_767_, v_00_u03b2_768_, v_inst_769_, v_inst_770_);
lean_dec_ref(v_inst_770_);
lean_dec_ref(v_inst_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1(lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_acc_774_, lean_object* v_x_775_){
_start:
{
lean_object* v_fst_776_; lean_object* v_entries_777_; lean_object* v_indexes_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_789_; 
v_fst_776_ = lean_ctor_get(v_x_775_, 0);
lean_inc(v_fst_776_);
v_entries_777_ = lean_ctor_get(v_acc_774_, 0);
v_indexes_778_ = lean_ctor_get(v_acc_774_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_acc_774_);
if (v_isSharedCheck_789_ == 0)
{
v___x_780_ = v_acc_774_;
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_indexes_778_);
lean_inc(v_entries_777_);
lean_dec(v_acc_774_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_i_782_; lean_object* v_f_783_; lean_object* v_entries_784_; lean_object* v_indexes_785_; lean_object* v___x_787_; 
v_i_782_ = lean_array_get_size(v_entries_777_);
v_f_783_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_783_, 0, v_i_782_);
v_entries_784_ = lean_array_push(v_entries_777_, v_x_775_);
v_indexes_785_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_772_, v_inst_773_, v_indexes_778_, v_fst_776_, v_f_783_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 1, v_indexes_785_);
lean_ctor_set(v___x_780_, 0, v_entries_784_);
v___x_787_ = v___x_780_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_entries_784_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_indexes_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg(lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_pairs_792_){
_start:
{
lean_object* v___f_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___f_793_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_793_, 0, v_inst_790_);
lean_closure_set(v___f_793_, 1, v_inst_791_);
v___x_794_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_795_ = l_List_foldl___redArg(v___f_793_, v___x_794_, v_pairs_792_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList(lean_object* v_00_u03b1_796_, lean_object* v_00_u03b2_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_pairs_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_Internal_IndexMultiMap_ofList___redArg(v_inst_798_, v_inst_799_, v_pairs_802_);
return v___x_803_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains___redArg(lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_map_806_, lean_object* v_key_807_){
_start:
{
lean_object* v_indexes_808_; uint8_t v___x_809_; 
v_indexes_808_ = lean_ctor_get(v_map_806_, 1);
v___x_809_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_804_, v_inst_805_, v_indexes_808_, v_key_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___redArg___boxed(lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_map_812_, lean_object* v_key_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_Std_Internal_IndexMultiMap_contains___redArg(v_inst_810_, v_inst_811_, v_map_812_, v_key_813_);
lean_dec_ref(v_map_812_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_map_820_, lean_object* v_key_821_){
_start:
{
lean_object* v_indexes_822_; uint8_t v___x_823_; 
v_indexes_822_ = lean_ctor_get(v_map_820_, 1);
v___x_823_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_818_, v_inst_819_, v_indexes_822_, v_key_821_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___boxed(lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_map_828_, lean_object* v_key_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_Std_Internal_IndexMultiMap_contains(v_00_u03b1_824_, v_00_u03b2_825_, v_inst_826_, v_inst_827_, v_map_828_, v_key_829_);
lean_dec_ref(v_map_828_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg___lam__1(lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_key_834_, lean_object* v_f_835_, lean_object* v_x1_836_, lean_object* v_x2_837_){
_start:
{
lean_object* v_fst_838_; lean_object* v_snd_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_864_; 
v_fst_838_ = lean_ctor_get(v_x2_837_, 0);
v_snd_839_ = lean_ctor_get(v_x2_837_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_x2_837_);
if (v_isSharedCheck_864_ == 0)
{
v___x_841_ = v_x2_837_;
v_isShared_842_ = v_isSharedCheck_864_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_snd_839_);
lean_inc(v_fst_838_);
lean_dec(v_x2_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_864_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___y_844_; lean_object* v___x_861_; uint8_t v___x_862_; 
lean_inc_ref(v_inst_832_);
lean_inc(v_fst_838_);
v___x_861_ = lean_apply_2(v_inst_832_, v_fst_838_, v_key_834_);
v___x_862_ = lean_unbox(v___x_861_);
if (v___x_862_ == 0)
{
lean_dec(v_f_835_);
v___y_844_ = v_snd_839_;
goto v___jp_843_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = lean_apply_1(v_f_835_, v_snd_839_);
v___y_844_ = v___x_863_;
goto v___jp_843_;
}
v___jp_843_:
{
lean_object* v_entries_845_; lean_object* v_indexes_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_860_; 
v_entries_845_ = lean_ctor_get(v_x1_836_, 0);
v_indexes_846_ = lean_ctor_get(v_x1_836_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_x1_836_);
if (v_isSharedCheck_860_ == 0)
{
v___x_848_ = v_x1_836_;
v_isShared_849_ = v_isSharedCheck_860_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_indexes_846_);
lean_inc(v_entries_845_);
lean_dec(v_x1_836_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_860_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_i_850_; lean_object* v_f_851_; lean_object* v___x_853_; 
v_i_850_ = lean_array_get_size(v_entries_845_);
v_f_851_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_851_, 0, v_i_850_);
lean_inc(v_fst_838_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___y_844_);
v___x_853_ = v___x_841_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_fst_838_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___y_844_);
v___x_853_ = v_reuseFailAlloc_859_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v_entries_854_; lean_object* v_indexes_855_; lean_object* v___x_857_; 
v_entries_854_ = lean_array_push(v_entries_845_, v___x_853_);
v_indexes_855_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_832_, v_inst_833_, v_indexes_846_, v_fst_838_, v_f_851_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v_indexes_855_);
lean_ctor_set(v___x_848_, 0, v_entries_854_);
v___x_857_ = v___x_848_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_entries_854_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_indexes_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg(lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_map_867_, lean_object* v_key_868_, lean_object* v_f_869_){
_start:
{
uint8_t v___x_870_; 
lean_inc(v_key_868_);
lean_inc_ref(v_inst_866_);
lean_inc_ref(v_inst_865_);
v___x_870_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_865_, v_inst_866_, v_key_868_, v_map_867_);
if (v___x_870_ == 0)
{
lean_dec(v_f_869_);
lean_dec(v_key_868_);
lean_dec_ref(v_inst_866_);
lean_dec_ref(v_inst_865_);
return v_map_867_;
}
else
{
lean_object* v_entries_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; 
v_entries_871_ = lean_ctor_get(v_map_867_, 0);
lean_inc_ref(v_entries_871_);
lean_dec_ref(v_map_867_);
v___x_872_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_array_get_size(v_entries_871_);
v___x_875_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_876_ = lean_nat_dec_lt(v___x_873_, v___x_874_);
if (v___x_876_ == 0)
{
lean_dec_ref(v_entries_871_);
lean_dec(v_f_869_);
lean_dec(v_key_868_);
lean_dec_ref(v_inst_866_);
lean_dec_ref(v_inst_865_);
return v___x_872_;
}
else
{
lean_object* v___f_877_; size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; 
v___f_877_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_877_, 0, v_inst_865_);
lean_closure_set(v___f_877_, 1, v_inst_866_);
lean_closure_set(v___f_877_, 2, v_key_868_);
lean_closure_set(v___f_877_, 3, v_f_869_);
v___x_878_ = ((size_t)0ULL);
v___x_879_ = lean_usize_of_nat(v___x_874_);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_875_, v___f_877_, v_entries_871_, v___x_878_, v___x_879_, v___x_872_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_map_887_, lean_object* v_key_888_, lean_object* v_f_889_){
_start:
{
uint8_t v___x_890_; 
lean_inc(v_key_888_);
lean_inc_ref(v_inst_884_);
lean_inc_ref(v_inst_883_);
v___x_890_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_883_, v_inst_884_, v_key_888_, v_map_887_);
if (v___x_890_ == 0)
{
lean_dec(v_f_889_);
lean_dec(v_key_888_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_inst_883_);
return v_map_887_;
}
else
{
lean_object* v_entries_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_entries_891_ = lean_ctor_get(v_map_887_, 0);
lean_inc_ref(v_entries_891_);
lean_dec_ref(v_map_887_);
v___x_892_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_array_get_size(v_entries_891_);
v___x_895_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_896_ = lean_nat_dec_lt(v___x_893_, v___x_894_);
if (v___x_896_ == 0)
{
lean_dec_ref(v_entries_891_);
lean_dec(v_f_889_);
lean_dec(v_key_888_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_inst_883_);
return v___x_892_;
}
else
{
lean_object* v___f_897_; size_t v___x_898_; size_t v___x_899_; lean_object* v___x_900_; 
v___f_897_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_897_, 0, v_inst_883_);
lean_closure_set(v___f_897_, 1, v_inst_884_);
lean_closure_set(v___f_897_, 2, v_key_888_);
lean_closure_set(v___f_897_, 3, v_f_889_);
v___x_898_ = ((size_t)0ULL);
v___x_899_ = lean_usize_of_nat(v___x_894_);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_895_, v___f_897_, v_entries_891_, v___x_898_, v___x_899_, v___x_892_);
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast___redArg(lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v_map_903_, lean_object* v_key_904_, lean_object* v_value_905_){
_start:
{
lean_object* v_entries_906_; lean_object* v_indexes_907_; uint8_t v___x_908_; 
v_entries_906_ = lean_ctor_get(v_map_903_, 0);
v_indexes_907_ = lean_ctor_get(v_map_903_, 1);
lean_inc(v_key_904_);
lean_inc_ref(v_inst_902_);
lean_inc_ref(v_inst_901_);
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_901_, v_inst_902_, v_indexes_907_, v_key_904_);
if (v___x_908_ == 0)
{
lean_dec(v_value_905_);
lean_dec(v_key_904_);
lean_dec_ref(v_inst_902_);
lean_dec_ref(v_inst_901_);
return v_map_903_;
}
else
{
lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_922_; 
lean_inc_ref(v_indexes_907_);
lean_inc_ref(v_entries_906_);
v_isSharedCheck_922_ = !lean_is_exclusive(v_map_903_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; lean_object* v_unused_924_; 
v_unused_923_ = lean_ctor_get(v_map_903_, 1);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_map_903_, 0);
lean_dec(v_unused_924_);
v___x_910_ = v_map_903_;
v_isShared_911_ = v_isSharedCheck_922_;
goto v_resetjp_909_;
}
else
{
lean_dec(v_map_903_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_922_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_idxs_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v_lastIdx_916_; lean_object* v___x_917_; lean_object* v_entries_918_; lean_object* v___x_920_; 
lean_inc(v_key_904_);
v_idxs_912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_901_, v_inst_902_, v_indexes_907_, v_key_904_);
v___x_913_ = lean_array_get_size(v_idxs_912_);
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_nat_sub(v___x_913_, v___x_914_);
v_lastIdx_916_ = lean_array_fget(v_idxs_912_, v___x_915_);
lean_dec(v___x_915_);
lean_dec(v_idxs_912_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_key_904_);
lean_ctor_set(v___x_917_, 1, v_value_905_);
v_entries_918_ = lean_array_fset(v_entries_906_, v_lastIdx_916_, v___x_917_);
lean_dec(v_lastIdx_916_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v_entries_918_);
v___x_920_ = v___x_910_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_entries_918_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_indexes_907_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_map_929_, lean_object* v_key_930_, lean_object* v_value_931_){
_start:
{
lean_object* v_entries_932_; lean_object* v_indexes_933_; uint8_t v___x_934_; 
v_entries_932_ = lean_ctor_get(v_map_929_, 0);
v_indexes_933_ = lean_ctor_get(v_map_929_, 1);
lean_inc(v_key_930_);
lean_inc_ref(v_inst_928_);
lean_inc_ref(v_inst_927_);
v___x_934_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_927_, v_inst_928_, v_indexes_933_, v_key_930_);
if (v___x_934_ == 0)
{
lean_dec(v_value_931_);
lean_dec(v_key_930_);
lean_dec_ref(v_inst_928_);
lean_dec_ref(v_inst_927_);
return v_map_929_;
}
else
{
lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_948_; 
lean_inc_ref(v_indexes_933_);
lean_inc_ref(v_entries_932_);
v_isSharedCheck_948_ = !lean_is_exclusive(v_map_929_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; lean_object* v_unused_950_; 
v_unused_949_ = lean_ctor_get(v_map_929_, 1);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v_map_929_, 0);
lean_dec(v_unused_950_);
v___x_936_ = v_map_929_;
v_isShared_937_ = v_isSharedCheck_948_;
goto v_resetjp_935_;
}
else
{
lean_dec(v_map_929_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_948_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_idxs_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_lastIdx_942_; lean_object* v___x_943_; lean_object* v_entries_944_; lean_object* v___x_946_; 
lean_inc(v_key_930_);
v_idxs_938_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_927_, v_inst_928_, v_indexes_933_, v_key_930_);
v___x_939_ = lean_array_get_size(v_idxs_938_);
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = lean_nat_sub(v___x_939_, v___x_940_);
v_lastIdx_942_ = lean_array_fget(v_idxs_938_, v___x_941_);
lean_dec(v___x_941_);
lean_dec(v_idxs_938_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_key_930_);
lean_ctor_set(v___x_943_, 1, v_value_931_);
v_entries_944_ = lean_array_fset(v_entries_932_, v_lastIdx_942_, v___x_943_);
lean_dec(v_lastIdx_942_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_entries_944_);
v___x_946_ = v___x_936_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_entries_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_indexes_933_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object* v_inst_951_, lean_object* v_key_952_, lean_object* v_inst_953_, lean_object* v_x1_954_, lean_object* v_x2_955_){
_start:
{
lean_object* v_fst_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_fst_956_ = lean_ctor_get(v_x2_955_, 0);
lean_inc_n(v_fst_956_, 2);
lean_inc_ref(v_inst_951_);
v___x_957_ = lean_apply_2(v_inst_951_, v_key_952_, v_fst_956_);
v___x_958_ = lean_unbox(v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v_entries_959_; lean_object* v_indexes_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_971_; 
v_entries_959_ = lean_ctor_get(v_x1_954_, 0);
v_indexes_960_ = lean_ctor_get(v_x1_954_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v_x1_954_);
if (v_isSharedCheck_971_ == 0)
{
v___x_962_ = v_x1_954_;
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_indexes_960_);
lean_inc(v_entries_959_);
lean_dec(v_x1_954_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_i_964_; lean_object* v_f_965_; lean_object* v_entries_966_; lean_object* v_indexes_967_; lean_object* v___x_969_; 
v_i_964_ = lean_array_get_size(v_entries_959_);
v_f_965_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_965_, 0, v_i_964_);
v_entries_966_ = lean_array_push(v_entries_959_, v_x2_955_);
v_indexes_967_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_951_, v_inst_953_, v_indexes_960_, v_fst_956_, v_f_965_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v_indexes_967_);
lean_ctor_set(v___x_962_, 0, v_entries_966_);
v___x_969_ = v___x_962_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_entries_966_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_indexes_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
lean_dec(v_fst_956_);
lean_dec_ref(v_x2_955_);
lean_dec_ref(v_inst_953_);
lean_dec_ref(v_inst_951_);
return v_x1_954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_map_974_, lean_object* v_key_975_){
_start:
{
uint8_t v___x_976_; 
lean_inc(v_key_975_);
lean_inc_ref(v_inst_973_);
lean_inc_ref(v_inst_972_);
v___x_976_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_972_, v_inst_973_, v_key_975_, v_map_974_);
if (v___x_976_ == 0)
{
lean_dec(v_key_975_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
return v_map_974_;
}
else
{
lean_object* v_entries_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v_entries_977_ = lean_ctor_get(v_map_974_, 0);
lean_inc_ref(v_entries_977_);
lean_dec_ref(v_map_974_);
v___x_978_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_array_get_size(v_entries_977_);
v___x_981_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_982_ = lean_nat_dec_lt(v___x_979_, v___x_980_);
if (v___x_982_ == 0)
{
lean_dec_ref(v_entries_977_);
lean_dec(v_key_975_);
lean_dec_ref(v_inst_973_);
lean_dec_ref(v_inst_972_);
return v___x_978_;
}
else
{
lean_object* v___f_983_; size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
v___f_983_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 5, 3);
lean_closure_set(v___f_983_, 0, v_inst_972_);
lean_closure_set(v___f_983_, 1, v_key_975_);
lean_closure_set(v___f_983_, 2, v_inst_973_);
v___x_984_ = ((size_t)0ULL);
v___x_985_ = lean_usize_of_nat(v___x_980_);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_981_, v___f_983_, v_entries_977_, v___x_984_, v___x_985_, v___x_978_);
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object* v_00_u03b1_987_, lean_object* v_00_u03b2_988_, lean_object* v_inst_989_, lean_object* v_inst_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_map_993_, lean_object* v_key_994_){
_start:
{
uint8_t v___x_995_; 
lean_inc(v_key_994_);
lean_inc_ref(v_inst_990_);
lean_inc_ref(v_inst_989_);
v___x_995_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_989_, v_inst_990_, v_key_994_, v_map_993_);
if (v___x_995_ == 0)
{
lean_dec(v_key_994_);
lean_dec_ref(v_inst_990_);
lean_dec_ref(v_inst_989_);
return v_map_993_;
}
else
{
lean_object* v_entries_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_entries_996_ = lean_ctor_get(v_map_993_, 0);
lean_inc_ref(v_entries_996_);
lean_dec_ref(v_map_993_);
v___x_997_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_array_get_size(v_entries_996_);
v___x_1000_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1001_ = lean_nat_dec_lt(v___x_998_, v___x_999_);
if (v___x_1001_ == 0)
{
lean_dec_ref(v_entries_996_);
lean_dec(v_key_994_);
lean_dec_ref(v_inst_990_);
lean_dec_ref(v_inst_989_);
return v___x_997_;
}
else
{
lean_object* v___f_1002_; size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v___f_1002_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1002_, 0, v_inst_989_);
lean_closure_set(v___f_1002_, 1, v_key_994_);
lean_closure_set(v___f_1002_, 2, v_inst_990_);
v___x_1003_ = ((size_t)0ULL);
v___x_1004_ = lean_usize_of_nat(v___x_999_);
v___x_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1000_, v___f_1002_, v_entries_996_, v___x_1003_, v___x_1004_, v___x_997_);
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1(lean_object* v_inst_1006_, lean_object* v_keys_1007_, lean_object* v_inst_1008_, lean_object* v_x1_1009_, lean_object* v_x2_1010_){
_start:
{
lean_object* v_fst_1011_; uint8_t v___x_1012_; 
v_fst_1011_ = lean_ctor_get(v_x2_1010_, 0);
lean_inc_n(v_fst_1011_, 2);
lean_inc_ref(v_inst_1006_);
v___x_1012_ = l_Array_contains___redArg(v_inst_1006_, v_keys_1007_, v_fst_1011_);
if (v___x_1012_ == 0)
{
lean_object* v_entries_1013_; lean_object* v_indexes_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1025_; 
v_entries_1013_ = lean_ctor_get(v_x1_1009_, 0);
v_indexes_1014_ = lean_ctor_get(v_x1_1009_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_x1_1009_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1016_ = v_x1_1009_;
v_isShared_1017_ = v_isSharedCheck_1025_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_indexes_1014_);
lean_inc(v_entries_1013_);
lean_dec(v_x1_1009_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1025_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_i_1018_; lean_object* v_f_1019_; lean_object* v_entries_1020_; lean_object* v_indexes_1021_; lean_object* v___x_1023_; 
v_i_1018_ = lean_array_get_size(v_entries_1013_);
v_f_1019_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1019_, 0, v_i_1018_);
v_entries_1020_ = lean_array_push(v_entries_1013_, v_x2_1010_);
v_indexes_1021_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1006_, v_inst_1008_, v_indexes_1014_, v_fst_1011_, v_f_1019_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v_indexes_1021_);
lean_ctor_set(v___x_1016_, 0, v_entries_1020_);
v___x_1023_ = v___x_1016_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_entries_1020_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_indexes_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
else
{
lean_dec(v_fst_1011_);
lean_dec_ref(v_x2_1010_);
lean_dec_ref(v_inst_1008_);
lean_dec_ref(v_inst_1006_);
return v_x1_1009_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg(lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_map_1028_, lean_object* v_keys_1029_){
_start:
{
lean_object* v_entries_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_entries_1030_ = lean_ctor_get(v_map_1028_, 0);
lean_inc_ref(v_entries_1030_);
lean_dec_ref(v_map_1028_);
v___x_1031_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_array_get_size(v_entries_1030_);
v___x_1034_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1035_ = lean_nat_dec_lt(v___x_1032_, v___x_1033_);
if (v___x_1035_ == 0)
{
lean_dec_ref(v_entries_1030_);
lean_dec_ref(v_keys_1029_);
lean_dec_ref(v_inst_1027_);
lean_dec_ref(v_inst_1026_);
return v___x_1031_;
}
else
{
lean_object* v___f_1036_; size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___f_1036_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1036_, 0, v_inst_1026_);
lean_closure_set(v___f_1036_, 1, v_keys_1029_);
lean_closure_set(v___f_1036_, 2, v_inst_1027_);
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = lean_usize_of_nat(v___x_1033_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1034_, v___f_1036_, v_entries_1030_, v___x_1037_, v___x_1038_, v___x_1031_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany(lean_object* v_00_u03b1_1040_, lean_object* v_00_u03b2_1041_, lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_map_1046_, lean_object* v_keys_1047_){
_start:
{
lean_object* v_entries_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_entries_1048_ = lean_ctor_get(v_map_1046_, 0);
lean_inc_ref(v_entries_1048_);
lean_dec_ref(v_map_1046_);
v___x_1049_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_array_get_size(v_entries_1048_);
v___x_1052_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1053_ = lean_nat_dec_lt(v___x_1050_, v___x_1051_);
if (v___x_1053_ == 0)
{
lean_dec_ref(v_entries_1048_);
lean_dec_ref(v_keys_1047_);
lean_dec_ref(v_inst_1043_);
lean_dec_ref(v_inst_1042_);
return v___x_1049_;
}
else
{
lean_object* v___f_1054_; size_t v___x_1055_; size_t v___x_1056_; lean_object* v___x_1057_; 
v___f_1054_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1054_, 0, v_inst_1042_);
lean_closure_set(v___f_1054_, 1, v_keys_1047_);
lean_closure_set(v___f_1054_, 2, v_inst_1043_);
v___x_1055_ = ((size_t)0ULL);
v___x_1056_ = lean_usize_of_nat(v___x_1051_);
v___x_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1052_, v___f_1054_, v_entries_1048_, v___x_1055_, v___x_1056_, v___x_1049_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg(lean_object* v_map_1058_){
_start:
{
lean_object* v_entries_1059_; lean_object* v___x_1060_; 
v_entries_1059_ = lean_ctor_get(v_map_1058_, 0);
v___x_1060_ = lean_array_get_size(v_entries_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg___boxed(lean_object* v_map_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Std_Internal_IndexMultiMap_size___redArg(v_map_1061_);
lean_dec_ref(v_map_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size(lean_object* v_00_u03b1_1063_, lean_object* v_00_u03b2_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_map_1067_){
_start:
{
lean_object* v_entries_1068_; lean_object* v___x_1069_; 
v_entries_1068_ = lean_ctor_get(v_map_1067_, 0);
v___x_1069_ = lean_array_get_size(v_entries_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___boxed(lean_object* v_00_u03b1_1070_, lean_object* v_00_u03b2_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_map_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Std_Internal_IndexMultiMap_size(v_00_u03b1_1070_, v_00_u03b2_1071_, v_inst_1072_, v_inst_1073_, v_map_1074_);
lean_dec_ref(v_map_1074_);
lean_dec_ref(v_inst_1073_);
lean_dec_ref(v_inst_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty___redArg(lean_object* v_map_1076_){
_start:
{
lean_object* v_entries_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_entries_1077_ = lean_ctor_get(v_map_1076_, 0);
v___x_1078_ = lean_array_get_size(v_entries_1077_);
v___x_1079_ = lean_unsigned_to_nat(0u);
v___x_1080_ = lean_nat_dec_eq(v___x_1078_, v___x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___redArg___boxed(lean_object* v_map_1081_){
_start:
{
uint8_t v_res_1082_; lean_object* v_r_1083_; 
v_res_1082_ = l_Std_Internal_IndexMultiMap_isEmpty___redArg(v_map_1081_);
lean_dec_ref(v_map_1081_);
v_r_1083_ = lean_box(v_res_1082_);
return v_r_1083_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty(lean_object* v_00_u03b1_1084_, lean_object* v_00_u03b2_1085_, lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v_map_1088_){
_start:
{
lean_object* v_entries_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_entries_1089_ = lean_ctor_get(v_map_1088_, 0);
v___x_1090_ = lean_array_get_size(v_entries_1089_);
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = lean_nat_dec_eq(v___x_1090_, v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___boxed(lean_object* v_00_u03b1_1093_, lean_object* v_00_u03b2_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_map_1097_){
_start:
{
uint8_t v_res_1098_; lean_object* v_r_1099_; 
v_res_1098_ = l_Std_Internal_IndexMultiMap_isEmpty(v_00_u03b1_1093_, v_00_u03b2_1094_, v_inst_1095_, v_inst_1096_, v_map_1097_);
lean_dec_ref(v_map_1097_);
lean_dec_ref(v_inst_1096_);
lean_dec_ref(v_inst_1095_);
v_r_1099_ = lean_box(v_res_1098_);
return v_r_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg(lean_object* v_map_1100_){
_start:
{
lean_object* v_entries_1101_; 
v_entries_1101_ = lean_ctor_get(v_map_1100_, 0);
lean_inc_ref(v_entries_1101_);
return v_entries_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg___boxed(lean_object* v_map_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_Internal_IndexMultiMap_toArray___redArg(v_map_1102_);
lean_dec_ref(v_map_1102_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_map_1108_){
_start:
{
lean_object* v_entries_1109_; 
v_entries_1109_ = lean_ctor_get(v_map_1108_, 0);
lean_inc_ref(v_entries_1109_);
return v_entries_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___boxed(lean_object* v_00_u03b1_1110_, lean_object* v_00_u03b2_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_map_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Std_Internal_IndexMultiMap_toArray(v_00_u03b1_1110_, v_00_u03b2_1111_, v_inst_1112_, v_inst_1113_, v_map_1114_);
lean_dec_ref(v_map_1114_);
lean_dec_ref(v_inst_1113_);
lean_dec_ref(v_inst_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___redArg(lean_object* v_map_1116_){
_start:
{
lean_object* v_entries_1117_; lean_object* v___x_1118_; 
v_entries_1117_ = lean_ctor_get(v_map_1116_, 0);
lean_inc_ref(v_entries_1117_);
lean_dec_ref(v_map_1116_);
v___x_1118_ = lean_array_to_list(v_entries_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList(lean_object* v_00_u03b1_1119_, lean_object* v_00_u03b2_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_map_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Std_Internal_IndexMultiMap_toList___redArg(v_map_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_map_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Std_Internal_IndexMultiMap_toList(v_00_u03b1_1125_, v_00_u03b2_1126_, v_inst_1127_, v_inst_1128_, v_map_1129_);
lean_dec_ref(v_inst_1128_);
lean_dec_ref(v_inst_1127_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg___lam__1(lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_x1_1133_, lean_object* v_x2_1134_){
_start:
{
lean_object* v_fst_1135_; lean_object* v_entries_1136_; lean_object* v_indexes_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1148_; 
v_fst_1135_ = lean_ctor_get(v_x2_1134_, 0);
lean_inc(v_fst_1135_);
v_entries_1136_ = lean_ctor_get(v_x1_1133_, 0);
v_indexes_1137_ = lean_ctor_get(v_x1_1133_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_x1_1133_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1139_ = v_x1_1133_;
v_isShared_1140_ = v_isSharedCheck_1148_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_indexes_1137_);
lean_inc(v_entries_1136_);
lean_dec(v_x1_1133_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1148_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_i_1141_; lean_object* v_f_1142_; lean_object* v_entries_1143_; lean_object* v_indexes_1144_; lean_object* v___x_1146_; 
v_i_1141_ = lean_array_get_size(v_entries_1136_);
v_f_1142_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1142_, 0, v_i_1141_);
v_entries_1143_ = lean_array_push(v_entries_1136_, v_x2_1134_);
v_indexes_1144_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1131_, v_inst_1132_, v_indexes_1137_, v_fst_1135_, v_f_1142_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v_indexes_1144_);
lean_ctor_set(v___x_1139_, 0, v_entries_1143_);
v___x_1146_ = v___x_1139_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_entries_1143_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_indexes_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_m1_1151_, lean_object* v_m2_1152_){
_start:
{
lean_object* v_entries_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_entries_1153_ = lean_ctor_get(v_m2_1152_, 0);
lean_inc_ref(v_entries_1153_);
lean_dec_ref(v_m2_1152_);
v___x_1154_ = lean_unsigned_to_nat(0u);
v___x_1155_ = lean_array_get_size(v_entries_1153_);
v___x_1156_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1157_ = lean_nat_dec_lt(v___x_1154_, v___x_1155_);
if (v___x_1157_ == 0)
{
lean_dec_ref(v_entries_1153_);
lean_dec_ref(v_inst_1150_);
lean_dec_ref(v_inst_1149_);
return v_m1_1151_;
}
else
{
lean_object* v___f_1158_; size_t v___x_1159_; size_t v___x_1160_; lean_object* v___x_1161_; 
v___f_1158_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1158_, 0, v_inst_1149_);
lean_closure_set(v___f_1158_, 1, v_inst_1150_);
v___x_1159_ = ((size_t)0ULL);
v___x_1160_ = lean_usize_of_nat(v___x_1155_);
v___x_1161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1156_, v___f_1158_, v_entries_1153_, v___x_1159_, v___x_1160_, v_m1_1151_);
return v___x_1161_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object* v_00_u03b1_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_m1_1168_, lean_object* v_m2_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Std_Internal_IndexMultiMap_merge___redArg(v_inst_1164_, v_inst_1165_, v_m1_1168_, v_m2_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg();
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection(lean_object* v_00_u03b1_1175_, lean_object* v_00_u03b2_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_1180_, lean_object* v_00_u03b2_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_Internal_IndexMultiMap_instEmptyCollection(v_00_u03b1_1180_, v_00_u03b2_1181_, v_inst_1182_, v_inst_1183_);
lean_dec_ref(v_inst_1183_);
lean_dec_ref(v_inst_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_x_1187_){
_start:
{
lean_object* v_fst_1188_; lean_object* v___x_1189_; lean_object* v_entries_1190_; lean_object* v_indexes_1191_; lean_object* v_i_1192_; lean_object* v_f_1193_; lean_object* v_entries_1194_; lean_object* v_indexes_1195_; lean_object* v___x_1196_; 
v_fst_1188_ = lean_ctor_get(v_x_1187_, 0);
lean_inc(v_fst_1188_);
v___x_1189_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v_entries_1190_ = lean_ctor_get(v___x_1189_, 0);
v_indexes_1191_ = lean_ctor_get(v___x_1189_, 1);
v_i_1192_ = lean_array_get_size(v_entries_1190_);
v_f_1193_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1193_, 0, v_i_1192_);
lean_inc_ref(v_entries_1190_);
v_entries_1194_ = lean_array_push(v_entries_1190_, v_x_1187_);
lean_inc_ref(v_indexes_1191_);
v_indexes_1195_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1185_, v_inst_1186_, v_indexes_1191_, v_fst_1188_, v_f_1193_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_entries_1194_);
lean_ctor_set(v___x_1196_, 1, v_indexes_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1197_, lean_object* v_inst_1198_){
_start:
{
lean_object* v___f_1199_; 
v___f_1199_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1199_, 0, v_inst_1197_);
lean_closure_set(v___f_1199_, 1, v_inst_1198_);
return v___f_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1200_, lean_object* v_00_u03b2_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_){
_start:
{
lean_object* v___f_1206_; 
v___f_1206_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1206_, 0, v_inst_1202_);
lean_closure_set(v___f_1206_, 1, v_inst_1203_);
return v___f_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1207_, lean_object* v_inst_1208_, lean_object* v_x_1209_, lean_object* v_m_1210_){
_start:
{
lean_object* v_fst_1211_; lean_object* v_entries_1212_; lean_object* v_indexes_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1224_; 
v_fst_1211_ = lean_ctor_get(v_x_1209_, 0);
lean_inc(v_fst_1211_);
v_entries_1212_ = lean_ctor_get(v_m_1210_, 0);
v_indexes_1213_ = lean_ctor_get(v_m_1210_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_m_1210_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1215_ = v_m_1210_;
v_isShared_1216_ = v_isSharedCheck_1224_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_indexes_1213_);
lean_inc(v_entries_1212_);
lean_dec(v_m_1210_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1224_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_i_1217_; lean_object* v_f_1218_; lean_object* v_entries_1219_; lean_object* v_indexes_1220_; lean_object* v___x_1222_; 
v_i_1217_ = lean_array_get_size(v_entries_1212_);
v_f_1218_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1218_, 0, v_i_1217_);
v_entries_1219_ = lean_array_push(v_entries_1212_, v_x_1209_);
v_indexes_1220_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1207_, v_inst_1208_, v_indexes_1213_, v_fst_1211_, v_f_1218_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v_indexes_1220_);
lean_ctor_set(v___x_1215_, 0, v_entries_1219_);
v___x_1222_ = v___x_1215_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_entries_1219_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_indexes_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1225_, lean_object* v_inst_1226_){
_start:
{
lean_object* v___f_1227_; 
v___f_1227_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1227_, 0, v_inst_1225_);
lean_closure_set(v___f_1227_, 1, v_inst_1226_);
return v___f_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b2_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_){
_start:
{
lean_object* v___f_1234_; 
v___f_1234_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1234_, 0, v_inst_1230_);
lean_closure_set(v___f_1234_, 1, v_inst_1231_);
return v___f_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1235_, lean_object* v_inst_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1237_, 0, lean_box(0));
lean_closure_set(v___x_1237_, 1, lean_box(0));
lean_closure_set(v___x_1237_, 2, v_inst_1235_);
lean_closure_set(v___x_1237_, 3, v_inst_1236_);
lean_closure_set(v___x_1237_, 4, lean_box(0));
lean_closure_set(v___x_1237_, 5, lean_box(0));
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1238_, lean_object* v_00_u03b2_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1244_, 0, lean_box(0));
lean_closure_set(v___x_1244_, 1, lean_box(0));
lean_closure_set(v___x_1244_, 2, v_inst_1240_);
lean_closure_set(v___x_1244_, 3, v_inst_1241_);
lean_closure_set(v___x_1244_, 4, lean_box(0));
lean_closure_set(v___x_1244_, 5, lean_box(0));
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1245_, lean_object* v_a_1246_, lean_object* v_x_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_apply_2(v_f_1245_, v_a_1246_, v___y_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1250_, lean_object* v_00_u03b2_1251_, lean_object* v_map_1252_, lean_object* v_b_1253_, lean_object* v_f_1254_){
_start:
{
lean_object* v_entries_1255_; lean_object* v___f_1256_; size_t v_sz_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v_entries_1255_ = lean_ctor_get(v_map_1252_, 0);
lean_inc_ref(v_entries_1255_);
lean_dec_ref(v_map_1252_);
v___f_1256_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1256_, 0, v_f_1254_);
v_sz_1257_ = lean_array_size(v_entries_1255_);
v___x_1258_ = ((size_t)0ULL);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1250_, v_entries_1255_, v___f_1256_, v_sz_1257_, v___x_1258_, v_b_1253_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg(lean_object* v_inst_1260_){
_start:
{
lean_object* v___f_1261_; 
v___f_1261_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1261_, 0, v_inst_1260_);
return v___f_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad(lean_object* v_00_u03b1_1262_, lean_object* v_00_u03b2_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_m_1266_, lean_object* v_inst_1267_){
_start:
{
lean_object* v___f_1268_; 
v___f_1268_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1268_, 0, v_inst_1267_);
return v___f_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1269_, lean_object* v_00_u03b2_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_m_1273_, lean_object* v_inst_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Std_Internal_IndexMultiMap_instForInProdOfMonad(v_00_u03b1_1269_, v_00_u03b2_1270_, v_inst_1271_, v_inst_1272_, v_m_1273_, v_inst_1274_);
lean_dec_ref(v_inst_1272_);
lean_dec_ref(v_inst_1271_);
return v_res_1275_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_IndexMultiMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
